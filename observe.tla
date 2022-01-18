------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
(**************************************************************************)
(* This TLA+ Spec verifies the reworked version of observe:              
                                                                       
 ```                                                                   
  for {                                                                 
    guard <- Semaphore[F](maxQueued - 1)
    outChan <- Channel.unbounded[F, Chunk[O]]
  } yield {
 
    val sinkOut: Stream[F, O] = {
      def go(s: Stream[F, Chunk[O]]): Pull[F, O, Unit] =
        s.pull.uncons1.flatMap { // InOutput
          case None => Pull.done
          case Some((ch, rest)) =>
            Pull.output(ch) >>
             Pull.eval(outChan.send(ch) // InSendToChannel
                       >> guard.acquire // InAcquireGuard
                       ) >>
                    go(rest)
        }
 
      go(self.chunks).stream
    }
 
    val runner =
      sinkOut.through(pipe)             // InComplete, ObserverComplete
        ++ Stream.exec(outChan.close.void) // ObserverOnFinalize
 
    def outStream =
      outChan.stream // OutPopFromChannel
        .flatMap { chunk =>
          Stream.chunk(chunk) // OutOutput
            ++ Stream.exec(guard.release) // OutReleaseGuard
        }
 
    val out = outStream.concurrently(runner)  // OutOnFinalize
    out
  }
 ```

 The parameter `maxQueued` is fixed at 1 to test `observe` only, so excludes
 `observeAsync`.
 
 Only finite streams are modelled.
 
 There are three main PlusCal processes:
   - *in* represents the input stream `self.chunks` and `sinkOut`.
   - *observer* represents the observer `onFinalize(outChan.close.void)`.
   - *out* represents the output stream `outStream`, including the logic
     interrupting the observer with `concurrently`.

 There are also processes for non-deterministically interrupting the in
 and out streams, named *in-interrupt* and *out-interrupt* respectively. 
 
 *)

(* Redeclare the symbols from ObserveSpec *)
CONSTANTS Streams, PIn, POut, PObs
CONSTANTS States, SRunning, SErrored, SCancelled, SSucceeded

(* We can configure how a stream terminates - whether it throws an error
   or is interrupted - through the termination state. We provide a range
   such that we run the spec accross a matrix of states *)
CONSTANTS TerminationStates,
          TError, (* An error occurred when evaluating work in the stream *)
	  TCancel, (* The stream was interrupted *)
	  TSuccess (* The stream terminated successfully *)
CONSTANT inTerminationRange, obsTerminationRange, outTerminationRange

(* We can configure how the observer is related to the input stream
   through the observer scope *)
CONSTANTS ObserverScopes,
          OParent, (* The observer is a constant parent, e.g. `in.take(1)` *)
	  OTransient, (* The input is active for part, but not all, of the
	                 observer, e.g. `in ++ other` *)
	  ONone       (* The observer runs the input in an unrelated scope
	                 e.g. `other.concurrently(in)` *)
CONSTANT observerScopeRange

(* We can configure the maximum number of elements to take from each stream *)
CONSTANTS inNTakeRange, (* The maximum number of elements emitted by `in` *)
          outNTakeRange, (* The maximum number of elements requested by `out` *)
	  obsNTakeRange (* The maximum number of elements requested by `observer` *)

(* We can configure whether the observer will handle an error from the input by
   setting a boolean value. *)
CONSTANT observerHandlesErrorRange

(* Validate the parameters set in the model *)
NonEmpty(S) == ~ S = {}
Naturals(S) == S \subseteq Nat
Minimum(S) == CHOOSE x \in S : \A y \in S : x <= y


(* NTakeRanges must be positive integers *)
ASSUME NonEmpty(inNTakeRange)  /\ Naturals(inNTakeRange)
ASSUME NonEmpty(obsNTakeRange) /\ Naturals(obsNTakeRange)
(* At least one element must be requested by `out` *)
ASSUME NonEmpty(outNTakeRange) /\ Naturals(outNTakeRange)  /\ Minimum(outNTakeRange) > 0

(* The input stream can be interrupted by the observer, and can also raise an error *)
ASSUME NonEmpty(inTerminationRange) /\ inTerminationRange \subseteq TerminationStates
(* The observer is run in the background using `concurrently`, so cannot be interrupted
   from outside the system. *)
ASSUME NonEmpty(obsTerminationRange) /\ obsTerminationRange \subseteq {TSuccess, TError}
(* There is no need to model error handling in the output stream *)
ASSUME NonEmpty(outTerminationRange) /\ outTerminationRange \subseteq {TSuccess, TCancel}

ASSUME NonEmpty(observerScopeRange) /\ observerScopeRange \subseteq ObserverScopes

ASSUME NonEmpty(observerHandlesErrorRange) /\ observerHandlesErrorRange \subseteq BOOLEAN

(* --algorithm observe
variable observerScope \in observerScopeRange,
         observerHandlesError \in observerHandlesErrorRange,
         inNTake \in inNTakeRange,
         outNTake \in outNTakeRange,
         obsNTake \in obsNTakeRange,
         inTermination \in inTerminationRange,
         obsTermination \in obsTerminationRange,
         outTermination \in outTerminationRange,
         inInterrupted = FALSE, \* Whether the in stream has been interrupted by the observer
         outInterrupted = FALSE, \* Whether the out stream has been interrupted from downstream
         observerInterrupted = FALSE, \* Whether the observer has been interrupted by `concurrently`
         streams = [
           PIn |-> [
             state |-> SRunning,
             sent |-> <<>>,
             hasFinalized |-> FALSE,      \* Whether the in stream has finished its work
             nTake |-> inNTake,          \* The maximum number of elements to send
             termination |-> inTermination
           ],
           POut |-> [
             state |-> SRunning,
             nRequested |-> 0,
             received |-> <<>>,
             nTake |-> outNTake
           ],
           PObs |-> [
            state |-> SRunning,
            nRequested |-> 0,
            received |-> <<>>,
            nTake |-> obsNTake,           \* The maximum number of elements to request from upstream
            termination |-> obsTermination
           ]
         ],
         guard = 0,
         outChan = [
           closed |-> FALSE,
           contents |-> <<>>
         ];

define
InHasElement == Len(streams.PIn.sent) < streams.PIn.nTake

NextElement == Len(streams.PIn.sent) + 1

Terminated(stream) == ~ stream.state = SRunning

ObsRequiresElement == streams.PObs.nRequested < streams.PObs.nTake
ObsHasReceivedAllElements == streams.PObs.nRequested = Len(streams.PObs.received)

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake

(* Whether the observer has been interrupted and is a parent of the `in` stream *)
ObserverInterrupted ==
  (observerScope = OParent \/ observerScope = OTransient) /\ observerInterrupted

(* Calculate the final state of the `in` stream, should it not have been terminated
   by the observer. *)
InEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ (ObserverInterrupted \/ inInterrupted)
     (* If the stream is running and has not been interrupted *)
  THEN
    (* If the stream should raise an error and the observer has yet to pull on it, raise an error.
       An error can only be raised if the stream has work that it can do. *)
    CASE streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements  -> SErrored
    (* In all other cases, terminate gracefully.
       The termination state of TCancel is handled elsewhere using the inInterrupt flag. *)
      [] OTHER                                                            -> SSucceeded
  ELSE IF /\ ~ Terminated(streams.PIn) /\ (ObserverInterrupted \/ inInterrupted)
    (* If the stream is running and has been interrupted, then cancel it. *)
    THEN SCancelled
  ELSE Assert(~ Terminated(streams.PIn), "Impossible code path: the input stream should be running, but is not.") 

(* Calculate the final state of the `observer` stream, should it be terminated by the `in` stream. *)
InObserverEndState ==
  IF ~ Terminated(streams.PObs)
     (* If the observer has not already terminated *)
  THEN
    IF observerScope = OParent /\ ~ ObserverInterrupted
    (* If the observer is a direct parent and it has not been interrupted *)
    THEN
    (* If the in stream raises an error and the observer does not handle it, the observer should raise the error *)
      CASE streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements /\ ~ observerHandlesError  -> SErrored
        (* If the in stream raises an error and the observer handles it, the observer should swallow the error *)
        [] streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements /\   observerHandlesError  -> SSucceeded
        (* In all other cases, the observer should succeed *)
        [] streams.PIn.termination = TSuccess                                                -> SSucceeded
        [] OTHER                                                                             -> SSucceeded
    ELSE
      IF ObserverInterrupted
      (* If the observer is a parent and it has been interrupted, then it should be cancelled *)
      THEN SCancelled
      (* In all other cases the observer's scope is not a parent. The observer's termination is handled in the
         observer process *)
      ELSE streams.PObs.state
  (* The observer has already terminated. It should remain in its state. *)
  ELSE streams.PObs.state

StateFromTermination(tstate) ==
  CASE tstate = TError   -> SErrored
    [] tstate = TCancel  -> SCancelled
    [] tstate = TSuccess -> SSucceeded

(* Calculate the final state of the `observer` stream, should it be terminated by the `observer` process. *)
ObserverEndState ==
  IF observerScope = OTransient \/ observerScope = ONone
   (* If the observer is a parent of the in stream, but has some work to do once the stream has finished,
      or if it is unrelated. *)
  THEN
      (* If the in stream was interrupted by the observer stream, terminate in the configured state. *)
    CASE streams.PIn.state = SCancelled                         -> StateFromTermination(streams.PObs.termination)
      (* If the in stream succeeded, terminate in the configured state. *)
      [] streams.PIn.state = SSucceeded                         -> StateFromTermination(streams.PObs.termination)
      (* If the in stream raised an error and the observer does not handle it, terminate with an error. *)
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      (* If the in stream raised an error and the observer handles it, swallow the error. *)
      [] streams.PIn.state = SErrored /\   observerHandlesError -> StateFromTermination(streams.PObs.termination)
      [] OTHER                                                  -> Assert(Terminated(streams.PIn.state), "Impossible code path. The input stream should have terminated.")
  ELSE Assert(Terminated(streams.PObs.state), "The observer scope was OParent, but the observer was not terminated by the in process.")


(* Define invariants for sanity checking *)
GuardIsNonNegative == guard >= 0
end define;

macro acquire() begin
  if guard > 0 then
    guard := guard - 1;
  else
    await guard > 0 \/ Terminated(streams.PIn) \/ ObserverInterrupted \/ inInterrupted;
  end if;
end macro;

macro release() begin
  guard := guard + 1;
end macro;

fair process in = "in"
begin
  InOutput:
  while /\ ~ Terminated(streams.PIn)
        /\ ~ ObserverInterrupted
	/\ ~ inInterrupted
        /\ ObsRequiresElement do
    if ~ InHasElement then
      \* The observer has requested an element, but there are none to send.
      streams.PObs.nRequested := streams.PObs.nRequested + 1;
      goto InComplete;
    else
      local_el := NextElement;
      streams.PObs.nRequested := streams.PObs.nRequested + 1 ||
      streams.PObs.received := Append(streams.PObs.received, local_el) ||
      streams.PIn.sent := Append(streams.PIn.sent, local_el);

      InSendToChannel:
        if \/ Terminated(streams.PIn)
	       \/ inInterrupted
           \/ ObserverInterrupted then
          goto InComplete;
        elsif ~ outChan.closed then
          outChan.contents := Append(outChan.contents, local_el);
        else
          \* The output channel is closed. Keep sending elements to the observer,
          \* but don't send them to the channel.
          skip;
        end if;

      InAcquireGuard:
        if /\ ~ Terminated(streams.PIn)
	       /\ ~ inInterrupted
           /\ ~ ObserverInterrupted then
          acquire();
        else
          \* The input has been terminated or interrupted
          skip;
        end if;
      end if;
  end while;

  InComplete:
    if streams.PIn.state = SRunning then
      streams.PIn.state := InEndState || streams.PObs.state := InObserverEndState;
    else
      \* The stream has been terminated by some other process.
      skip;
    end if;

  InOnFinalize:
    streams.PIn.hasFinalized := TRUE;
end process;

(* We run the observer in a separate process in order to represent independent asynchronous termination. *)
fair process observer = "observer"
begin
  ObserverComplete:
  \* If the scope is not a parent, it is transient or unrelated and must be handled here
  if ~ observerScope = OParent then
    await \/ Terminated(streams.PObs)
          \/ Terminated(streams.PIn)
          \/ observerInterrupted;
  \* If the input stream has terminated, we assume that there is still work to be done by the observer
  \* The steps between the input termination and this step represents that work
    if ~ Terminated(streams.PObs) /\ ~ observerInterrupted /\ Terminated(streams.PIn) then
      streams.PObs.state := ObserverEndState;
  \* If the input stream has not terminated, and is running concurrently to the observer, then it must be interrupted.
    elsif /\ observerInterrupted /\ observerScope = ONone then
      if streams.PIn.state = SRunning then
        streams.PIn.state := SCancelled || streams.PObs.state := SCancelled;
      else
        streams.PObs.state := SCancelled;
      end if;
    elsif ~ Terminated(streams.PObs) /\ observerInterrupted /\ Terminated(streams.PIn) /\ observerScope = OTransient then
      streams.PObs.state := SCancelled;
    else
      \* Either:
      \* - The observer has been interrupted and its scope is OParent. The interrupt is handled by the
      \*     "in" process.
      \* - The observer has been interrupted and its scope is OTransient and the "in" process is still running. The
      \*   interrupt is handled by the "in" process.
      \* - The observer has been terminated, but not interrupted, by some other process.
      \* - The "in" stream and the observer have both been terminated, but not interrupted, by some other process.
      skip;
    end if;
  end if;
  ObserverOnFinalize:
    await streams.PIn.hasFinalized; \* Wait for the "in" stream to terminate before closing the channel
    if streams.PObs.state = SSucceeded then 
      outChan.closed := TRUE;
    end if;
end process;

fair process out = "out"
variable local_el = 0, local_running = TRUE;
begin
OutPopFromChannel:
while local_running /\ OutRequiresElement do
    await    outChan.closed
          \/ Len(outChan.contents) > 0
          \/ Terminated(streams.POut)
          \/ streams.PObs.state = SErrored
          \/ outInterrupted;
    if outInterrupted /\ ~ Terminated(streams.POut) then
      streams.POut.nRequested := streams.POut.nRequested + 1 ||
      streams.POut.state := SCancelled;
      local_running := FALSE;
    elsif streams.PObs.state = SErrored /\ ~ Terminated(streams.POut) then
      streams.POut.nRequested := streams.POut.nRequested + 1 ||
      streams.POut.state := SErrored;
      local_running := FALSE;
    elsif Len(outChan.contents) > 0 /\ ~ Terminated(streams.POut) then
      streams.POut.nRequested := streams.POut.nRequested + 1;
      local_el := Head(outChan.contents);
      outChan.contents := Tail(outChan.contents);

      OutOutput:
        if ~ Terminated(streams.POut) /\ ~ streams.PObs.state = SErrored /\ ~ outInterrupted then
          streams.POut.received := Append(streams.POut.received, local_el);

          OutReleaseGuard:
            if ~ Terminated(streams.POut) /\ ~ streams.PObs.state = SErrored /\ ~ outInterrupted then
              release();
	    else
	      local_running := FALSE;
	    end if;
        else
         \* The stream has terminated or been interrupted by an error in the observer
         local_running := FALSE;
        end if;
    elsif ~ Terminated(streams.POut) /\ outChan.closed /\ Len(outChan.contents) = 0 then
        \* The output channel is closed. We must close the downstream output stream
        streams.POut.nRequested := streams.POut.nRequested + 1;
        local_running := FALSE;
    end if;
end while;
observerInterrupted := TRUE;

OutOnFinalize:
  await ~ streams.PObs.state = SRunning;
  if streams.PObs.state = SErrored then
    streams.POut.state := SErrored;
  elsif outInterrupted /\ ~ Terminated(streams.POut) then
    streams.POut.state := SCancelled;
  elsif ~ Terminated(streams.POut) then
      streams.POut.state := SSucceeded;
  end if;
end process;

fair process outInterrupt = "out-interrupt"
begin
OutInterrupt:
await Len(streams.POut.received) > 0 \/ Terminated(streams.POut);
if ~ Terminated(streams.POut) /\ outTermination = TCancel then
  outInterrupted := TRUE;
end if;
end process

fair process inInterrupt = "in-interrupt"
begin
InInterrupt:
if ~ Terminated(streams.PIn) /\ inTermination = TCancel then
  inInterrupted := TRUE;
end if;
end process



end algorithm;

\* Invariants
*)


\* BEGIN TRANSLATION (chksum(pcal) = "1221cc68" /\ chksum(tla) = "95da467f")
VARIABLES observerScope, observerHandlesError, inNTake, outNTake, obsNTake, 
          inTermination, obsTermination, outTermination, inInterrupted, 
          outInterrupted, observerInterrupted, streams, guard, outChan, pc

(* define statement *)
InHasElement == Len(streams.PIn.sent) < streams.PIn.nTake

NextElement == Len(streams.PIn.sent) + 1

Terminated(stream) == ~ stream.state = SRunning

ObsRequiresElement == streams.PObs.nRequested < streams.PObs.nTake
ObsHasReceivedAllElements == streams.PObs.nRequested = Len(streams.PObs.received)

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake


ObserverInterrupted ==
  (observerScope = OParent \/ observerScope = OTransient) /\ observerInterrupted



InEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ (ObserverInterrupted \/ inInterrupted)

  THEN


    CASE streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements  -> SErrored


      [] OTHER                                                            -> SSucceeded
  ELSE IF /\ ~ Terminated(streams.PIn) /\ (ObserverInterrupted \/ inInterrupted)

    THEN SCancelled
  ELSE Assert(~ Terminated(streams.PIn), "Impossible code path: the input stream should be running, but is not.")


InObserverEndState ==
  IF ~ Terminated(streams.PObs)

  THEN
    IF observerScope = OParent /\ ~ ObserverInterrupted

    THEN

      CASE streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements /\ ~ observerHandlesError  -> SErrored

        [] streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements /\   observerHandlesError  -> SSucceeded

        [] streams.PIn.termination = TSuccess                                                -> SSucceeded
        [] OTHER                                                                             -> SSucceeded
    ELSE
      IF ObserverInterrupted

      THEN SCancelled


      ELSE streams.PObs.state

  ELSE streams.PObs.state

StateFromTermination(tstate) ==
  CASE tstate = TError   -> SErrored
    [] tstate = TCancel  -> SCancelled
    [] tstate = TSuccess -> SSucceeded


ObserverEndState ==
  IF observerScope = OTransient \/ observerScope = ONone


  THEN

    CASE streams.PIn.state = SCancelled                         -> StateFromTermination(streams.PObs.termination)

      [] streams.PIn.state = SSucceeded                         -> StateFromTermination(streams.PObs.termination)

      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored

      [] streams.PIn.state = SErrored /\   observerHandlesError -> StateFromTermination(streams.PObs.termination)
      [] OTHER                                                  -> Assert(Terminated(streams.PIn.state), "Impossible code path. The input stream should have terminated.")
  ELSE Assert(Terminated(streams.PObs.state), "The observer scope was OParent, but the observer was not terminated by the in process.")



GuardIsNonNegative == guard >= 0

VARIABLES local_el, local_running

vars == << observerScope, observerHandlesError, inNTake, outNTake, obsNTake, 
           inTermination, obsTermination, outTermination, inInterrupted, 
           outInterrupted, observerInterrupted, streams, guard, outChan, pc, 
           local_el, local_running >>

ProcSet == {"in"} \cup {"observer"} \cup {"out"} \cup {"out-interrupt"} \cup {"in-interrupt"}

Init == (* Global variables *)
        /\ observerScope \in observerScopeRange
        /\ observerHandlesError \in observerHandlesErrorRange
        /\ inNTake \in inNTakeRange
        /\ outNTake \in outNTakeRange
        /\ obsNTake \in obsNTakeRange
        /\ inTermination \in inTerminationRange
        /\ obsTermination \in obsTerminationRange
        /\ outTermination \in outTerminationRange
        /\ inInterrupted = FALSE
        /\ outInterrupted = FALSE
        /\ observerInterrupted = FALSE
        /\ streams =           [
                       PIn |-> [
                         state |-> SRunning,
                         sent |-> <<>>,
                         hasFinalized |-> FALSE,
                         nTake |-> inNTake,
                         termination |-> inTermination
                       ],
                       POut |-> [
                         state |-> SRunning,
                         nRequested |-> 0,
                         received |-> <<>>,
                         nTake |-> outNTake
                       ],
                       PObs |-> [
                        state |-> SRunning,
                        nRequested |-> 0,
                        received |-> <<>>,
                        nTake |-> obsNTake,
                        termination |-> obsTermination
                       ]
                     ]
        /\ guard = 0
        /\ outChan =           [
                       closed |-> FALSE,
                       contents |-> <<>>
                     ]
        (* Process out *)
        /\ local_el = 0
        /\ local_running = TRUE
        /\ pc = [self \in ProcSet |-> CASE self = "in" -> "InOutput"
                                        [] self = "observer" -> "ObserverComplete"
                                        [] self = "out" -> "OutPopFromChannel"
                                        [] self = "out-interrupt" -> "OutInterrupt"
                                        [] self = "in-interrupt" -> "InInterrupt"]

InOutput == /\ pc["in"] = "InOutput"
            /\ IF /\ ~ Terminated(streams.PIn)
                  /\ ~ ObserverInterrupted
                  /\ ~ inInterrupted
                  /\ ObsRequiresElement
                  THEN /\ IF ~ InHasElement
                             THEN /\ streams' = [streams EXCEPT !.PObs.nRequested = streams.PObs.nRequested + 1]
                                  /\ pc' = [pc EXCEPT !["in"] = "InComplete"]
                                  /\ UNCHANGED local_el
                             ELSE /\ local_el' = NextElement
                                  /\ streams' = [streams EXCEPT !.PObs.nRequested = streams.PObs.nRequested + 1,
                                                                !.PObs.received = Append(streams.PObs.received, local_el'),
                                                                !.PIn.sent = Append(streams.PIn.sent, local_el')]
                                  /\ pc' = [pc EXCEPT !["in"] = "InSendToChannel"]
                  ELSE /\ pc' = [pc EXCEPT !["in"] = "InComplete"]
                       /\ UNCHANGED << streams, local_el >>
            /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                            outNTake, obsNTake, inTermination, obsTermination, 
                            outTermination, inInterrupted, outInterrupted, 
                            observerInterrupted, guard, outChan, local_running >>

InSendToChannel == /\ pc["in"] = "InSendToChannel"
                   /\ IF \/ Terminated(streams.PIn)
                             \/ inInterrupted
                         \/ ObserverInterrupted
                         THEN /\ pc' = [pc EXCEPT !["in"] = "InComplete"]
                              /\ UNCHANGED outChan
                         ELSE /\ IF ~ outChan.closed
                                    THEN /\ outChan' = [outChan EXCEPT !.contents = Append(outChan.contents, local_el)]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED outChan
                              /\ pc' = [pc EXCEPT !["in"] = "InAcquireGuard"]
                   /\ UNCHANGED << observerScope, observerHandlesError, 
                                   inNTake, outNTake, obsNTake, inTermination, 
                                   obsTermination, outTermination, 
                                   inInterrupted, outInterrupted, 
                                   observerInterrupted, streams, guard, 
                                   local_el, local_running >>

InAcquireGuard == /\ pc["in"] = "InAcquireGuard"
                  /\ IF /\ ~ Terminated(streams.PIn)
                            /\ ~ inInterrupted
                        /\ ~ ObserverInterrupted
                        THEN /\ IF guard > 0
                                   THEN /\ guard' = guard - 1
                                   ELSE /\ guard > 0 \/ Terminated(streams.PIn) \/ ObserverInterrupted \/ inInterrupted
                                        /\ guard' = guard
                        ELSE /\ TRUE
                             /\ guard' = guard
                  /\ pc' = [pc EXCEPT !["in"] = "InOutput"]
                  /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                                  outNTake, obsNTake, inTermination, 
                                  obsTermination, outTermination, 
                                  inInterrupted, outInterrupted, 
                                  observerInterrupted, streams, outChan, 
                                  local_el, local_running >>

InComplete == /\ pc["in"] = "InComplete"
              /\ IF streams.PIn.state = SRunning
                    THEN /\ streams' = [streams EXCEPT !.PIn.state = InEndState,
                                                       !.PObs.state = InObserverEndState]
                    ELSE /\ TRUE
                         /\ UNCHANGED streams
              /\ pc' = [pc EXCEPT !["in"] = "InOnFinalize"]
              /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                              outNTake, obsNTake, inTermination, 
                              obsTermination, outTermination, inInterrupted, 
                              outInterrupted, observerInterrupted, guard, 
                              outChan, local_el, local_running >>

InOnFinalize == /\ pc["in"] = "InOnFinalize"
                /\ streams' = [streams EXCEPT !.PIn.hasFinalized = TRUE]
                /\ pc' = [pc EXCEPT !["in"] = "Done"]
                /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                                outNTake, obsNTake, inTermination, 
                                obsTermination, outTermination, inInterrupted, 
                                outInterrupted, observerInterrupted, guard, 
                                outChan, local_el, local_running >>

in == InOutput \/ InSendToChannel \/ InAcquireGuard \/ InComplete
         \/ InOnFinalize

ObserverComplete == /\ pc["observer"] = "ObserverComplete"
                    /\ IF ~ observerScope = OParent
                          THEN /\ \/ Terminated(streams.PObs)
                                  \/ Terminated(streams.PIn)
                                  \/ observerInterrupted
                               /\ IF ~ Terminated(streams.PObs) /\ ~ observerInterrupted /\ Terminated(streams.PIn)
                                     THEN /\ streams' = [streams EXCEPT !.PObs.state = ObserverEndState]
                                     ELSE /\ IF /\ observerInterrupted /\ observerScope = ONone
                                                THEN /\ IF streams.PIn.state = SRunning
                                                           THEN /\ streams' = [streams EXCEPT !.PIn.state = SCancelled,
                                                                                              !.PObs.state = SCancelled]
                                                           ELSE /\ streams' = [streams EXCEPT !.PObs.state = SCancelled]
                                                ELSE /\ IF ~ Terminated(streams.PObs) /\ observerInterrupted /\ Terminated(streams.PIn) /\ observerScope = OTransient
                                                           THEN /\ streams' = [streams EXCEPT !.PObs.state = SCancelled]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED streams
                          ELSE /\ TRUE
                               /\ UNCHANGED streams
                    /\ pc' = [pc EXCEPT !["observer"] = "ObserverOnFinalize"]
                    /\ UNCHANGED << observerScope, observerHandlesError, 
                                    inNTake, outNTake, obsNTake, inTermination, 
                                    obsTermination, outTermination, 
                                    inInterrupted, outInterrupted, 
                                    observerInterrupted, guard, outChan, 
                                    local_el, local_running >>

ObserverOnFinalize == /\ pc["observer"] = "ObserverOnFinalize"
                      /\ streams.PIn.hasFinalized
                      /\ IF streams.PObs.state = SSucceeded
                            THEN /\ outChan' = [outChan EXCEPT !.closed = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED outChan
                      /\ pc' = [pc EXCEPT !["observer"] = "Done"]
                      /\ UNCHANGED << observerScope, observerHandlesError, 
                                      inNTake, outNTake, obsNTake, 
                                      inTermination, obsTermination, 
                                      outTermination, inInterrupted, 
                                      outInterrupted, observerInterrupted, 
                                      streams, guard, local_el, local_running >>

observer == ObserverComplete \/ ObserverOnFinalize

OutPopFromChannel == /\ pc["out"] = "OutPopFromChannel"
                     /\ IF local_running /\ OutRequiresElement
                           THEN /\    outChan.closed
                                   \/ Len(outChan.contents) > 0
                                   \/ Terminated(streams.POut)
                                   \/ streams.PObs.state = SErrored
                                   \/ outInterrupted
                                /\ IF outInterrupted /\ ~ Terminated(streams.POut)
                                      THEN /\ streams' = [streams EXCEPT !.POut.nRequested = streams.POut.nRequested + 1,
                                                                         !.POut.state = SCancelled]
                                           /\ local_running' = FALSE
                                           /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
                                           /\ UNCHANGED << outChan, local_el >>
                                      ELSE /\ IF streams.PObs.state = SErrored /\ ~ Terminated(streams.POut)
                                                 THEN /\ streams' = [streams EXCEPT !.POut.nRequested = streams.POut.nRequested + 1,
                                                                                    !.POut.state = SErrored]
                                                      /\ local_running' = FALSE
                                                      /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
                                                      /\ UNCHANGED << outChan, 
                                                                      local_el >>
                                                 ELSE /\ IF Len(outChan.contents) > 0 /\ ~ Terminated(streams.POut)
                                                            THEN /\ streams' = [streams EXCEPT !.POut.nRequested = streams.POut.nRequested + 1]
                                                                 /\ local_el' = Head(outChan.contents)
                                                                 /\ outChan' = [outChan EXCEPT !.contents = Tail(outChan.contents)]
                                                                 /\ pc' = [pc EXCEPT !["out"] = "OutOutput"]
                                                                 /\ UNCHANGED local_running
                                                            ELSE /\ IF ~ Terminated(streams.POut) /\ outChan.closed /\ Len(outChan.contents) = 0
                                                                       THEN /\ streams' = [streams EXCEPT !.POut.nRequested = streams.POut.nRequested + 1]
                                                                            /\ local_running' = FALSE
                                                                       ELSE /\ TRUE
                                                                            /\ UNCHANGED << streams, 
                                                                                            local_running >>
                                                                 /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
                                                                 /\ UNCHANGED << outChan, 
                                                                                 local_el >>
                                /\ UNCHANGED observerInterrupted
                           ELSE /\ observerInterrupted' = TRUE
                                /\ pc' = [pc EXCEPT !["out"] = "OutOnFinalize"]
                                /\ UNCHANGED << streams, outChan, local_el, 
                                                local_running >>
                     /\ UNCHANGED << observerScope, observerHandlesError, 
                                     inNTake, outNTake, obsNTake, 
                                     inTermination, obsTermination, 
                                     outTermination, inInterrupted, 
                                     outInterrupted, guard >>

OutOutput == /\ pc["out"] = "OutOutput"
             /\ IF ~ Terminated(streams.POut) /\ ~ streams.PObs.state = SErrored /\ ~ outInterrupted
                   THEN /\ streams' = [streams EXCEPT !.POut.received = Append(streams.POut.received, local_el)]
                        /\ pc' = [pc EXCEPT !["out"] = "OutReleaseGuard"]
                        /\ UNCHANGED local_running
                   ELSE /\ local_running' = FALSE
                        /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
                        /\ UNCHANGED streams
             /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                             outNTake, obsNTake, inTermination, obsTermination, 
                             outTermination, inInterrupted, outInterrupted, 
                             observerInterrupted, guard, outChan, local_el >>

OutReleaseGuard == /\ pc["out"] = "OutReleaseGuard"
                   /\ IF ~ Terminated(streams.POut) /\ ~ streams.PObs.state = SErrored /\ ~ outInterrupted
                         THEN /\ guard' = guard + 1
                              /\ UNCHANGED local_running
                         ELSE /\ local_running' = FALSE
                              /\ guard' = guard
                   /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
                   /\ UNCHANGED << observerScope, observerHandlesError, 
                                   inNTake, outNTake, obsNTake, inTermination, 
                                   obsTermination, outTermination, 
                                   inInterrupted, outInterrupted, 
                                   observerInterrupted, streams, outChan, 
                                   local_el >>

OutOnFinalize == /\ pc["out"] = "OutOnFinalize"
                 /\ ~ streams.PObs.state = SRunning
                 /\ IF streams.PObs.state = SErrored
                       THEN /\ streams' = [streams EXCEPT !.POut.state = SErrored]
                       ELSE /\ IF outInterrupted /\ ~ Terminated(streams.POut)
                                  THEN /\ streams' = [streams EXCEPT !.POut.state = SCancelled]
                                  ELSE /\ IF ~ Terminated(streams.POut)
                                             THEN /\ streams' = [streams EXCEPT !.POut.state = SSucceeded]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED streams
                 /\ pc' = [pc EXCEPT !["out"] = "Done"]
                 /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                                 outNTake, obsNTake, inTermination, 
                                 obsTermination, outTermination, inInterrupted, 
                                 outInterrupted, observerInterrupted, guard, 
                                 outChan, local_el, local_running >>

out == OutPopFromChannel \/ OutOutput \/ OutReleaseGuard \/ OutOnFinalize

OutInterrupt == /\ pc["out-interrupt"] = "OutInterrupt"
                /\ Len(streams.POut.received) > 0 \/ Terminated(streams.POut)
                /\ IF ~ Terminated(streams.POut) /\ outTermination = TCancel
                      THEN /\ outInterrupted' = TRUE
                      ELSE /\ TRUE
                           /\ UNCHANGED outInterrupted
                /\ pc' = [pc EXCEPT !["out-interrupt"] = "Done"]
                /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                                outNTake, obsNTake, inTermination, 
                                obsTermination, outTermination, inInterrupted, 
                                observerInterrupted, streams, guard, outChan, 
                                local_el, local_running >>

outInterrupt == OutInterrupt

InInterrupt == /\ pc["in-interrupt"] = "InInterrupt"
               /\ IF ~ Terminated(streams.PIn) /\ inTermination = TCancel
                     THEN /\ inInterrupted' = TRUE
                     ELSE /\ TRUE
                          /\ UNCHANGED inInterrupted
               /\ pc' = [pc EXCEPT !["in-interrupt"] = "Done"]
               /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                               outNTake, obsNTake, inTermination, 
                               obsTermination, outTermination, outInterrupted, 
                               observerInterrupted, streams, guard, outChan, 
                               local_el, local_running >>

inInterrupt == InInterrupt

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == in \/ observer \/ out \/ outInterrupt \/ inInterrupt
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(in)
        /\ WF_vars(observer)
        /\ WF_vars(out)
        /\ WF_vars(outInterrupt)
        /\ WF_vars(inInterrupt)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

INSTANCE ObserveSpec

=============================================================================
\* Modification History
\* Last modified Tue Jan 18 14:03:19 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
