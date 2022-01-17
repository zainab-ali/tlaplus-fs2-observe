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
        s.pull.uncons1.flatMap { \\ InOutput
          case None => Pull.done
          case Some((ch, rest)) =>
            Pull.output(ch) >>
             Pull.eval(outChan.send(ch) \\ InSendToChannel
                       >> guard.acquire \\ InAcquireGuard
                       ) >>
                    go(rest)
        }
 
      go(self.chunks).stream
    }
 
    val runner =
      sinkOut.through(pipe)             \\ InComplete, ObserverComplete
        .onFinalize(outChan.close.void) \\ ObserverOnFinalize
 
    def outStream =
      outChan.stream \\ OutPopFromChannel
        .flatMap { chunk =>
          Stream.chunk(chunk) \\ OutOutput
            .onFinalize(guard.release) \\ OutReleaseGuard
        }
 
    val out = outStream.concurrently(runner)  \\ OutOnFinalize
    out
  }
 ```
 
 There are three processes:
   - PIn represents the input stream `self.chunks` and `sinkOut`.
   - PObs represents the observer `onFinalize(outChan.close.void)`.
   - POut represents the output stream `outStream`, including the logic
     interrupting the observer with `concurrently`.
 
 The parameter `maxQueued` is fixed at 1 to test `observe` only, so excludes
 `observeAsync`.
 
 The input stream `self` is finite, capped at nTake.
 *)

(* Redeclare the symbols from ObserveSpec *)
CONSTANTS Streams, PIn, POut, PObs
CONSTANTS States, SRunning, SErrored, SCancelled, SSucceeded
CONSTANTS TerminationStates, TError, TCancel, TSuccess
CONSTANTS ObserverScopes, OParent, OTransient, ONone
CONSTANTS inNTakeRange, outNTakeRange, obsNTakeRange

CONSTANT observerScopeRange
CONSTANT observerHandlesErrorRange
CONSTANT inTerminationRange, obsTerminationRange, outTerminationRange

(* Validate the parameters set in the model *)
NonEmpty(S) == ~ S = {}
Minimum(S) == CHOOSE x \in S : \A y \in S : x <= y

Naturals(S) == S \subseteq Nat

ASSUME NonEmpty(inNTakeRange)  /\ Naturals(inNTakeRange)
ASSUME NonEmpty(obsNTakeRange) /\ Naturals(obsNTakeRange)
ASSUME NonEmpty(outNTakeRange) /\ Naturals(outNTakeRange)  /\ Minimum(outNTakeRange) > 0

ASSUME NonEmpty(observerScopeRange) /\ observerScopeRange \subseteq ObserverScopes
ASSUME NonEmpty(observerHandlesErrorRange) /\ observerHandlesErrorRange \subseteq BOOLEAN
ASSUME NonEmpty(inTerminationRange) /\ inTerminationRange \subseteq TerminationStates
ASSUME NonEmpty(obsTerminationRange) /\ obsTerminationRange \subseteq {TSuccess, TError}
ASSUME NonEmpty(outTerminationRange) /\ outTerminationRange \subseteq {TSuccess, TCancel}

(* --algorithm observe
variable observerScope \in observerScopeRange,
         observerHandlesError \in observerHandlesErrorRange,
         inNTake \in inNTakeRange,
         outNTake \in outNTakeRange,
         obsNTake \in obsNTakeRange,
         inTermination \in inTerminationRange,
         obsTermination \in obsTerminationRange,
         outTermination \in outTerminationRange,
         inInterrupted = FALSE,
         outInterrupted = FALSE,
         streams = [
           PIn |-> [
             state |-> SRunning,
             sent |-> <<>>,
             hasFinalized |-> FALSE,      \* Whether the in stream has work to do before the observer stream can finalize
             nTake |-> inNTake,          \* The maximum number of elements to send
             termination |-> inTermination    \* The state we intend the stream to terminate in, should all its elements be requested.
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
            termination |-> obsTermination \* The state we intend the stream to terminate in, should all its elements be requested.
           ]
         ],
         guard = 0,
         outChan = [
           closed |-> FALSE,
           contents |-> <<>>
         ],
         observerInterrupt = FALSE;

define
PInDownstream == streams.PObs

InHasElement == Len(streams.PIn.sent) < streams.PIn.nTake
InHasSentAllElements == ~ InHasElement

NextElement == Len(streams.PIn.sent) + 1

Terminated(stream) == ~ stream.state = SRunning

ObserverRequiresElement ==
  /\   streams.PObs.state = SRunning
  /\   streams.PObs.nRequested < streams.PObs.nTake
ObsRequiresElement == streams.PObs.nRequested < streams.PObs.nTake
ObsHasRequestedAllElements == ~ ObsRequiresElement
ObsHasReceivedAllElements == streams.PObs.nRequested = Len(streams.PObs.received)

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake

ObserverInterrupted ==
  (observerScope = OParent \/ observerScope = OTransient) /\ observerInterrupt

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
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ Terminated(streams.PObs)
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
  IF observerScope = OTransient
  THEN
    CASE streams.PIn.state = SCancelled                         -> StateFromTermination(streams.PObs.termination)
      [] streams.PIn.state = SSucceeded                         -> StateFromTermination(streams.PObs.termination)
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      [] streams.PIn.state = SErrored /\   observerHandlesError -> StateFromTermination(streams.PObs.termination)
      [] OTHER                                                  -> SSucceeded
  ELSE IF observerScope = ONone THEN
    CASE streams.PIn.state = SCancelled                         -> StateFromTermination(streams.PObs.termination)
      [] streams.PIn.state = SSucceeded                         -> StateFromTermination(streams.PObs.termination)
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      [] streams.PIn.state = SErrored /\   observerHandlesError -> StateFromTermination(streams.PObs.termination)
      [] OTHER                                                  -> SSucceeded
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

(* This represents `sinkOut` in

        val sinkOut: Stream[F, O] = {
          def go(s: Stream[F, Chunk[O]]): Pull[F, O, Unit] =
            s.pull.uncons1.flatMap {
              case None => Pull.done
              case Some((ch, rest)) =>
                Pull.output(ch) >> Pull.eval(outChan.send(ch) >> guard.acquire) >> go(rest)
            }

          go(self.chunks).stream
        }
*)
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

(* This represents runner in
        val runner =
          sinkOut.through(pipe).onFinalize(outChan.close.void)
      ...
        .concurrently(runner)

The pipe may do anything with the sinkOut stream.

We model the observer as synchronous, meaning it terminates when the sinkOut stream terminates,
or as asynchronous, meaning it could terminate at some point after the sinkOut stream.

We assume that the observer will be well-behaved in that it won't leak
resources - it won't start the input stream in a separate fiber and forget
about it.

We run the observer in a separate process in order to represent independent asynchronous termination.
*)
fair process observer = "observer"
begin
  ObserverComplete:
  \* If the scope is not a parent, it is transient or unrelated and must be handled here
  if ~ observerScope = OParent then
    await \/ Terminated(streams.PObs)
          \/ Terminated(streams.PIn)
          \/ observerInterrupt;
  \* If the input stream has terminated, we assume that there is still work to be done by the observer
  \* The steps between the input termination and this step represents that work
    if ~ Terminated(streams.PObs) /\ ~ observerInterrupt /\ Terminated(streams.PIn) then
      streams.PObs.state := ObserverEndState;
  \* If the input stream has not terminated, and is running concurrently to the observer, then it must be interrupted.
    elsif /\ observerInterrupt /\ observerScope = ONone then
      if streams.PIn.state = SRunning then
        streams.PIn.state := SCancelled || streams.PObs.state := SCancelled;
      else
        streams.PObs.state := SCancelled;
      end if;
    elsif ~ Terminated(streams.PObs) /\ observerInterrupt /\ Terminated(streams.PIn) /\ observerScope = OTransient then
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

(* Ths represents
        def outStream =
          outChan.stream
            .flatMap { chunk =>
              Stream.chunk(chunk).onFinalize(guard.release)
            }

    val out = outStream.concurrently(runner)

It is pulled on by a downstream component.
*)
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
            release();
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
observerInterrupt := TRUE;

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

(* This represents:
        val out = outStream.concurrently(runner)
*)

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


\* BEGIN TRANSLATION (chksum(pcal) = "559af23e" /\ chksum(tla) = "8e57cbf0")
VARIABLES observerScope, observerHandlesError, inNTake, outNTake, obsNTake,
	  inTermination, obsTermination, outTermination, outInterrupted,
	  streams, guard, outChan, observerInterrupt, pc

(* define statement *)
PInDownstream == streams.PObs

InHasElement == Len(streams.PIn.sent) < streams.PIn.nTake
NextElement == Len(streams.PIn.sent) + 1

ObserverRequiresElement ==
  /\   streams.PObs.state = SRunning
  /\   streams.PObs.nRequested < streams.PObs.nTake

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake

InInterrupted ==
  (observerScope = OParent \/ observerScope = OTransient) /\ observerInterrupt

ObsRequiresElement == streams.PObs.nRequested < streams.PObs.nTake

InHasSentAllElements == ~ InHasElement
ObsHasRequestedAllElements == ~ ObsRequiresElement
ObsHasReceivedAllElements == streams.PObs.nRequested = Len(streams.PObs.received)

InEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ InHasSentAllElements
       \/ ObsHasRequestedAllElements
  THEN
    CASE streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements  -> SErrored
      [] streams.PIn.termination = TCancel /\ ~ ObsHasReceivedAllElements -> SCancelled
      [] OTHER                                                   -> SSucceeded
  ELSE IF /\ ~ Terminated(streams.PIn) /\ InInterrupted
  THEN SCancelled
  ELSE SSucceeded

InObserverEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ Terminated(streams.PObs)
  THEN
    IF /\ observerScope = OParent
       /\ InHasSentAllElements
	 \/ ObsHasRequestedAllElements
    THEN
      CASE streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements /\ ~ observerHandlesError  -> SErrored
	[] streams.PIn.termination = TError /\ ~ ObsHasReceivedAllElements /\   observerHandlesError  -> SSucceeded
	[] streams.PIn.termination = TCancel /\ ~ ObsHasReceivedAllElements                           -> SCancelled
	[] streams.PIn.termination = TSuccess                                                -> SSucceeded
	[] OTHER                                                                             -> SSucceeded
    ELSE
      IF InInterrupted
      THEN SCancelled
      ELSE streams.PObs.state
  ELSE streams.PObs.state

StateFromTermination(tstate) ==
  CASE tstate = TError   -> SErrored
    [] tstate = TCancel  -> SCancelled
    [] tstate = TSuccess -> SSucceeded

ObserverEndState ==
  IF observerScope = OTransient
  THEN
    CASE streams.PIn.state = SCancelled                         -> SCancelled
      [] streams.PIn.state = SSucceeded                         -> StateFromTermination(streams.PObs.termination)
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      [] streams.PIn.state = SErrored /\   observerHandlesError -> StateFromTermination(streams.PObs.termination)
      [] OTHER                                                  -> SSucceeded
  ELSE IF observerScope = ONone THEN
    CASE streams.PIn.state = SCancelled                         -> StateFromTermination(streams.PObs.termination)
      [] streams.PIn.state = SSucceeded                         -> StateFromTermination(streams.PObs.termination)
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      [] streams.PIn.state = SErrored /\   observerHandlesError -> StateFromTermination(streams.PObs.termination)
      [] OTHER                                                  -> SSucceeded

  ELSE streams.PObs.state


GuardIsNonNegative == guard >= 0

VARIABLES local_el, local_running

vars == << observerScope, observerHandlesError, inNTake, outNTake, obsNTake,
	   inTermination, obsTermination, outTermination, outInterrupted,
	   streams, guard, outChan, observerInterrupt, pc, local_el,
	   local_running >>

ProcSet == {"in"} \cup {"observer"} \cup {"out"} \cup {"out-interrupt"}

Init == (* Global variables *)
	/\ observerScope \in observerScopeRange
	/\ observerHandlesError \in observerHandlesErrorRange
	/\ inNTake \in inNTakeRange
	/\ outNTake \in outNTakeRange
	/\ obsNTake \in obsNTakeRange
	/\ inTermination \in inTerminationRange
	/\ obsTermination \in obsTerminationRange
	/\ outTermination \in outTerminationRange
	/\ outInterrupted = FALSE
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
	/\ observerInterrupt = FALSE
	(* Process out *)
	/\ local_el = 0
	/\ local_running = TRUE
	/\ pc = [self \in ProcSet |-> CASE self = "in" -> "InOutput"
					[] self = "observer" -> "ObserverComplete"
					[] self = "out" -> "OutPopFromChannel"
					[] self = "out-interrupt" -> "OutInterrupt"]

InOutput == /\ pc["in"] = "InOutput"
	    /\ IF /\ ~ Terminated(streams.PIn)
		  /\ ~ InInterrupted
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
			    outTermination, outInterrupted, guard, outChan,
			    observerInterrupt, local_running >>

InSendToChannel == /\ pc["in"] = "InSendToChannel"
		   /\ IF \/ Terminated(streams.PIn)
			 \/ InInterrupted
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
				   outInterrupted, streams, guard,
				   observerInterrupt, local_el, local_running >>

InAcquireGuard == /\ pc["in"] = "InAcquireGuard"
		  /\ IF /\ ~ Terminated(streams.PIn)
			/\ ~ InInterrupted
			THEN /\ IF guard > 0
				   THEN /\ guard' = guard - 1
				   ELSE /\ guard > 0 \/ Terminated(streams.PIn) \/ InInterrupted
					/\ guard' = guard
			ELSE /\ TRUE
			     /\ guard' = guard
		  /\ pc' = [pc EXCEPT !["in"] = "InOutput"]
		  /\ UNCHANGED << observerScope, observerHandlesError, inNTake,
				  outNTake, obsNTake, inTermination,
				  obsTermination, outTermination,
				  outInterrupted, streams, outChan,
				  observerInterrupt, local_el, local_running >>

InComplete == /\ pc["in"] = "InComplete"
	      /\ IF streams.PIn.state = SRunning
		    THEN /\ streams' = [streams EXCEPT !.PIn.state = InEndState,
						       !.PObs.state = InObserverEndState]
		    ELSE /\ TRUE
			 /\ UNCHANGED streams
	      /\ pc' = [pc EXCEPT !["in"] = "InOnFinalize"]
	      /\ UNCHANGED << observerScope, observerHandlesError, inNTake,
			      outNTake, obsNTake, inTermination,
			      obsTermination, outTermination, outInterrupted,
			      guard, outChan, observerInterrupt, local_el,
			      local_running >>

InOnFinalize == /\ pc["in"] = "InOnFinalize"
		/\ streams' = [streams EXCEPT !.PIn.hasFinalized = TRUE]
		/\ pc' = [pc EXCEPT !["in"] = "Done"]
		/\ UNCHANGED << observerScope, observerHandlesError, inNTake,
				outNTake, obsNTake, inTermination,
				obsTermination, outTermination, outInterrupted,
				guard, outChan, observerInterrupt, local_el,
				local_running >>

in == InOutput \/ InSendToChannel \/ InAcquireGuard \/ InComplete
	 \/ InOnFinalize

ObserverComplete == /\ pc["observer"] = "ObserverComplete"
		    /\ IF ~ observerScope = OParent
			  THEN /\ \/ Terminated(streams.PObs)
				  \/ Terminated(streams.PIn)
				  \/ observerInterrupt
			       /\ IF ~ Terminated(streams.PObs) /\ ~ observerInterrupt /\ Terminated(streams.PIn)
				     THEN /\ streams' = [streams EXCEPT !.PObs.state = ObserverEndState]
				     ELSE /\ IF /\ observerInterrupt /\ (observerScope = ONone \/ observerScope = OTransient)
						THEN /\ IF streams.PIn.state = SRunning
							   THEN /\ streams' = [streams EXCEPT !.PIn.state = SCancelled,
											      !.PObs.state = SCancelled]
							   ELSE /\ streams' = [streams EXCEPT !.PObs.state = SCancelled]
						ELSE /\ TRUE
						     /\ UNCHANGED streams
			  ELSE /\ TRUE
			       /\ UNCHANGED streams
		    /\ pc' = [pc EXCEPT !["observer"] = "ObserverOnFinalize"]
		    /\ UNCHANGED << observerScope, observerHandlesError,
				    inNTake, outNTake, obsNTake, inTermination,
				    obsTermination, outTermination,
				    outInterrupted, guard, outChan,
				    observerInterrupt, local_el, local_running >>

ObserverOnFinalize == /\ pc["observer"] = "ObserverOnFinalize"
		      /\ streams.PIn.hasFinalized
		      /\ outChan' = [outChan EXCEPT !.closed = TRUE]
		      /\ pc' = [pc EXCEPT !["observer"] = "Done"]
		      /\ UNCHANGED << observerScope, observerHandlesError,
				      inNTake, outNTake, obsNTake,
				      inTermination, obsTermination,
				      outTermination, outInterrupted, streams,
				      guard, observerInterrupt, local_el,
				      local_running >>

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
				/\ UNCHANGED observerInterrupt
			   ELSE /\ observerInterrupt' = TRUE
				/\ pc' = [pc EXCEPT !["out"] = "OutOnFinalize"]
				/\ UNCHANGED << streams, outChan, local_el,
						local_running >>
		     /\ UNCHANGED << observerScope, observerHandlesError,
				     inNTake, outNTake, obsNTake,
				     inTermination, obsTermination,
				     outTermination, outInterrupted, guard >>

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
			     outTermination, outInterrupted, guard, outChan,
			     observerInterrupt, local_el >>

OutReleaseGuard == /\ pc["out"] = "OutReleaseGuard"
		   /\ guard' = guard + 1
		   /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
		   /\ UNCHANGED << observerScope, observerHandlesError,
				   inNTake, outNTake, obsNTake, inTermination,
				   obsTermination, outTermination,
				   outInterrupted, streams, outChan,
				   observerInterrupt, local_el, local_running >>

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
				 obsTermination, outTermination,
				 outInterrupted, guard, outChan,
				 observerInterrupt, local_el, local_running >>

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
				obsTermination, outTermination, streams, guard,
				outChan, observerInterrupt, local_el,
				local_running >>

outInterrupt == OutInterrupt

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
	       /\ UNCHANGED vars

Next == in \/ observer \/ out \/ outInterrupt
	   \/ Terminating

Spec == /\ Init /\ [][Next]_vars
	/\ WF_vars(in)
	/\ WF_vars(observer)
	/\ WF_vars(out)
	/\ WF_vars(outInterrupt)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

INSTANCE ObserveSpec

=============================================================================
\* Modification History
\* Last modified Sat Jan 15 23:42:31 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
