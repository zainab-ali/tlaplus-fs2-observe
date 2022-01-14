------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences
(* This TLA+ Spec verifies the reworked version of observe:

```
      for {
	guard <- Semaphore[F](maxQueued - 1)
	outChan <- Channel.unbounded[F, Chunk[O]]
      } yield {

	val sinkOut: Stream[F, O] = {
	  def go(s: Stream[F, Chunk[O]]): Pull[F, O, Unit] =
	    s.pull.uncons1.flatMap {
	      case None => Pull.done
	      case Some((ch, rest)) =>
		Pull.output(ch) >> Pull.eval(outChan.send(ch) >> guard.acquire) >> go(rest)
	    }

	  go(self.chunks).stream
	}

	val runner =
	  sinkOut.through(pipe).onFinalize(outChan.close.void)

	def outStream =
	  outChan.stream
	    .flatMap { chunk =>
	      Stream.chunk(chunk).onFinalize(guard.release)
	    }

	val out = outStream.concurrently(runner)
	out
      }
```

Where:
 - PIn corresponds to self.chunks
 - POut corresponds to out
 - PObs corresponds to the result of sinkOut.through(pipe)

The parameter `maxQueued` is fixed at 1 to test `observe` only, so excludes
`observeAsync`.

The input stream `self` is finite, capped at nTake.
*)

\* Redeclare the symbols from ObserveSpec
CONSTANTS Streams, PIn, POut, PObs
CONSTANTS States, SRunning, SErrored, SCancelled, SSucceeded
CONSTANTS TerminationStates, TError, TCancel, TSuccess
CONSTANTS ObserverScopes, OParent, OTransient, ONone
CONSTANTS inNTakeRange, outNTakeRange, obsNTakeRange

CONSTANT observerScopeRange
CONSTANT observerHandlesErrorRange

AppendHead(seq, els) == Append(seq, Head(els))

Terminated(stream) == ~ stream.state = SRunning

(* --algorithm observe
variable observerScope \in observerScopeRange,
	 observerHandlesError \in observerHandlesErrorRange,
	 inNTake \in inNTakeRange,
	 outNTake \in outNTakeRange,
	 obsNTake \in obsNTakeRange,
streams = [
 PIn |-> [
   state |-> SRunning,
   sent |-> <<>>,
   uncons |-> FALSE,           \* Whether the downstream system has requested an element
   pendingWork |-> FALSE,      \* Whether the in stream has work to do before the observer stream can finalize
   nTake |-> inNTake,          \* The maximum number of elements to send
   termination |-> TSuccess    \* The state we intend the stream to terminate in, should all its elements be requested.
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
   nTake |-> obsNTake           \* The maximum number of elements to request from upstream
   \* termination |-> TSucceed \* The state we intend the stream to terminate in, should all its elements be requested.
 ]
],
guard = 0,
outChan = [
  closed |-> FALSE,
  contents |-> <<>>
];

define
PInDownstream == streams.PObs

SinkOutHasElement == Len(streams.PIn.sent) < streams.PIn.nTake
NextElement == Len(streams.PIn.sent) + 1

ObserverRequiresElement ==
  /\   streams.PObs.state = SRunning
  /\   streams.PObs.nRequested < streams.PObs.nTake
  /\ ~ streams.PIn.uncons

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake


InEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ SinkOutHasElement
       \/ ~ streams.PObs.nRequested < streams.PObs.nTake
  THEN
    CASE streams.PIn.termination = TError  -> SErrored
      [] streams.PIn.termination = TCancel -> SCancelled
      [] OTHER                             -> SSucceeded
  ELSE SSucceeded

InObserverEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ Terminated(streams.PObs)
     /\ observerScope = OParent
     /\ ~ SinkOutHasElement
       \/ ~ streams.PObs.nRequested < streams.PObs.nTake
  THEN
      CASE streams.PIn.termination = TError  /\ ~ observerHandlesError  -> SErrored
	[] streams.PIn.termination = TError  /\   observerHandlesError  -> SSucceeded
	[] streams.PIn.termination = TCancel                            -> SCancelled
	[] streams.PIn.termination = TSuccess                           -> SSucceeded
	[] OTHER                                                        -> SSucceeded
  ELSE
    streams.PObs.state

ObserverEndState ==
  IF observerScope = OTransient
  THEN
    CASE streams.PIn.state = SCancelled                         -> SCancelled
      [] streams.PIn.state = SSucceeded                         -> SSucceeded
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      [] streams.PIn.state = SErrored /\   observerHandlesError -> SSucceeded
      [] OTHER                                                  -> SSucceeded
  ELSE IF observerScope = ONone THEN
    CASE streams.PIn.state = SCancelled                         -> SSucceeded
      [] streams.PIn.state = SSucceeded                         -> SSucceeded
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored   \* The error is propagated to the fore
      [] streams.PIn.state = SErrored /\   observerHandlesError -> SSucceeded
      [] OTHER                                                  -> SSucceeded
      \* Cancellation does not affect the observer stream. TODO: We're assuming that the observer now completes its work. Model infinite observer streams.
  ELSE streams.PObs.state
end define;

macro acquire() begin
  if guard > 0 then
    guard := guard - 1;
  else
    await guard > 0 \/ Terminated(streams.PIn);
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

The downstream system is PObs. It requests an element by setting uncons to TRUE.
*)
fair process in = "in"
begin
  InOutput:
  while streams.PIn.state = SRunning
	/\ streams.PObs.nRequested < streams.PObs.nTake
	/\ SinkOutHasElement do
    local_el := NextElement;
    streams.PObs.nRequested := streams.PObs.nRequested + 1 ||
    streams.PObs.received := Append(streams.PObs.received, local_el) ||
    streams.PIn.sent := Append(streams.PIn.sent, local_el) ||
    streams.PIn.pendingWork := TRUE;
    InSendToChannel:
      if Terminated(streams.PIn) then
	goto InOnFinalize;
      elsif ~ outChan.closed then
	outChan.contents := Append(outChan.contents, NextElement);
      end if;
    InAcquireGuard:
      if Terminated(streams.PIn) then
	goto InOnFinalize;
      else
	acquire();
      end if;
  end while;
  InComplete:
    if streams.PIn.state = SRunning then
      streams.PIn.state := InEndState || streams.PObs.state := InObserverEndState;
    end if;
   InOnFinalize:
     streams.PIn.pendingWork := FALSE;
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
	  \/ Terminated(streams.PIn);
  \* If the input stream has terminated, we assume that there is still work to be done by the observer
  \* The steps between the input termination and this step represents that work
    if ~ Terminated(streams.PObs) /\ Terminated(streams.PIn) then
      streams.PObs.state := ObserverEndState;
    elsif /\ streams.PObs.state = SCancelled
	  /\ observerScope = ONone
	  /\ streams.PIn.state = SRunning then
      streams.PIn.state := SCancelled;
    end if;
  end if;

  \* TODO: The observer is transient and the `in` stream has already finished.
  ObserverOnFinalize:
    await ~ streams.PIn.pendingWork; \* Wait for the in stream to terminate
    outChan.closed := TRUE;
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
variable local_el = 0;
begin
OutPopFromChannel:
while streams.POut.state = SRunning /\ OutRequiresElement do
    await    outChan.closed
	  \/ Len(outChan.contents) > 0
	  \/ ~ streams.POut.state = SRunning;
    if Len(outChan.contents) > 0 /\ ~ Terminated(streams.POut) then
      streams.POut.nRequested := streams.POut.nRequested + 1;
      local_el := Head(outChan.contents);
      outChan.contents := Tail(outChan.contents);
      OutOutput:
	if ~ Terminated(streams.POut) then
	  streams.POut.received := Append(streams.POut.received, local_el);
	end if;
      OutReleaseGuard:
	release();
    elsif streams.POut.state = SRunning /\ outChan.closed then
	\* The output channel is closed. We must close the downstream output stream
	streams.POut.nRequested := streams.POut.nRequested + 1 ||
	streams.POut.state := SSucceeded;
    end if;
end while;

if streams.POut.state = SRunning /\ ~ OutRequiresElement then
  streams.POut.state := SSucceeded;
end if;

\* At this point, the POut stream must have terminated.
OutOnFinalize:
  if streams.PObs.state = SRunning then
  \* TODO: The observer is in a state that is interrupted but not yet cancelled.
  \* An interruption flag has been set, but the observer may yet still do work.
  \* We should model this before we model errors.
    if \/ observerScope = OParent
       \/ observerScope = OParent
	 \/ streams.PIn.state = SRunning then
	streams.PObs.state := SCancelled ||
	streams.PIn.state := SCancelled;
    else
	streams.PObs.state := SCancelled;
    end if;
  end if;
  \* TODO: If the observer stream has errored, then we should interrupt the output stream
end process;

(* This represents:
	val out = outStream.concurrently(runner)
*)
end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "e76f3e39" /\ chksum(tla) = "20e99c05")
VARIABLES observerScope, observerHandlesError, inNTake, outNTake, obsNTake,
	  streams, guard, outChan, pc

(* define statement *)
PInDownstream == streams.PObs

SinkOutHasElement == Len(streams.PIn.sent) < streams.PIn.nTake
NextElement == Len(streams.PIn.sent) + 1

ObserverRequiresElement ==
  /\   streams.PObs.state = SRunning
  /\   streams.PObs.nRequested < streams.PObs.nTake
  /\ ~ streams.PIn.uncons

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake


InEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ SinkOutHasElement
       \/ ~ streams.PObs.nRequested < streams.PObs.nTake
  THEN
    CASE streams.PIn.termination = TError  -> SErrored
      [] streams.PIn.termination = TCancel -> SCancelled
      [] OTHER                             -> SSucceeded
  ELSE SSucceeded

InObserverEndState ==
  IF /\ ~ Terminated(streams.PIn)
     /\ ~ Terminated(streams.PObs)
     /\ observerScope = OParent
     /\ ~ SinkOutHasElement
       \/ ~ streams.PObs.nRequested < streams.PObs.nTake
  THEN
      CASE streams.PIn.termination = TError  /\ ~ observerHandlesError  -> SErrored
	[] streams.PIn.termination = TError  /\   observerHandlesError  -> SSucceeded
	[] streams.PIn.termination = TCancel                            -> SCancelled
	[] streams.PIn.termination = TSuccess                           -> SSucceeded
	[] OTHER                                                        -> SSucceeded
  ELSE
    streams.PObs.state

ObserverEndState ==
  IF observerScope = OTransient
  THEN
    CASE streams.PIn.state = SCancelled                         -> SCancelled
      [] streams.PIn.state = SSucceeded                         -> SSucceeded
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      [] streams.PIn.state = SErrored /\   observerHandlesError -> SSucceeded
      [] OTHER                                                  -> SSucceeded
  ELSE IF observerScope = ONone THEN
    CASE streams.PIn.state = SCancelled                         -> SSucceeded
      [] streams.PIn.state = SSucceeded                         -> SSucceeded
      [] streams.PIn.state = SErrored /\ ~ observerHandlesError -> SErrored
      [] streams.PIn.state = SErrored /\   observerHandlesError -> SSucceeded
      [] OTHER                                                  -> SSucceeded

  ELSE streams.PObs.state

VARIABLE local_el

vars == << observerScope, observerHandlesError, inNTake, outNTake, obsNTake, 
           streams, guard, outChan, pc, local_el >>

ProcSet == {"in"} \cup {"observer"} \cup {"out"}

Init == (* Global variables *)
        /\ observerScope \in observerScopeRange
        /\ observerHandlesError \in observerHandlesErrorRange
        /\ inNTake \in inNTakeRange
        /\ outNTake \in outNTakeRange
        /\ obsNTake \in obsNTakeRange
        /\ streams =           [
                      PIn |-> [
                        state |-> SRunning,
                        sent |-> <<>>,
                        uncons |-> FALSE,
                        pendingWork |-> FALSE,
                        nTake |-> inNTake,
                        termination |-> TSuccess
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
                        nTake |-> obsNTake
                     
                      ]
                     ]
        /\ guard = 0
        /\ outChan =           [
                       closed |-> FALSE,
                       contents |-> <<>>
                     ]
        (* Process out *)
        /\ local_el = 0
        /\ pc = [self \in ProcSet |-> CASE self = "in" -> "InOutput"
                                        [] self = "observer" -> "ObserverComplete"
                                        [] self = "out" -> "OutPopFromChannel"]

InOutput == /\ pc["in"] = "InOutput"
            /\ IF streams.PIn.state = SRunning
                  /\ streams.PObs.nRequested < streams.PObs.nTake
                  /\ SinkOutHasElement
                  THEN /\ local_el' = NextElement
                       /\ streams' = [streams EXCEPT !.PObs.nRequested = streams.PObs.nRequested + 1,
                                                     !.PObs.received = Append(streams.PObs.received, local_el'),
                                                     !.PIn.sent = Append(streams.PIn.sent, local_el'),
                                                     !.PIn.pendingWork = TRUE]
                       /\ pc' = [pc EXCEPT !["in"] = "InSendToChannel"]
                  ELSE /\ pc' = [pc EXCEPT !["in"] = "InComplete"]
                       /\ UNCHANGED << streams, local_el >>
            /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                            outNTake, obsNTake, guard, outChan >>

InSendToChannel == /\ pc["in"] = "InSendToChannel"
                   /\ IF Terminated(streams.PIn)
                         THEN /\ pc' = [pc EXCEPT !["in"] = "InOnFinalize"]
                              /\ UNCHANGED outChan
                         ELSE /\ IF ~ outChan.closed
                                    THEN /\ outChan' = [outChan EXCEPT !.contents = Append(outChan.contents, NextElement)]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED outChan
                              /\ pc' = [pc EXCEPT !["in"] = "InAcquireGuard"]
                   /\ UNCHANGED << observerScope, observerHandlesError, 
                                   inNTake, outNTake, obsNTake, streams, guard, 
                                   local_el >>

InAcquireGuard == /\ pc["in"] = "InAcquireGuard"
                  /\ IF Terminated(streams.PIn)
                        THEN /\ pc' = [pc EXCEPT !["in"] = "InOnFinalize"]
                             /\ guard' = guard
                        ELSE /\ IF guard > 0
                                   THEN /\ guard' = guard - 1
                                   ELSE /\ guard > 0 \/ Terminated(streams.PIn)
                                        /\ guard' = guard
                             /\ pc' = [pc EXCEPT !["in"] = "InOutput"]
                  /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                                  outNTake, obsNTake, streams, outChan, 
                                  local_el >>

InComplete == /\ pc["in"] = "InComplete"
              /\ IF streams.PIn.state = SRunning
                    THEN /\ streams' = [streams EXCEPT !.PIn.state = InEndState,
                                                       !.PObs.state = InObserverEndState]
                    ELSE /\ TRUE
                         /\ UNCHANGED streams
              /\ pc' = [pc EXCEPT !["in"] = "InOnFinalize"]
              /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                              outNTake, obsNTake, guard, outChan, local_el >>

InOnFinalize == /\ pc["in"] = "InOnFinalize"
                /\ streams' = [streams EXCEPT !.PIn.pendingWork = FALSE]
                /\ pc' = [pc EXCEPT !["in"] = "Done"]
                /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                                outNTake, obsNTake, guard, outChan, local_el >>

in == InOutput \/ InSendToChannel \/ InAcquireGuard \/ InComplete
         \/ InOnFinalize

ObserverComplete == /\ pc["observer"] = "ObserverComplete"
                    /\ IF ~ observerScope = OParent
                          THEN /\ \/ Terminated(streams.PObs)
                                  \/ Terminated(streams.PIn)
                               /\ IF ~ Terminated(streams.PObs) /\ Terminated(streams.PIn)
                                     THEN /\ streams' = [streams EXCEPT !.PObs.state = ObserverEndState]
                                     ELSE /\ IF /\ streams.PObs.state = SCancelled
                                                /\ observerScope = ONone
                                                /\ streams.PIn.state = SRunning
                                                THEN /\ streams' = [streams EXCEPT !.PIn.state = SCancelled]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED streams
                          ELSE /\ TRUE
                               /\ UNCHANGED streams
                    /\ pc' = [pc EXCEPT !["observer"] = "ObserverOnFinalize"]
                    /\ UNCHANGED << observerScope, observerHandlesError, 
                                    inNTake, outNTake, obsNTake, guard, 
                                    outChan, local_el >>

ObserverOnFinalize == /\ pc["observer"] = "ObserverOnFinalize"
                      /\ ~ streams.PIn.pendingWork
                      /\ outChan' = [outChan EXCEPT !.closed = TRUE]
                      /\ pc' = [pc EXCEPT !["observer"] = "Done"]
                      /\ UNCHANGED << observerScope, observerHandlesError, 
                                      inNTake, outNTake, obsNTake, streams, 
                                      guard, local_el >>

observer == ObserverComplete \/ ObserverOnFinalize

OutPopFromChannel == /\ pc["out"] = "OutPopFromChannel"
                     /\ IF streams.POut.state = SRunning /\ OutRequiresElement
                           THEN /\    outChan.closed
                                   \/ Len(outChan.contents) > 0
                                   \/ ~ streams.POut.state = SRunning
                                /\ IF Len(outChan.contents) > 0 /\ ~ Terminated(streams.POut)
                                      THEN /\ streams' = [streams EXCEPT !.POut.nRequested = streams.POut.nRequested + 1]
                                           /\ local_el' = Head(outChan.contents)
                                           /\ outChan' = [outChan EXCEPT !.contents = Tail(outChan.contents)]
                                           /\ pc' = [pc EXCEPT !["out"] = "OutOutput"]
                                      ELSE /\ IF streams.POut.state = SRunning /\ outChan.closed
                                                 THEN /\ streams' = [streams EXCEPT !.POut.nRequested = streams.POut.nRequested + 1,
                                                                                    !.POut.state = SSucceeded]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED streams
                                           /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
                                           /\ UNCHANGED << outChan, local_el >>
                           ELSE /\ IF streams.POut.state = SRunning /\ ~ OutRequiresElement
                                      THEN /\ streams' = [streams EXCEPT !.POut.state = SSucceeded]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED streams
                                /\ pc' = [pc EXCEPT !["out"] = "OutOnFinalize"]
                                /\ UNCHANGED << outChan, local_el >>
                     /\ UNCHANGED << observerScope, observerHandlesError, 
                                     inNTake, outNTake, obsNTake, guard >>

OutOutput == /\ pc["out"] = "OutOutput"
             /\ IF ~ Terminated(streams.POut)
                   THEN /\ streams' = [streams EXCEPT !.POut.received = Append(streams.POut.received, local_el)]
                   ELSE /\ TRUE
                        /\ UNCHANGED streams
             /\ pc' = [pc EXCEPT !["out"] = "OutReleaseGuard"]
             /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                             outNTake, obsNTake, guard, outChan, local_el >>

OutReleaseGuard == /\ pc["out"] = "OutReleaseGuard"
                   /\ guard' = guard + 1
                   /\ pc' = [pc EXCEPT !["out"] = "OutPopFromChannel"]
                   /\ UNCHANGED << observerScope, observerHandlesError, 
                                   inNTake, outNTake, obsNTake, streams, 
                                   outChan, local_el >>

OutOnFinalize == /\ pc["out"] = "OutOnFinalize"
                 /\ IF streams.PObs.state = SRunning
                       THEN /\ IF observerScope = OParent
                                  THEN /\ streams' = [streams EXCEPT !.PObs.state = SCancelled,
                                                                     !.PIn.state = SCancelled]
                                  ELSE /\ streams' = [streams EXCEPT !.PObs.state = SCancelled]
                       ELSE /\ TRUE
                            /\ UNCHANGED streams
                 /\ pc' = [pc EXCEPT !["out"] = "Done"]
                 /\ UNCHANGED << observerScope, observerHandlesError, inNTake, 
                                 outNTake, obsNTake, guard, outChan, local_el >>

out == OutPopFromChannel \/ OutOutput \/ OutReleaseGuard \/ OutOnFinalize

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == in \/ observer \/ out
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(in)
        /\ WF_vars(observer)
        /\ WF_vars(out)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

INSTANCE ObserveSpec

=============================================================================
\* Modification History
\* Last modified Fri Jan 14 18:30:59 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
