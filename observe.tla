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
 - PObs corresponds to sinkOut.through(pipe)

The parameter `maxQueued` is fixed at 1 to test `observe` only, so excludes
`observeAsync`.

The input stream `self` is finite, capped at nTake.
*)

\* Redeclare the symbols from ObserveSpec
CONSTANTS Streams, PIn, POut, PObs
CONSTANTS States, SRunning, SErrored, SCancelled, SSucceeded
\* CONSTANTS TerminationState, TError, TCancel, TSucceed

CONSTANTS inNTakeRange, outNTakeRange, obsNTakeRange

AppendHead(seq, els) == Append(seq, Head(els))

Terminated(stream) == ~ stream.state = SRunning

(* --algorithm observe
variable inNTake \in inNTakeRange,
         outNTake \in outNTakeRange,
         obsNTake \in obsNTakeRange,
streams = [
 PIn |-> [
   state |-> SRunning,
   sent |-> <<>>,
   uncons |-> FALSE,        \* Whether the downstream system has requested an element
   nTake |-> inNTake           \* The maximum number of elements to send
   \* termination |-> TSucceed \* The state we intend the stream to terminate in, should all its elements be requested.
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
],
outStreamUncons = FALSE \* Whether the output stream has requested an element from outStream
;

define
PInDownstream == streams.PObs

SinkOutHasElement == Len(streams.PIn.sent) < streams.PIn.nTake
NextElement == Len(streams.PIn.sent) + 1

ObserverRequiresElement == 
  /\   streams.PObs.state = SRunning
  /\   streams.PObs.nRequested < streams.PObs.nTake 
  /\ ~ streams.PIn.uncons

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake

end define;

macro acquire() begin
  if guard > 0 then
    guard := guard - 1;
  else 
    await guard > 0;
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
process sinkOut = "sinkOut"
begin
  SinkOutLoop:
  \* TODO: Where do we set uncons?
  while streams.PIn.state = SRunning do
    SinkOutWaitForUncons: 
      await \/ Terminated(streams.PObs)
            \/ streams.PIn.uncons;
    if Terminated(streams.PObs) then
	  CleanUp:
        streams.PIn.state := SSucceeded;
    else
       streams.PIn.uncons := FALSE;
       \* Downstream is running and requested an element
       if SinkOutHasElement then
         SinkOutOutput:
           streams.PObs.received := Append(streams.PObs.received, NextElement) ||
           streams.PIn.sent := Append(streams.PIn.sent, NextElement);
         SendToChannel:
           if ~ outChan.closed then
             outChan.contents := Append(outChan.contents, NextElement);
           end if;
         Guard:
           acquire();
       else
         \* There are no more elements to output
         OutputDone:
           streams.PIn.state := SSucceeded;
       end if;
    end if;
  end while;
end process;

(* This represents runner in 
        val runner =
          sinkOut.through(pipe).onFinalize(outChan.close.void)
It also represents the right part of
        .concurrently(runner)
        
as it pulls on the runner stream.
*)
process runner = "runner"
begin
  RunnerLoop:
  while ObserverRequiresElement do
    RunnerMakeUncons:
      streams.PObs.nRequested := streams.PObs.nRequested + 1 ||
      streams.PIn.uncons := TRUE;
    RunnerWaitForElement:
      await    Len(streams.PObs.received) = streams.PObs.nRequested
            \/ ~ streams.PObs.state = SRunning
            \/ ~ streams.PIn.state = SRunning;
      if streams.PIn.state = SSucceeded /\ streams.PObs.state = SRunning then
        streams.PObs.state := SSucceeded;
      end if
  end while;
  RunnerOnFinalize:
    outChan.closed := TRUE;
end process;

(* Ths represents
        def outStream =
          outChan.stream
            .flatMap { chunk =>
              Stream.chunk(chunk).onFinalize(guard.release)
            }
            
It is pulled on by a downstream component.

The cancellation checks could be improved
*)
process outStream = "outStream"
variable local_el = 0;
begin
OutStreamLoop:
while streams.POut.state = SRunning do
  OutStreamWaitForUncons:
    await \/ ~ streams.POut.state = SRunning
          \/ outStreamUncons;
  if streams.POut.state = SRunning then
    await    outChan.closed 
          \/ Len(outChan.contents) > 0 
          \/ ~ streams.POut.state = SRunning;
    if Len(outChan.contents) > 0 then
      PopFromChannel:
        if ~ Terminated(streams.POut) then
          local_el := Head(outChan.contents);
          outChan.contents := Tail(outChan.contents);
        end if;
      SinkOutOutput:
        if ~ Terminated(streams.POut) then
          streams.POut.received := Append(streams.POut.received, local_el);
    	end if;
      ReleaseGuard:
        release();
    elsif streams.POut.state = SRunning /\ outChan.closed then
        \* The output channel is closed. We must close the downstream output stream
        streams.POut.state := SSucceeded;
    end if;
  end if;
end while;
end process;

(* This represents:
        val out = outStream.concurrently(runner)
*)
process concurrentlyLeft = "concurrentlyLeft"
begin
ConcurrentlyLeftLoop:
while OutRequiresElement do
ConcurrentlyLeftMakeUncons:
  streams.POut.nRequested := streams.POut.nRequested + 1;
  outStreamUncons := TRUE;
ConcurrentlyLeftWaitForElement:
  await    Len(streams.POut.received) = streams.POut.nRequested 
        \/ Terminated(streams.POut);
end while;
ConcurrentlyLeftOnFinalize:
  \* FIXME: If the observer stream has errored, then we should interrupt the output stream
  if streams.PObs.state = SErrored then
    streams.POut.state := SErrored;
  elsif streams.PObs.state = SRunning then
    streams.PObs.state := SCancelled ||
    streams.POut.state := SSucceeded;
  else
    streams.POut.state := SSucceeded;
  end if;
end process;
end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "b4268b52" /\ chksum(tla) = "5b9a3ccf")
\* Label SinkOutOutput of process sinkOut at line 150 col 12 changed to SinkOutOutput_
VARIABLES inNTake, outNTake, obsNTake, streams, guard, outChan, 
          outStreamUncons, pc

(* define statement *)
PInDownstream == streams.PObs

SinkOutHasElement == Len(streams.PIn.sent) < streams.PIn.nTake
NextElement == Len(streams.PIn.sent) + 1

ObserverRequiresElement ==
  /\   streams.PObs.state = SRunning
  /\   streams.PObs.nRequested < streams.PObs.nTake
  /\ ~ streams.PIn.uncons

OutRequiresElement == streams.POut.nRequested < streams.POut.nTake

VARIABLE local_el

vars == << inNTake, outNTake, obsNTake, streams, guard, outChan, 
           outStreamUncons, pc, local_el >>

ProcSet == {"sinkOut"} \cup {"runner"} \cup {"outStream"} \cup {"concurrentlyLeft"}

Init == (* Global variables *)
        /\ inNTake \in inNTakeRange
        /\ outNTake \in outNTakeRange
        /\ obsNTake \in obsNTakeRange
        /\ streams =           [
                      PIn |-> [
                        state |-> SRunning,
                        sent |-> <<>>,
                        uncons |-> FALSE,
                        nTake |-> inNTake
                     
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
        /\ outStreamUncons = FALSE
        (* Process outStream *)
        /\ local_el = 0
        /\ pc = [self \in ProcSet |-> CASE self = "sinkOut" -> "SinkOutLoop"
                                        [] self = "runner" -> "RunnerLoop"
                                        [] self = "outStream" -> "OutStreamLoop"
                                        [] self = "concurrentlyLeft" -> "ConcurrentlyLeftLoop"]

SinkOutLoop == /\ pc["sinkOut"] = "SinkOutLoop"
               /\ IF streams.PIn.state = SRunning
                     THEN /\ pc' = [pc EXCEPT !["sinkOut"] = "SinkOutWaitForUncons"]
                     ELSE /\ pc' = [pc EXCEPT !["sinkOut"] = "Done"]
               /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, guard, 
                               outChan, outStreamUncons, local_el >>

SinkOutWaitForUncons == /\ pc["sinkOut"] = "SinkOutWaitForUncons"
                        /\ \/ Terminated(streams.PObs)
                           \/ streams.PIn.uncons
                        /\ IF Terminated(streams.PObs)
                              THEN /\ pc' = [pc EXCEPT !["sinkOut"] = "CleanUp"]
                                   /\ UNCHANGED streams
                              ELSE /\ streams' = [streams EXCEPT !.PIn.uncons = FALSE]
                                   /\ IF SinkOutHasElement
                                         THEN /\ pc' = [pc EXCEPT !["sinkOut"] = "SinkOutOutput_"]
                                         ELSE /\ pc' = [pc EXCEPT !["sinkOut"] = "OutputDone"]
                        /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, 
                                        outChan, outStreamUncons, local_el >>

CleanUp == /\ pc["sinkOut"] = "CleanUp"
           /\ streams' = [streams EXCEPT !.PIn.state = SSucceeded]
           /\ pc' = [pc EXCEPT !["sinkOut"] = "SinkOutLoop"]
           /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, outChan, 
                           outStreamUncons, local_el >>

SinkOutOutput_ == /\ pc["sinkOut"] = "SinkOutOutput_"
                  /\ streams' = [streams EXCEPT !.PObs.received = Append(streams.PObs.received, NextElement),
                                                !.PIn.sent = Append(streams.PIn.sent, NextElement)]
                  /\ pc' = [pc EXCEPT !["sinkOut"] = "SendToChannel"]
                  /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, outChan, 
                                  outStreamUncons, local_el >>

SendToChannel == /\ pc["sinkOut"] = "SendToChannel"
                 /\ IF ~ outChan.closed
                       THEN /\ outChan' = [outChan EXCEPT !.contents = Append(outChan.contents, NextElement)]
                       ELSE /\ TRUE
                            /\ UNCHANGED outChan
                 /\ pc' = [pc EXCEPT !["sinkOut"] = "Guard"]
                 /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, guard, 
                                 outStreamUncons, local_el >>

Guard == /\ pc["sinkOut"] = "Guard"
         /\ IF guard > 0
               THEN /\ guard' = guard - 1
               ELSE /\ guard > 0
                    /\ guard' = guard
         /\ pc' = [pc EXCEPT !["sinkOut"] = "SinkOutLoop"]
         /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, outChan, 
                         outStreamUncons, local_el >>

OutputDone == /\ pc["sinkOut"] = "OutputDone"
              /\ streams' = [streams EXCEPT !.PIn.state = SSucceeded]
              /\ pc' = [pc EXCEPT !["sinkOut"] = "SinkOutLoop"]
              /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, outChan, 
                              outStreamUncons, local_el >>

sinkOut == SinkOutLoop \/ SinkOutWaitForUncons \/ CleanUp \/ SinkOutOutput_
              \/ SendToChannel \/ Guard \/ OutputDone

RunnerLoop == /\ pc["runner"] = "RunnerLoop"
              /\ IF ObserverRequiresElement
                    THEN /\ pc' = [pc EXCEPT !["runner"] = "RunnerMakeUncons"]
                    ELSE /\ pc' = [pc EXCEPT !["runner"] = "RunnerOnFinalize"]
              /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, guard, 
                              outChan, outStreamUncons, local_el >>

RunnerMakeUncons == /\ pc["runner"] = "RunnerMakeUncons"
                    /\ streams' = [streams EXCEPT !.PObs.nRequested = streams.PObs.nRequested + 1,
                                                  !.PIn.uncons = TRUE]
                    /\ pc' = [pc EXCEPT !["runner"] = "RunnerWaitForElement"]
                    /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, 
                                    outChan, outStreamUncons, local_el >>

RunnerWaitForElement == /\ pc["runner"] = "RunnerWaitForElement"
                        /\    Len(streams.PObs.received) = streams.PObs.nRequested
                           \/ ~ streams.PObs.state = SRunning
                           \/ ~ streams.PIn.state = SRunning
                        /\ IF streams.PIn.state = SSucceeded /\ streams.PObs.state = SRunning
                              THEN /\ streams' = [streams EXCEPT !.PObs.state = SSucceeded]
                              ELSE /\ TRUE
                                   /\ UNCHANGED streams
                        /\ pc' = [pc EXCEPT !["runner"] = "RunnerLoop"]
                        /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, 
                                        outChan, outStreamUncons, local_el >>

RunnerOnFinalize == /\ pc["runner"] = "RunnerOnFinalize"
                    /\ outChan' = [outChan EXCEPT !.closed = TRUE]
                    /\ pc' = [pc EXCEPT !["runner"] = "Done"]
                    /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, 
                                    guard, outStreamUncons, local_el >>

runner == RunnerLoop \/ RunnerMakeUncons \/ RunnerWaitForElement
             \/ RunnerOnFinalize

OutStreamLoop == /\ pc["outStream"] = "OutStreamLoop"
                 /\ IF streams.POut.state = SRunning
                       THEN /\ pc' = [pc EXCEPT !["outStream"] = "OutStreamWaitForUncons"]
                       ELSE /\ pc' = [pc EXCEPT !["outStream"] = "Done"]
                 /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, guard, 
                                 outChan, outStreamUncons, local_el >>

OutStreamWaitForUncons == /\ pc["outStream"] = "OutStreamWaitForUncons"
                          /\ \/ ~ streams.POut.state = SRunning
                             \/ outStreamUncons
                          /\ IF streams.POut.state = SRunning
                                THEN /\    outChan.closed
                                        \/ Len(outChan.contents) > 0
                                        \/ ~ streams.POut.state = SRunning
                                     /\ IF Len(outChan.contents) > 0
                                           THEN /\ pc' = [pc EXCEPT !["outStream"] = "PopFromChannel"]
                                                /\ UNCHANGED streams
                                           ELSE /\ IF streams.POut.state = SRunning /\ outChan.closed
                                                      THEN /\ streams' = [streams EXCEPT !.POut.state = SSucceeded]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED streams
                                                /\ pc' = [pc EXCEPT !["outStream"] = "OutStreamLoop"]
                                ELSE /\ pc' = [pc EXCEPT !["outStream"] = "OutStreamLoop"]
                                     /\ UNCHANGED streams
                          /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, 
                                          outChan, outStreamUncons, local_el >>

PopFromChannel == /\ pc["outStream"] = "PopFromChannel"
                  /\ IF ~ Terminated(streams.POut)
                        THEN /\ local_el' = Head(outChan.contents)
                             /\ outChan' = [outChan EXCEPT !.contents = Tail(outChan.contents)]
                        ELSE /\ TRUE
                             /\ UNCHANGED << outChan, local_el >>
                  /\ pc' = [pc EXCEPT !["outStream"] = "SinkOutOutput"]
                  /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, guard, 
                                  outStreamUncons >>

SinkOutOutput == /\ pc["outStream"] = "SinkOutOutput"
                 /\ IF ~ Terminated(streams.POut)
                       THEN /\ streams' = [streams EXCEPT !.POut.received = Append(streams.POut.received, local_el)]
                       ELSE /\ TRUE
                            /\ UNCHANGED streams
                 /\ pc' = [pc EXCEPT !["outStream"] = "ReleaseGuard"]
                 /\ UNCHANGED << inNTake, outNTake, obsNTake, guard, outChan, 
                                 outStreamUncons, local_el >>

ReleaseGuard == /\ pc["outStream"] = "ReleaseGuard"
                /\ guard' = guard + 1
                /\ pc' = [pc EXCEPT !["outStream"] = "OutStreamLoop"]
                /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, outChan, 
                                outStreamUncons, local_el >>

outStream == OutStreamLoop \/ OutStreamWaitForUncons \/ PopFromChannel
                \/ SinkOutOutput \/ ReleaseGuard

ConcurrentlyLeftLoop == /\ pc["concurrentlyLeft"] = "ConcurrentlyLeftLoop"
                        /\ IF OutRequiresElement
                              THEN /\ pc' = [pc EXCEPT !["concurrentlyLeft"] = "ConcurrentlyLeftMakeUncons"]
                              ELSE /\ pc' = [pc EXCEPT !["concurrentlyLeft"] = "ConcurrentlyLeftOnFinalize"]
                        /\ UNCHANGED << inNTake, outNTake, obsNTake, streams, 
                                        guard, outChan, outStreamUncons, 
                                        local_el >>

ConcurrentlyLeftMakeUncons == /\ pc["concurrentlyLeft"] = "ConcurrentlyLeftMakeUncons"
                              /\ streams' = [streams EXCEPT !.POut.nRequested = streams.POut.nRequested + 1]
                              /\ outStreamUncons' = TRUE
                              /\ pc' = [pc EXCEPT !["concurrentlyLeft"] = "ConcurrentlyLeftWaitForElement"]
                              /\ UNCHANGED << inNTake, outNTake, obsNTake, 
                                              guard, outChan, local_el >>

ConcurrentlyLeftWaitForElement == /\ pc["concurrentlyLeft"] = "ConcurrentlyLeftWaitForElement"
                                  /\    Len(streams.POut.received) = streams.POut.nRequested
                                     \/ Terminated(streams.POut)
                                  /\ pc' = [pc EXCEPT !["concurrentlyLeft"] = "ConcurrentlyLeftLoop"]
                                  /\ UNCHANGED << inNTake, outNTake, obsNTake, 
                                                  streams, guard, outChan, 
                                                  outStreamUncons, local_el >>

ConcurrentlyLeftOnFinalize == /\ pc["concurrentlyLeft"] = "ConcurrentlyLeftOnFinalize"
                              /\ IF streams.PObs.state = SErrored
                                    THEN /\ streams' = [streams EXCEPT !.POut.state = SErrored]
                                    ELSE /\ IF streams.PObs.state = SRunning
                                               THEN /\ streams' = [streams EXCEPT !.PObs.state = SCancelled,
                                                                                  !.POut.state = SSucceeded]
                                               ELSE /\ streams' = [streams EXCEPT !.POut.state = SSucceeded]
                              /\ pc' = [pc EXCEPT !["concurrentlyLeft"] = "Done"]
                              /\ UNCHANGED << inNTake, outNTake, obsNTake, 
                                              guard, outChan, outStreamUncons, 
                                              local_el >>

concurrentlyLeft == ConcurrentlyLeftLoop \/ ConcurrentlyLeftMakeUncons
                       \/ ConcurrentlyLeftWaitForElement
                       \/ ConcurrentlyLeftOnFinalize

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == sinkOut \/ runner \/ outStream \/ concurrentlyLeft
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

INSTANCE ObserveSpec

=============================================================================
\* Modification History
\* Last modified Sat Jan 08 12:25:20 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
