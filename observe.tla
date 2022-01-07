------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences
(* This TLA+ Spec verifies

val pipe = _.take(pipeTotal)           // pipeTotal is from 0 to 3

upstream                               // UPSTREAM
.evalMap(q.enqueue)                    // QUEUE
.concurrently(q.dequeue.through(pipe)) // PIPE
.compile.drain                         // DOWNSTREAM

q.dequeue                              // DEQUEUE
  .concurrently(
  upstream.evalTap(q.enqueue).through(pipe) ++ q.close
)

Where upstream can contain 0 to 3 elements.

Note that there is a non-terminating case:
The left stream will never terminate if pipeTotal = 0 because q.enqueue will block.

If pipeTotal is >= upstreamTotal then the right stream may be cancelled.
*)

\* Redeclare the symbols from ObserveSpec
CONSTANTS Streams, PIn, POut, PObs
CONSTANTS States, SRunning, SErrored, SCancelled, SSucceeded

(* --algorithm hello_world
variable streams = [
 PIn |-> [
   state |-> SRunning,
   sent |-> <<>>
 ],
 POut |-> [
   state |-> SRunning,
   nRequested |-> 0
 ] 
];
begin
  A: 
    \*streams.POut.nRequested := 1 ||
    streams.PIn.sent := <<1>>;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "af74177a" /\ chksum(tla) = "aed4c27b")
VARIABLES streams, pc

vars == << streams, pc >>

Init == (* Global variables *)
        /\ streams =                    [
                      PIn |-> [
                        state |-> SRunning,
                        sent |-> <<>>
                      ],
                      POut |-> [
                        state |-> SRunning,
                        nRequested |-> 0
                      ]
                     ]
        /\ pc = "A"

A == /\ pc = "A"
     /\ streams' = [streams EXCEPT !.PIn.sent = <<1>>]
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

INSTANCE ObserveSpec

=============================================================================
\* Modification History
\* Last modified Fri Jan 07 15:27:10 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
