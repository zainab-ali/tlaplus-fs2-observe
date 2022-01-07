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
CONSTANTS Streams, P_in, P_out, P_obs
CONSTANTS States, S_Running, S_Errored, S_Cancelled, S_Succeeded
VARIABLES streams
INSTANCE ObserveSpec

(* --algorithm hello_world
variable s \in {"Hello", "World!"};
begin
  A: 
    s := "";
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c711c0af" /\ chksum(tla) = "61a234c6")
VARIABLES s, pc

vars == << s, pc >>

Init == (* Global variables *)
        /\ s \in {"Hello", "World!"}
        /\ pc = "A"

A == /\ pc = "A"
     /\ s' = ""
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Jan 07 14:41:02 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
