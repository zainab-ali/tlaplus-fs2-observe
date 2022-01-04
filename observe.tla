------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences
(* This TLA+ Spec verifies

val pipe = _.take(pipeTotal)           // pipeTotal is from 0 to 3

upstream                               // UPSTREAM
.evalMap(q.enqueue)                    // QUEUE
.concurrently(q.dequeue.through(pipe)) // PIPE
.compile.drain                         // DOWNSTREAM

Where upstream can contain 0 to 3 elements.

Note that there is a non-terminating case:
The left stream will never terminate if pipeTotal = 0 because q.enqueue will block.
*)

(* --algorithm observe
variables 
          upstreamTotal \in 0..3, \* The total number of elements upstream
          upstreamPending = upstreamTotal, \* The number of elements to be pulled from upstream
          upstreamPulled = {}, \* The elements pulled from upstream
          downstreamNRequests = 0, \* The number of elements requested by downstream
          downstreamReceived = {}, \* The elements received by downstream from upstream
          downstreamFinished = FALSE, \* Whether downstream has received a "done" message
          queueNRequests = 0, \* The number of "dequeue" requests made to the queue
          queueContents = {}, \* The elements within the queue.
          queueCancelled = FALSE, \* Whether the queue has been cancelled
          pipeTotal \in 0..3, \* The maximum number of elements requested by the pipe
          pipeNRequested = 0, \* The number of elements that have been requested by the pipe 
          pipeContents = {}
define
\* Invariants
(* All elements that have been pulled from upstream were requested by downstream

Given that the value of an element corresponds to its index, this can be translated into:

For all elements in the set of "elements pulled from upstream"
The "number of elements requested from downstream" is greater than or equal to the element
*)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests
end define

macro check_queue_cancelled()
begin
  if queueCancelled then goto Cancelled end if;
end macro;

fair process left = "left"
variable element = -8;
begin
  \* While downstream has not finished
  CheckFinished:
    while ~downstreamFinished do
      \* Make a request from downstream to upstream
      MakeRequestLeft:
        downstreamNRequests := downstreamNRequests + 1;
        \* If there is an element upstream
        if upstreamPending > 0 then
          \* Then pull the element
          \* This is a 1-indexed sequence
          element := upstreamTotal - upstreamPending + 1;
          upstreamPending := upstreamPending - 1;
          upstreamPulled := upstreamPulled \union {element};
          \* While the queue has not received a dequeue request
          BlockUntilEnqueued:
            await queueNRequests > 0;
          Enqueue:
            \* Then remove the "dequeue" request
            queueNRequests := queueNRequests -1;
            \* And enqueue the element
            queueContents := queueContents \union {element};
            \* And deliver the element downstream
            downstreamReceived := downstreamReceived \union {element};
            \* If the queue has received a dequeue request
        else
          \* Else deliver "done" downstream
          CompleteLeft:
            downstreamFinished := TRUE;
            queueCancelled := TRUE
        end if;
    end while;
end process;

fair process right = "right"
variable element = -9;
begin 
  \* While the pipe has not finished
  MakeRequestRight:
    while pipeNRequested < pipeTotal /\ ~queueCancelled do
      pipeNRequested := pipeNRequested + 1;
      CheckCancellation: check_queue_cancelled();
      BlockUntilDequeued:
        \* TODO: The right stream is blocked so cannot check the cancellation flag.
        \* Make a "dequeue" request 
        queueNRequests := queueNRequests + 1;
        \* While there is no element in the queue: loop
        BlockUntilDequeuedCheckCancellation:
        while queueContents = {} do
          check_queue_cancelled();
        end while;
      CheckCancellation1: check_queue_cancelled();
      Dequeue:
        \* Take the element off the queue
        element := CHOOSE x \in queueContents : TRUE;
        queueContents := queueContents \ { element} ;
        \* Receive it in the pipe
      CheckCancellation2: check_queue_cancelled();
      Send: 
        pipeContents := pipeContents \union {element};
    end while;
  Cancelled:
    skip;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "e5ab2323" /\ chksum(tla) = "3a63e42c")
\* Process variable element of process left at line 50 col 10 changed to element_
VARIABLES upstreamTotal, upstreamPending, upstreamPulled, downstreamNRequests, 
          downstreamReceived, downstreamFinished, queueNRequests, 
          queueContents, queueCancelled, pipeTotal, pipeNRequested, 
          pipeContents, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests

VARIABLES element_, element

vars == << upstreamTotal, upstreamPending, upstreamPulled, 
           downstreamNRequests, downstreamReceived, downstreamFinished, 
           queueNRequests, queueContents, queueCancelled, pipeTotal, 
           pipeNRequested, pipeContents, pc, element_, element >>

ProcSet == {"left"} \cup {"right"}

Init == (* Global variables *)
        /\ upstreamTotal \in 0..3
        /\ upstreamPending = upstreamTotal
        /\ upstreamPulled = {}
        /\ downstreamNRequests = 0
        /\ downstreamReceived = {}
        /\ downstreamFinished = FALSE
        /\ queueNRequests = 0
        /\ queueContents = {}
        /\ queueCancelled = FALSE
        /\ pipeTotal \in 0..3
        /\ pipeNRequested = 0
        /\ pipeContents = {}
        (* Process left *)
        /\ element_ = -8
        (* Process right *)
        /\ element = -9
        /\ pc = [self \in ProcSet |-> CASE self = "left" -> "CheckFinished"
                                        [] self = "right" -> "MakeRequestRight"]

CheckFinished == /\ pc["left"] = "CheckFinished"
                 /\ IF ~downstreamFinished
                       THEN /\ pc' = [pc EXCEPT !["left"] = "MakeRequestLeft"]
                       ELSE /\ pc' = [pc EXCEPT !["left"] = "Done"]
                 /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                 upstreamPulled, downstreamNRequests, 
                                 downstreamReceived, downstreamFinished, 
                                 queueNRequests, queueContents, queueCancelled, 
                                 pipeTotal, pipeNRequested, pipeContents, 
                                 element_, element >>

MakeRequestLeft == /\ pc["left"] = "MakeRequestLeft"
                   /\ downstreamNRequests' = downstreamNRequests + 1
                   /\ IF upstreamPending > 0
                         THEN /\ element_' = upstreamTotal - upstreamPending + 1
                              /\ upstreamPending' = upstreamPending - 1
                              /\ upstreamPulled' = (upstreamPulled \union {element_'})
                              /\ pc' = [pc EXCEPT !["left"] = "BlockUntilEnqueued"]
                         ELSE /\ pc' = [pc EXCEPT !["left"] = "CompleteLeft"]
                              /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                              element_ >>
                   /\ UNCHANGED << upstreamTotal, downstreamReceived, 
                                   downstreamFinished, queueNRequests, 
                                   queueContents, queueCancelled, pipeTotal, 
                                   pipeNRequested, pipeContents, element >>

BlockUntilEnqueued == /\ pc["left"] = "BlockUntilEnqueued"
                      /\ queueNRequests > 0
                      /\ pc' = [pc EXCEPT !["left"] = "Enqueue"]
                      /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                      upstreamPulled, downstreamNRequests, 
                                      downstreamReceived, downstreamFinished, 
                                      queueNRequests, queueContents, 
                                      queueCancelled, pipeTotal, 
                                      pipeNRequested, pipeContents, element_, 
                                      element >>

Enqueue == /\ pc["left"] = "Enqueue"
           /\ queueNRequests' = queueNRequests -1
           /\ queueContents' = (queueContents \union {element_})
           /\ downstreamReceived' = (downstreamReceived \union {element_})
           /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
           /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                           downstreamNRequests, downstreamFinished, 
                           queueCancelled, pipeTotal, pipeNRequested, 
                           pipeContents, element_, element >>

CompleteLeft == /\ pc["left"] = "CompleteLeft"
                /\ downstreamFinished' = TRUE
                /\ queueCancelled' = TRUE
                /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
                /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                                downstreamNRequests, downstreamReceived, 
                                queueNRequests, queueContents, pipeTotal, 
                                pipeNRequested, pipeContents, element_, 
                                element >>

left == CheckFinished \/ MakeRequestLeft \/ BlockUntilEnqueued \/ Enqueue
           \/ CompleteLeft

MakeRequestRight == /\ pc["right"] = "MakeRequestRight"
                    /\ IF pipeNRequested < pipeTotal /\ ~queueCancelled
                          THEN /\ pipeNRequested' = pipeNRequested + 1
                               /\ pc' = [pc EXCEPT !["right"] = "CheckCancellation"]
                          ELSE /\ pc' = [pc EXCEPT !["right"] = "Cancelled"]
                               /\ UNCHANGED pipeNRequested
                    /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                    upstreamPulled, downstreamNRequests, 
                                    downstreamReceived, downstreamFinished, 
                                    queueNRequests, queueContents, 
                                    queueCancelled, pipeTotal, pipeContents, 
                                    element_, element >>

CheckCancellation == /\ pc["right"] = "CheckCancellation"
                     /\ IF queueCancelled
                           THEN /\ pc' = [pc EXCEPT !["right"] = "Cancelled"]
                           ELSE /\ pc' = [pc EXCEPT !["right"] = "BlockUntilDequeued"]
                     /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                     upstreamPulled, downstreamNRequests, 
                                     downstreamReceived, downstreamFinished, 
                                     queueNRequests, queueContents, 
                                     queueCancelled, pipeTotal, pipeNRequested, 
                                     pipeContents, element_, element >>

BlockUntilDequeued == /\ pc["right"] = "BlockUntilDequeued"
                      /\ queueNRequests' = queueNRequests + 1
                      /\ pc' = [pc EXCEPT !["right"] = "BlockUntilDequeuedCheckCancellation"]
                      /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                      upstreamPulled, downstreamNRequests, 
                                      downstreamReceived, downstreamFinished, 
                                      queueContents, queueCancelled, pipeTotal, 
                                      pipeNRequested, pipeContents, element_, 
                                      element >>

BlockUntilDequeuedCheckCancellation == /\ pc["right"] = "BlockUntilDequeuedCheckCancellation"
                                       /\ IF queueContents = {}
                                             THEN /\ IF queueCancelled
                                                        THEN /\ pc' = [pc EXCEPT !["right"] = "Cancelled"]
                                                        ELSE /\ pc' = [pc EXCEPT !["right"] = "BlockUntilDequeuedCheckCancellation"]
                                             ELSE /\ pc' = [pc EXCEPT !["right"] = "CheckCancellation1"]
                                       /\ UNCHANGED << upstreamTotal, 
                                                       upstreamPending, 
                                                       upstreamPulled, 
                                                       downstreamNRequests, 
                                                       downstreamReceived, 
                                                       downstreamFinished, 
                                                       queueNRequests, 
                                                       queueContents, 
                                                       queueCancelled, 
                                                       pipeTotal, 
                                                       pipeNRequested, 
                                                       pipeContents, element_, 
                                                       element >>

CheckCancellation1 == /\ pc["right"] = "CheckCancellation1"
                      /\ IF queueCancelled
                            THEN /\ pc' = [pc EXCEPT !["right"] = "Cancelled"]
                            ELSE /\ pc' = [pc EXCEPT !["right"] = "Dequeue"]
                      /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                      upstreamPulled, downstreamNRequests, 
                                      downstreamReceived, downstreamFinished, 
                                      queueNRequests, queueContents, 
                                      queueCancelled, pipeTotal, 
                                      pipeNRequested, pipeContents, element_, 
                                      element >>

Dequeue == /\ pc["right"] = "Dequeue"
           /\ element' = (CHOOSE x \in queueContents : TRUE)
           /\ queueContents' = queueContents \ { element'}
           /\ pc' = [pc EXCEPT !["right"] = "CheckCancellation2"]
           /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                           downstreamNRequests, downstreamReceived, 
                           downstreamFinished, queueNRequests, queueCancelled, 
                           pipeTotal, pipeNRequested, pipeContents, element_ >>

CheckCancellation2 == /\ pc["right"] = "CheckCancellation2"
                      /\ IF queueCancelled
                            THEN /\ pc' = [pc EXCEPT !["right"] = "Cancelled"]
                            ELSE /\ pc' = [pc EXCEPT !["right"] = "Send"]
                      /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                      upstreamPulled, downstreamNRequests, 
                                      downstreamReceived, downstreamFinished, 
                                      queueNRequests, queueContents, 
                                      queueCancelled, pipeTotal, 
                                      pipeNRequested, pipeContents, element_, 
                                      element >>

Send == /\ pc["right"] = "Send"
        /\ pipeContents' = (pipeContents \union {element})
        /\ pc' = [pc EXCEPT !["right"] = "MakeRequestRight"]
        /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                        downstreamNRequests, downstreamReceived, 
                        downstreamFinished, queueNRequests, queueContents, 
                        queueCancelled, pipeTotal, pipeNRequested, element_, 
                        element >>

Cancelled == /\ pc["right"] = "Cancelled"
             /\ TRUE
             /\ pc' = [pc EXCEPT !["right"] = "Done"]
             /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                             downstreamNRequests, downstreamReceived, 
                             downstreamFinished, queueNRequests, queueContents, 
                             queueCancelled, pipeTotal, pipeNRequested, 
                             pipeContents, element_, element >>

right == MakeRequestRight \/ CheckCancellation \/ BlockUntilDequeued
            \/ BlockUntilDequeuedCheckCancellation \/ CheckCancellation1
            \/ Dequeue \/ CheckCancellation2 \/ Send \/ Cancelled

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == left \/ right
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(left)
        /\ WF_vars(right)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Jan 04 19:26:14 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
