------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences
(* This TLA+ Spec verifies

val pipe = _.take(1)

upstream                               // UPSTREAM
.evalMap(q.enqueue)                    // QUEUE
.concurrently(q.dequeue.through(pipe)) // PIPE
.compile.drain                         // DOWNSTREAM

Where upstream can contain 0 to 3 elements.
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
            await queueNRequests = 0;
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
          downstreamFinished := TRUE
        end if;
    end while;
end process;

fair process right = "right"
variable element = -9;
begin 
  \* While the pipe has not finished
  MakeRequestRight:
    while pipeNRequested < pipeTotal do
      pipeNRequested := pipeNRequested + 1;
      BlockUntilDequeued:
        \* Make a "dequeue" request 
        queueNRequests := queueNRequests + 1;
        \* While there is no element in the queue: loop
        await queueContents /= {};
      Dequeue:
        \* Take the element off the queue
        element := CHOOSE x \in queueContents : TRUE;
        queueContents := queueContents \ { element} ;
        \* Receive it in the pipe
      Send: 
        pipeContents := pipeContents \union {element};
    end while;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "215be21c" /\ chksum(tla) = "586561f6")
\* Process variable element of process left at line 40 col 10 changed to element_
VARIABLES upstreamTotal, upstreamPending, upstreamPulled, downstreamNRequests, 
          downstreamReceived, downstreamFinished, queueNRequests, 
          queueContents, pipeTotal, pipeNRequested, pipeContents, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests

VARIABLES element_, element

vars == << upstreamTotal, upstreamPending, upstreamPulled, 
           downstreamNRequests, downstreamReceived, downstreamFinished, 
           queueNRequests, queueContents, pipeTotal, pipeNRequested, 
           pipeContents, pc, element_, element >>

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
                                 queueNRequests, queueContents, pipeTotal, 
                                 pipeNRequested, pipeContents, element_, 
                                 element >>

MakeRequestLeft == /\ pc["left"] = "MakeRequestLeft"
                   /\ downstreamNRequests' = downstreamNRequests + 1
                   /\ IF upstreamPending > 0
                         THEN /\ element_' = upstreamTotal - upstreamPending + 1
                              /\ upstreamPending' = upstreamPending - 1
                              /\ upstreamPulled' = (upstreamPulled \union {element_'})
                              /\ pc' = [pc EXCEPT !["left"] = "BlockUntilEnqueued"]
                              /\ UNCHANGED downstreamFinished
                         ELSE /\ downstreamFinished' = TRUE
                              /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
                              /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                              element_ >>
                   /\ UNCHANGED << upstreamTotal, downstreamReceived, 
                                   queueNRequests, queueContents, pipeTotal, 
                                   pipeNRequested, pipeContents, element >>

BlockUntilEnqueued == /\ pc["left"] = "BlockUntilEnqueued"
                      /\ queueNRequests = 0
                      /\ pc' = [pc EXCEPT !["left"] = "Enqueue"]
                      /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                      upstreamPulled, downstreamNRequests, 
                                      downstreamReceived, downstreamFinished, 
                                      queueNRequests, queueContents, pipeTotal, 
                                      pipeNRequested, pipeContents, element_, 
                                      element >>

Enqueue == /\ pc["left"] = "Enqueue"
           /\ queueNRequests' = queueNRequests -1
           /\ queueContents' = (queueContents \union {element_})
           /\ downstreamReceived' = (downstreamReceived \union {element_})
           /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
           /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                           downstreamNRequests, downstreamFinished, pipeTotal, 
                           pipeNRequested, pipeContents, element_, element >>

left == CheckFinished \/ MakeRequestLeft \/ BlockUntilEnqueued \/ Enqueue

MakeRequestRight == /\ pc["right"] = "MakeRequestRight"
                    /\ IF pipeNRequested < pipeTotal
                          THEN /\ pipeNRequested' = pipeNRequested + 1
                               /\ pc' = [pc EXCEPT !["right"] = "BlockUntilDequeued"]
                          ELSE /\ pc' = [pc EXCEPT !["right"] = "Done"]
                               /\ UNCHANGED pipeNRequested
                    /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                    upstreamPulled, downstreamNRequests, 
                                    downstreamReceived, downstreamFinished, 
                                    queueNRequests, queueContents, pipeTotal, 
                                    pipeContents, element_, element >>

BlockUntilDequeued == /\ pc["right"] = "BlockUntilDequeued"
                      /\ queueNRequests' = queueNRequests + 1
                      /\ queueContents /= {}
                      /\ pc' = [pc EXCEPT !["right"] = "Dequeue"]
                      /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                      upstreamPulled, downstreamNRequests, 
                                      downstreamReceived, downstreamFinished, 
                                      queueContents, pipeTotal, pipeNRequested, 
                                      pipeContents, element_, element >>

Dequeue == /\ pc["right"] = "Dequeue"
           /\ element' = (CHOOSE x \in queueContents : TRUE)
           /\ queueContents' = queueContents \ { element'}
           /\ pc' = [pc EXCEPT !["right"] = "Send"]
           /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                           downstreamNRequests, downstreamReceived, 
                           downstreamFinished, queueNRequests, pipeTotal, 
                           pipeNRequested, pipeContents, element_ >>

Send == /\ pc["right"] = "Send"
        /\ pipeContents' = (pipeContents \union {element})
        /\ pc' = [pc EXCEPT !["right"] = "MakeRequestRight"]
        /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                        downstreamNRequests, downstreamReceived, 
                        downstreamFinished, queueNRequests, queueContents, 
                        pipeTotal, pipeNRequested, element_, element >>

right == MakeRequestRight \/ BlockUntilDequeued \/ Dequeue \/ Send

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
\* Last modified Tue Jan 04 00:43:04 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
