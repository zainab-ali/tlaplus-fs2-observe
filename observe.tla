------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences
(* This TLA+ Spec verifies

val pipe = _.take(1)

Stream(1, 2, 3)                        // UPSTREAM
.evalMap(q.enqueue)                    // QUEUE
.concurrently(q.dequeue.through(pipe)) // PIPE
.compile.drain                         // DOWNSTREAM
*)

(* --algorithm observe
variables upstreamPending = <<1, 2, 3>>, \* The elements in the upstream Stream(1, 2, 3)
          upstreamPulled = {}, \* The elements pulled from upstream
          downstreamNRequests = 0, \* The number of elements requested by downstream
          downstreamReceived = {}, \* The elements received by downstream from upstream
          downstreamFinished = FALSE, \* Whether downstream has received a "done" message
          queueNRequests = 0, \* The number of "dequeue" requests made to the queue
          queueContents = {}, \* The elements within the queue.
          pipeContents = {}
define
\* Invariants
(* All elements that have been pulled from upstream were requested by downstream

Given that the value of an element corresponds to its index, this can be translated into:

For all elements in the set of "elements pulled from upstream"
The "number of elements requested from downstream" is greater than or equal to the element
*)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests

\* This is a dummy invariant added for testing
DoneInvariant == ~downstreamFinished
end define
process left = "left"
variable element = FALSE;
begin
  \* While downstream has not finished
  CheckFinished:
    while ~downstreamFinished do
      \* Make a request from downstream to upstream
      MakeRequest:
        downstreamNRequests := downstreamNRequests + 1;
        \* If there is an element upstream
        if Len(upstreamPending) > 0 then
          \* Then pull the element
          element := Head(upstreamPending);
          upstreamPending := Tail(upstreamPending);
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

process right = "right"
variable element = FALSE;
begin 
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
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "1e2abdd" /\ chksum(tla) = "2298e64e")
\* Process variable element of process left at line 37 col 10 changed to element_
VARIABLES upstreamPending, upstreamPulled, downstreamNRequests, 
          downstreamReceived, downstreamFinished, queueNRequests, 
          queueContents, pipeContents, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests


DoneInvariant == ~downstreamFinished

VARIABLES element_, element

vars == << upstreamPending, upstreamPulled, downstreamNRequests, 
           downstreamReceived, downstreamFinished, queueNRequests, 
           queueContents, pipeContents, pc, element_, element >>

ProcSet == {"left"} \cup {"right"}

Init == (* Global variables *)
        /\ upstreamPending = <<1, 2, 3>>
        /\ upstreamPulled = {}
        /\ downstreamNRequests = 0
        /\ downstreamReceived = {}
        /\ downstreamFinished = FALSE
        /\ queueNRequests = 0
        /\ queueContents = {}
        /\ pipeContents = {}
        (* Process left *)
        /\ element_ = FALSE
        (* Process right *)
        /\ element = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "left" -> "CheckFinished"
                                        [] self = "right" -> "BlockUntilDequeued"]

CheckFinished == /\ pc["left"] = "CheckFinished"
                 /\ IF ~downstreamFinished
                       THEN /\ pc' = [pc EXCEPT !["left"] = "MakeRequest"]
                       ELSE /\ pc' = [pc EXCEPT !["left"] = "Done"]
                 /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                 downstreamNRequests, downstreamReceived, 
                                 downstreamFinished, queueNRequests, 
                                 queueContents, pipeContents, element_, 
                                 element >>

MakeRequest == /\ pc["left"] = "MakeRequest"
               /\ downstreamNRequests' = downstreamNRequests + 1
               /\ IF Len(upstreamPending) > 0
                     THEN /\ element_' = Head(upstreamPending)
                          /\ upstreamPending' = Tail(upstreamPending)
                          /\ upstreamPulled' = (upstreamPulled \union {element_'})
                          /\ pc' = [pc EXCEPT !["left"] = "BlockUntilEnqueued"]
                          /\ UNCHANGED downstreamFinished
                     ELSE /\ downstreamFinished' = TRUE
                          /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
                          /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                          element_ >>
               /\ UNCHANGED << downstreamReceived, queueNRequests, 
                               queueContents, pipeContents, element >>

BlockUntilEnqueued == /\ pc["left"] = "BlockUntilEnqueued"
                      /\ queueNRequests = 0
                      /\ pc' = [pc EXCEPT !["left"] = "Enqueue"]
                      /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                      downstreamNRequests, downstreamReceived, 
                                      downstreamFinished, queueNRequests, 
                                      queueContents, pipeContents, element_, 
                                      element >>

Enqueue == /\ pc["left"] = "Enqueue"
           /\ queueNRequests' = queueNRequests -1
           /\ queueContents' = (queueContents \union {element_})
           /\ downstreamReceived' = (downstreamReceived \union {element_})
           /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
           /\ UNCHANGED << upstreamPending, upstreamPulled, 
                           downstreamNRequests, downstreamFinished, 
                           pipeContents, element_, element >>

left == CheckFinished \/ MakeRequest \/ BlockUntilEnqueued \/ Enqueue

BlockUntilDequeued == /\ pc["right"] = "BlockUntilDequeued"
                      /\ queueNRequests' = queueNRequests + 1
                      /\ queueContents /= {}
                      /\ pc' = [pc EXCEPT !["right"] = "Dequeue"]
                      /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                      downstreamNRequests, downstreamReceived, 
                                      downstreamFinished, queueContents, 
                                      pipeContents, element_, element >>

Dequeue == /\ pc["right"] = "Dequeue"
           /\ element' = (CHOOSE x \in queueContents : TRUE)
           /\ queueContents' = queueContents \ { element'}
           /\ pc' = [pc EXCEPT !["right"] = "Send"]
           /\ UNCHANGED << upstreamPending, upstreamPulled, 
                           downstreamNRequests, downstreamReceived, 
                           downstreamFinished, queueNRequests, pipeContents, 
                           element_ >>

Send == /\ pc["right"] = "Send"
        /\ pipeContents' = (pipeContents \union {element})
        /\ pc' = [pc EXCEPT !["right"] = "Done"]
        /\ UNCHANGED << upstreamPending, upstreamPulled, downstreamNRequests, 
                        downstreamReceived, downstreamFinished, queueNRequests, 
                        queueContents, element_, element >>

right == BlockUntilDequeued \/ Dequeue \/ Send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == left \/ right
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Jan 03 22:52:54 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
