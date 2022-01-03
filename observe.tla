------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences
(* This TLA+ Spec verifies

Stream(1, 2, 3)     // UPSTREAM
.evalMap(q.enqueue) // QUEUE
.compile.drain      // DOWNSTREAM
*)

\* Constants
DequeueRequest == "dequeue"


(* --algorithm observe
variables upstreamPending = <<1, 2, 3>>, \* The elements in the upstream Stream(1, 2, 3)
          upstreamPulled = {}, \* The elements pulled from upstream
          downstreamNRequests = 0, \* The number of elements requested by downstream
          downstreamReceived = {}, \* The elements received by downstream from upstream
          downstreamFinished = FALSE, \* Whether downstream has received a "done" message
          queueRequests = {}, \* The "dequeue" and "enqueue" requests made to the queue
          queueContents = {}, \* The elements within the queue.
          \* Temporary variables
          element = FALSE;
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
begin
  \* While downstream has not finished
  CheckFinished: while ~downstreamFinished do
    \* Make a request from downstream to upstream
    MakeRequest: downstreamNRequests := downstreamNRequests + 1;
    \* If there is an element upstream
    if Len(upstreamPending) > 0 then 
      \* Then pull the element
      element := Head(upstreamPending);
      upstreamPending := Tail(upstreamPending);
      upstreamPulled := upstreamPulled \union {element};
      \* While the queue has not received a dequeue request
      Loop: while DequeueRequest \notin queueRequests do
        \* block
        skip;
      end while;
      \* Then remove the "dequeue" request
      queueRequests := queueRequests \ {DequeueRequest};
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
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "cff49e2d" /\ chksum(tla) = "e66fd1ab")
VARIABLES upstreamPending, upstreamPulled, downstreamNRequests, 
          downstreamReceived, downstreamFinished, queueRequests, 
          queueContents, element, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests


DoneInvariant == ~downstreamFinished


vars == << upstreamPending, upstreamPulled, downstreamNRequests, 
           downstreamReceived, downstreamFinished, queueRequests, 
           queueContents, element, pc >>

Init == (* Global variables *)
        /\ upstreamPending = <<1, 2, 3>>
        /\ upstreamPulled = {}
        /\ downstreamNRequests = 0
        /\ downstreamReceived = {}
        /\ downstreamFinished = FALSE
        /\ queueRequests = {}
        /\ queueContents = {}
        /\ element = FALSE
        /\ pc = "CheckFinished"

CheckFinished == /\ pc = "CheckFinished"
                 /\ IF ~downstreamFinished
                       THEN /\ pc' = "MakeRequest"
                       ELSE /\ pc' = "Done"
                 /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                 downstreamNRequests, downstreamReceived, 
                                 downstreamFinished, queueRequests, 
                                 queueContents, element >>

MakeRequest == /\ pc = "MakeRequest"
               /\ downstreamNRequests' = downstreamNRequests + 1
               /\ IF Len(upstreamPending) > 0
                     THEN /\ element' = Head(upstreamPending)
                          /\ upstreamPending' = Tail(upstreamPending)
                          /\ upstreamPulled' = (upstreamPulled \union {element'})
                          /\ pc' = "Loop"
                          /\ UNCHANGED downstreamFinished
                     ELSE /\ downstreamFinished' = TRUE
                          /\ pc' = "CheckFinished"
                          /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                          element >>
               /\ UNCHANGED << downstreamReceived, queueRequests, 
                               queueContents >>

Loop == /\ pc = "Loop"
        /\ IF DequeueRequest \notin queueRequests
              THEN /\ TRUE
                   /\ pc' = "Loop"
                   /\ UNCHANGED << downstreamReceived, queueRequests, 
                                   queueContents >>
              ELSE /\ queueRequests' = queueRequests \ {DequeueRequest}
                   /\ queueContents' = (queueContents \union {element})
                   /\ downstreamReceived' = (downstreamReceived \union {element})
                   /\ pc' = "CheckFinished"
        /\ UNCHANGED << upstreamPending, upstreamPulled, downstreamNRequests, 
                        downstreamFinished, element >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CheckFinished \/ MakeRequest \/ Loop
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Jan 03 20:13:55 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
