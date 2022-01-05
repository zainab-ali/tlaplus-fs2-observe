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
          queueCompleted = FALSE,
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
QueueIsNeverCancelled == ~queueCancelled

\* Constants
QStateRunning == "Running"
QStateCancelled == "Cancelled"
QStateCompleted == "Completed"

ElNull == -1 \* The initial value of a temporary element variable
ElNone == -2 \* Represents a q.close or effectively a Pull.done

end define

macro check_queue_cancelled()
begin
  if state = QStateCancelled then goto Cancelled end if;
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
            if ~queueCompleted then
              queueCancelled := TRUE;
            end if;
        end if;
    end while;
end process;

(*
A process representing the q.dequeue stream. This is able to run on either the left or right side of
a concurrently such that the following code is represented:
 
 q.dequeue.concurrently(right)
 left.concurrently(q.dequeue)

It should have several abilities:
 - It can be cancelled
 - If there is no element in the queue, it registers itself as a listener on the queue

The left and right branches of a concurrently block are treated in different ways. 
This is because the left branch needs to know about the stream it is embedded in (downstream)
while the right branch does not.

We could model this as a CSP-like process, where a request from downstream is submitted into a mailbox.
In the left branch, a request is only submitted when downstream wants one. In the right branch, 
a request is always submitted.

Alternatively, we could assume that this was always connected to a .take(N).compile.drain. This would make it more accurate.
*)
fair process dequeue \in {"dequeue"}
variable \* Global variables
         state = QStateRunning, \* Whether the queue has been completed or cancelled. This is global mutable state.
         requestedN = 0,        \* The number of dequeue requests made. This is a global variable of the queue.
         \* Local variables. We may want to have invariants based on these.
         el = -1,               \* The current element being dequeued. 
         takeN = 0..3,          \* The total number of dequeues to request
         receivedEls = {};      \* The elements that have been dequeued     
begin 
  \* While the pipe has not finished
  Take:
    while requestedN < takeN /\ state = QStateRunning do
      CheckCancellationBeforeRequest: 
        check_queue_cancelled();
      Request:
        \* Make a "dequeue" request 
        requestedN := requestedN + 1;
      \* While there is no element in the queue: loop
      Spin:
        while queueContents = {} do
          CheckCancellationInSpin: 
            check_queue_cancelled();
        end while;
      CheckCancellationBeforeGet:
        check_queue_cancelled();
      Get:
        \* Take the element off the queue
        el := CHOOSE x \in queueContents : TRUE;
        queueContents := queueContents \ {el} ;
      CheckCompletion:
        if el = ElNone then
          goto Completed;
        end if;
      \* Receive it in the pipe
      CheckCancellationBeforeReceive: 
        check_queue_cancelled();
      Receive:
        receivedEls := receivedEls \union {element};
    end while;
  Completed:
     state := QStateCompleted;
  Cancelled:
    skip;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "7efbc0fa" /\ chksum(tla) = "ba710627")
VARIABLES upstreamTotal, upstreamPending, upstreamPulled, downstreamNRequests, 
          downstreamReceived, downstreamFinished, queueNRequests, 
          queueContents, queueCancelled, queueCompleted, pipeTotal, 
          pipeNRequested, pipeContents, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests
QueueIsNeverCancelled == ~queueCancelled


QStateRunning == "Running"
QStateCancelled == "Cancelled"
QStateCompleted == "Completed"

ElNone == -2

VARIABLES element, state, requestedN, el, takeN, receivedEls

vars == << upstreamTotal, upstreamPending, upstreamPulled, 
           downstreamNRequests, downstreamReceived, downstreamFinished, 
           queueNRequests, queueContents, queueCancelled, queueCompleted, 
           pipeTotal, pipeNRequested, pipeContents, pc, element, state, 
           requestedN, el, takeN, receivedEls >>

ProcSet == {"left"} \cup ({"dequeue"})

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
        /\ queueCompleted = FALSE
        /\ pipeTotal \in 0..3
        /\ pipeNRequested = 0
        /\ pipeContents = {}
        (* Process left *)
        /\ element = -8
        (* Process dequeue *)
        /\ state = [self \in {"dequeue"} |-> QStateRunning]
        /\ requestedN = [self \in {"dequeue"} |-> 0]
        /\ el = [self \in {"dequeue"} |-> -1]
        /\ takeN = [self \in {"dequeue"} |-> 0..3]
        /\ receivedEls = [self \in {"dequeue"} |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = "left" -> "CheckFinished"
                                        [] self \in {"dequeue"} -> "Take"]

CheckFinished == /\ pc["left"] = "CheckFinished"
                 /\ IF ~downstreamFinished
                       THEN /\ pc' = [pc EXCEPT !["left"] = "MakeRequestLeft"]
                       ELSE /\ pc' = [pc EXCEPT !["left"] = "Done"]
                 /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                 upstreamPulled, downstreamNRequests, 
                                 downstreamReceived, downstreamFinished, 
                                 queueNRequests, queueContents, queueCancelled, 
                                 queueCompleted, pipeTotal, pipeNRequested, 
                                 pipeContents, element, state, requestedN, el, 
                                 takeN, receivedEls >>

MakeRequestLeft == /\ pc["left"] = "MakeRequestLeft"
                   /\ downstreamNRequests' = downstreamNRequests + 1
                   /\ IF upstreamPending > 0
                         THEN /\ element' = upstreamTotal - upstreamPending + 1
                              /\ upstreamPending' = upstreamPending - 1
                              /\ upstreamPulled' = (upstreamPulled \union {element'})
                              /\ pc' = [pc EXCEPT !["left"] = "BlockUntilEnqueued"]
                         ELSE /\ pc' = [pc EXCEPT !["left"] = "CompleteLeft"]
                              /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                              element >>
                   /\ UNCHANGED << upstreamTotal, downstreamReceived, 
                                   downstreamFinished, queueNRequests, 
                                   queueContents, queueCancelled, 
                                   queueCompleted, pipeTotal, pipeNRequested, 
                                   pipeContents, state, requestedN, el, takeN, 
                                   receivedEls >>

BlockUntilEnqueued == /\ pc["left"] = "BlockUntilEnqueued"
                      /\ queueNRequests > 0
                      /\ pc' = [pc EXCEPT !["left"] = "Enqueue"]
                      /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                      upstreamPulled, downstreamNRequests, 
                                      downstreamReceived, downstreamFinished, 
                                      queueNRequests, queueContents, 
                                      queueCancelled, queueCompleted, 
                                      pipeTotal, pipeNRequested, pipeContents, 
                                      element, state, requestedN, el, takeN, 
                                      receivedEls >>

Enqueue == /\ pc["left"] = "Enqueue"
           /\ queueNRequests' = queueNRequests -1
           /\ queueContents' = (queueContents \union {element})
           /\ downstreamReceived' = (downstreamReceived \union {element})
           /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
           /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                           downstreamNRequests, downstreamFinished, 
                           queueCancelled, queueCompleted, pipeTotal, 
                           pipeNRequested, pipeContents, element, state, 
                           requestedN, el, takeN, receivedEls >>

CompleteLeft == /\ pc["left"] = "CompleteLeft"
                /\ downstreamFinished' = TRUE
                /\ IF ~queueCompleted
                      THEN /\ queueCancelled' = TRUE
                      ELSE /\ TRUE
                           /\ UNCHANGED queueCancelled
                /\ pc' = [pc EXCEPT !["left"] = "CheckFinished"]
                /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                                downstreamNRequests, downstreamReceived, 
                                queueNRequests, queueContents, queueCompleted, 
                                pipeTotal, pipeNRequested, pipeContents, 
                                element, state, requestedN, el, takeN, 
                                receivedEls >>

left == CheckFinished \/ MakeRequestLeft \/ BlockUntilEnqueued \/ Enqueue
           \/ CompleteLeft

Take(self) == /\ pc[self] = "Take"
              /\ IF requestedN[self] < takeN[self] /\ state[self] = QStateRunning
                    THEN /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeRequest"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Completed"]
              /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                              downstreamNRequests, downstreamReceived, 
                              downstreamFinished, queueNRequests, 
                              queueContents, queueCancelled, queueCompleted, 
                              pipeTotal, pipeNRequested, pipeContents, element, 
                              state, requestedN, el, takeN, receivedEls >>

CheckCancellationBeforeRequest(self) == /\ pc[self] = "CheckCancellationBeforeRequest"
                                        /\ IF state[self] = QStateCancelled
                                              THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "Request"]
                                        /\ UNCHANGED << upstreamTotal, 
                                                        upstreamPending, 
                                                        upstreamPulled, 
                                                        downstreamNRequests, 
                                                        downstreamReceived, 
                                                        downstreamFinished, 
                                                        queueNRequests, 
                                                        queueContents, 
                                                        queueCancelled, 
                                                        queueCompleted, 
                                                        pipeTotal, 
                                                        pipeNRequested, 
                                                        pipeContents, element, 
                                                        state, requestedN, el, 
                                                        takeN, receivedEls >>

Request(self) == /\ pc[self] = "Request"
                 /\ requestedN' = [requestedN EXCEPT ![self] = requestedN[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "Spin"]
                 /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                 upstreamPulled, downstreamNRequests, 
                                 downstreamReceived, downstreamFinished, 
                                 queueNRequests, queueContents, queueCancelled, 
                                 queueCompleted, pipeTotal, pipeNRequested, 
                                 pipeContents, element, state, el, takeN, 
                                 receivedEls >>

Spin(self) == /\ pc[self] = "Spin"
              /\ IF queueContents = {}
                    THEN /\ pc' = [pc EXCEPT ![self] = "CheckCancellationInSpin"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeGet"]
              /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                              downstreamNRequests, downstreamReceived, 
                              downstreamFinished, queueNRequests, 
                              queueContents, queueCancelled, queueCompleted, 
                              pipeTotal, pipeNRequested, pipeContents, element, 
                              state, requestedN, el, takeN, receivedEls >>

CheckCancellationInSpin(self) == /\ pc[self] = "CheckCancellationInSpin"
                                 /\ IF state[self] = QStateCancelled
                                       THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Spin"]
                                 /\ UNCHANGED << upstreamTotal, 
                                                 upstreamPending, 
                                                 upstreamPulled, 
                                                 downstreamNRequests, 
                                                 downstreamReceived, 
                                                 downstreamFinished, 
                                                 queueNRequests, queueContents, 
                                                 queueCancelled, 
                                                 queueCompleted, pipeTotal, 
                                                 pipeNRequested, pipeContents, 
                                                 element, state, requestedN, 
                                                 el, takeN, receivedEls >>

CheckCancellationBeforeGet(self) == /\ pc[self] = "CheckCancellationBeforeGet"
                                    /\ IF state[self] = QStateCancelled
                                          THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "Get"]
                                    /\ UNCHANGED << upstreamTotal, 
                                                    upstreamPending, 
                                                    upstreamPulled, 
                                                    downstreamNRequests, 
                                                    downstreamReceived, 
                                                    downstreamFinished, 
                                                    queueNRequests, 
                                                    queueContents, 
                                                    queueCancelled, 
                                                    queueCompleted, pipeTotal, 
                                                    pipeNRequested, 
                                                    pipeContents, element, 
                                                    state, requestedN, el, 
                                                    takeN, receivedEls >>

Get(self) == /\ pc[self] = "Get"
             /\ el' = [el EXCEPT ![self] = CHOOSE x \in queueContents : TRUE]
             /\ queueContents' = queueContents \ {el'[self]}
             /\ pc' = [pc EXCEPT ![self] = "CheckCompletion"]
             /\ UNCHANGED << upstreamTotal, upstreamPending, upstreamPulled, 
                             downstreamNRequests, downstreamReceived, 
                             downstreamFinished, queueNRequests, 
                             queueCancelled, queueCompleted, pipeTotal, 
                             pipeNRequested, pipeContents, element, state, 
                             requestedN, takeN, receivedEls >>

CheckCompletion(self) == /\ pc[self] = "CheckCompletion"
                         /\ IF el[self] = ElNone
                               THEN /\ pc' = [pc EXCEPT ![self] = "Completed"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeReceive"]
                         /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                         upstreamPulled, downstreamNRequests, 
                                         downstreamReceived, 
                                         downstreamFinished, queueNRequests, 
                                         queueContents, queueCancelled, 
                                         queueCompleted, pipeTotal, 
                                         pipeNRequested, pipeContents, element, 
                                         state, requestedN, el, takeN, 
                                         receivedEls >>

CheckCancellationBeforeReceive(self) == /\ pc[self] = "CheckCancellationBeforeReceive"
                                        /\ IF state[self] = QStateCancelled
                                              THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "Receive"]
                                        /\ UNCHANGED << upstreamTotal, 
                                                        upstreamPending, 
                                                        upstreamPulled, 
                                                        downstreamNRequests, 
                                                        downstreamReceived, 
                                                        downstreamFinished, 
                                                        queueNRequests, 
                                                        queueContents, 
                                                        queueCancelled, 
                                                        queueCompleted, 
                                                        pipeTotal, 
                                                        pipeNRequested, 
                                                        pipeContents, element, 
                                                        state, requestedN, el, 
                                                        takeN, receivedEls >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ receivedEls' = [receivedEls EXCEPT ![self] = receivedEls[self] \union {element}]
                 /\ pc' = [pc EXCEPT ![self] = "Take"]
                 /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                 upstreamPulled, downstreamNRequests, 
                                 downstreamReceived, downstreamFinished, 
                                 queueNRequests, queueContents, queueCancelled, 
                                 queueCompleted, pipeTotal, pipeNRequested, 
                                 pipeContents, element, state, requestedN, el, 
                                 takeN >>

Completed(self) == /\ pc[self] = "Completed"
                   /\ state' = [state EXCEPT ![self] = QStateCompleted]
                   /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                   /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                   upstreamPulled, downstreamNRequests, 
                                   downstreamReceived, downstreamFinished, 
                                   queueNRequests, queueContents, 
                                   queueCancelled, queueCompleted, pipeTotal, 
                                   pipeNRequested, pipeContents, element, 
                                   requestedN, el, takeN, receivedEls >>

Cancelled(self) == /\ pc[self] = "Cancelled"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << upstreamTotal, upstreamPending, 
                                   upstreamPulled, downstreamNRequests, 
                                   downstreamReceived, downstreamFinished, 
                                   queueNRequests, queueContents, 
                                   queueCancelled, queueCompleted, pipeTotal, 
                                   pipeNRequested, pipeContents, element, 
                                   state, requestedN, el, takeN, receivedEls >>

dequeue(self) == Take(self) \/ CheckCancellationBeforeRequest(self)
                    \/ Request(self) \/ Spin(self)
                    \/ CheckCancellationInSpin(self)
                    \/ CheckCancellationBeforeGet(self) \/ Get(self)
                    \/ CheckCompletion(self)
                    \/ CheckCancellationBeforeReceive(self)
                    \/ Receive(self) \/ Completed(self) \/ Cancelled(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == left
           \/ (\E self \in {"dequeue"}: dequeue(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(left)
        /\ \A self \in {"dequeue"} : WF_vars(dequeue(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Jan 05 19:04:08 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
