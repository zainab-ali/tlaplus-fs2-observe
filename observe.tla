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

CONSTANTS Q_STATES,
          QStateCompleted,
          QStateErrored,
          QStateCancelled,
          QStateRunning,
          UPSTREAM_N, \* The number of elements upstream.
          UPSTREAM_ERROR_N, \* The index of the error upstream, if any
          DOWNSTREAM_TAKE_N, \* The number of elements to be requested from downstream
          OBSERVER_TAKE_N, \* The number of elements to be requested by the observer stream
          NULL,
          NONE,         \* Represents a q.close or effectively a Pull.done
          ERROR         \* Represents an error in a stream 
ASSUME UPSTREAM_N >= 0
ASSUME DOWNSTREAM_TAKE_N >= 0
ASSUME OBSERVER_TAKE_N >= 0

\* Constants
ConcurrentLeft == "dequeue"  \* The label of the process on the left side of 'concurrently'
ConcurrentRight == "enqueue" \* The label on the right side

(* --algorithm observe
variables 
          upstreamEls = {}, \* The elements pulled from upstream
          observerTakeN \in 0..OBSERVER_TAKE_N, 
          upstreamN \in 0..UPSTREAM_N, \* The total number of elements upstream
          downstreamTakeN \in 0..DOWNSTREAM_TAKE_N,              \* The total number of dequeues to request  
          queueContents = {}, \* The elements within the queue.
          streams = [ 
            enqueue |-> [
              state |-> QStateRunning,
              requestedN |-> 0,         \* The number of elements requested by this stream
              receivedEls |-> {}        \* The elements sent downstream by this stream
              ],
            dequeue |-> [
              state |-> QStateRunning,
              requestedN |-> 0,
              receivedEls |-> {}
              ]
            ]
define
\* Invariants
(* All elements that have been pulled from upstream were requested by downstream

Given that the value of an element corresponds to its index, this can be translated into:

For all elements in the set of "elements pulled from upstream"
The "number of elements requested from downstream" is greater than or equal to the element
*)
PulledRequestedInvariant == \A e \in upstreamEls : e <= streams["dequeue"].requestedN

\* TODO: Explain this
QueueIsNeverCancelled == streams["enqueue"].state /= QStateCancelled

(* If the observer requests the same number of elements as downstream, 
   then both streams should receive the same set of elements.   
*)
EventuallyReceiveSameElements == observerTakeN = downstreamTakeN => <>(streams["enqueue"].requestedEls = streams["dequeue"].requestedEls)
(* If the background process errors then the foreground will eventually error *)
EventuallyBothError == streams["enqueue"].state = QStateErrored ~> streams["dequeue"].state = QStateErrored

UpstreamPending == [ n \in 1..UPSTREAM_N |-> IF n = UPSTREAM_ERROR_N THEN ERROR ELSE n ]


end define

\* TODO: Parameterize this on the name of the process / stream
macro check_cancelled()
begin
  if streams["dequeue"].state = QStateCancelled then goto Cancelled end if;
end macro;

fair process concurrent \in {"concurrent"}
begin
  Loop:
    while streams[ConcurrentLeft].state = QStateRunning /\ streams[ConcurrentRight].state = QStateRunning do
      CheckLeftCompleted:
        if streams[ConcurrentLeft].state = QStateCompleted /\ streams[ConcurrentRight].state = QStateRunning then
          streams[ConcurrentRight].state := QStateCancelled; 
        elsif streams[ConcurrentRight].state = QStateErrored then
          \* If there is an error in the right stream, propagate it to the left stream
          \* Note that this isn't exactly how 'concurrently' behaves, but we'd need to model the concept of scopes
          \* to spec out its actual behaviour
          streams[ConcurrentLeft].state := QStateErrored; 
        end if
    end while;
end process;

fair process enqueue \in {"enqueue"}
variable 
         el = NULL, 
         takeN = observerTakeN, 
         upstreamPending = UpstreamPending, \* The elements to be pulled from upstream
         enqueuedN = 0;
begin
  \* While downstream has not finished
  CheckFinished:
    while streams["enqueue"].requestedN < takeN /\ streams["enqueue"].state = QStateRunning do
      CheckCancellationBeforeRequest: 
        check_cancelled();
      \* Make a request from downstream to upstream
      Request:
        streams["enqueue"].requestedN := streams["enqueue"].requestedN + 1;
        \* If there is an element upstream
        if Len(upstreamPending) > 0 then
          \* Then pull the element
          \* This is a 1-indexed sequence
          el := Head(upstreamPending);
          upstreamPending := Tail(upstreamPending);
          upstreamEls := upstreamEls \union {el};
          \* If there is an error upstream
          CheckUpstreamError:
            if el = ERROR then
              streams["enqueue"].state := QStateErrored;
              goto Errored;
            end if;
          \* While the queue has not received a dequeue request
          Spin:
            while streams["dequeue"].requestedN <= enqueuedN do
              CheckCancellationInSpin: 
                check_cancelled();
            end while;
          CheckCancellationBeforePut:
            check_cancelled();
          Put:
            \* Then count the "enqueued" element
            enqueuedN := enqueuedN + 1;
            \* And enqueue the element
            queueContents := queueContents \union {el};
          CheckCancellationBeforeSend:
            check_cancelled();
          Send:          
            \* And deliver the element downstream
            streams["enqueue"].receivedEls := streams["enqueue"].receivedEls \union {el};
        else
          \* Else deliver "done" downstream
          SpinComplete:
            while streams["dequeue"].requestedN <= enqueuedN do
              CheckCancellationInSpinComplete:
                check_cancelled();
            end while;
          CheckCancellationBeforePutComplete:
            check_cancelled();
          PutComplete:
            \* Then count the "enqueued" element
            enqueuedN := enqueuedN + 1;
            \* And enqueue the element
            queueContents := queueContents \union {NONE};
          goto Complete;
        end if;
    end while;
    Complete:
      streams["enqueue"].state := QStateCompleted;
    Cancelled:
      skip;
    Errored:
      skip;
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
variable 
         el = NULL,               \* The current element being dequeued. 
         takeN = downstreamTakeN,              \* The total number of dequeues to request
begin 
  \* While the pipe has not finished
  Take:
    while streams["dequeue"].requestedN < takeN /\ streams["dequeue"].state = QStateRunning do
      CheckCancellationBeforeRequest: 
        check_cancelled();
      Request:
        \* Make a "dequeue" request 
        streams["dequeue"].requestedN := streams["dequeue"].requestedN + 1;
      \* While there is no element in the queue: loop
      Spin:
        while queueContents = {} do
          CheckCancellationInSpin: 
            check_cancelled();
        end while;
      CheckCancellationBeforeGet:
        check_cancelled();
      Get:
        \* Take the element off the queue
        el := CHOOSE x \in queueContents : TRUE;
        queueContents := queueContents \ {el} ;
      CheckCompletion:
        if el = NONE then
          goto Completed;
        end if;
      \* Receive it in the pipe
      CheckCancellationBeforeReceive: 
        check_cancelled();
      Receive:
        streams["dequeue"].receivedEls := streams["dequeue"].receivedEls \union {el };
    end while;
  Completed:
     streams["dequeue"].state := QStateCompleted;
  Cancelled:
    skip;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "cf5e6cb8" /\ chksum(tla) = "b17c18bf")
\* Label CheckCancellationBeforeRequest of process enqueue at line 93 col 3 changed to CheckCancellationBeforeRequest_
\* Label Request of process enqueue at line 126 col 9 changed to Request_
\* Label Spin of process enqueue at line 142 col 13 changed to Spin_
\* Label CheckCancellationInSpin of process enqueue at line 93 col 3 changed to CheckCancellationInSpin_
\* Label Cancelled of process enqueue at line 178 col 7 changed to Cancelled_
\* Process variable el of process enqueue at line 114 col 10 changed to el_
\* Process variable takeN of process enqueue at line 115 col 10 changed to takeN_
VARIABLES upstreamEls, observerTakeN, upstreamN, downstreamTakeN, 
          queueContents, streams, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamEls : e <= streams["dequeue"].requestedN


QueueIsNeverCancelled == streams["enqueue"].state /= QStateCancelled




EventuallyReceiveSameElements == observerTakeN = downstreamTakeN => <>(streams["enqueue"].requestedEls = streams["dequeue"].requestedEls)

EventuallyBothError == streams["enqueue"].state = QStateErrored ~> streams["dequeue"].state = QStateErrored

UpstreamPending == [ n \in 1..UPSTREAM_N |-> IF n = UPSTREAM_ERROR_N THEN ERROR ELSE n ]

VARIABLES el_, takeN_, upstreamPending, enqueuedN, el, takeN

vars == << upstreamEls, observerTakeN, upstreamN, downstreamTakeN, 
           queueContents, streams, pc, el_, takeN_, upstreamPending, 
           enqueuedN, el, takeN >>

ProcSet == ({"concurrent"}) \cup ({"enqueue"}) \cup ({"dequeue"})

Init == (* Global variables *)
        /\ upstreamEls = {}
        /\ observerTakeN \in 0..OBSERVER_TAKE_N
        /\ upstreamN \in 0..UPSTREAM_N
        /\ downstreamTakeN \in 0..DOWNSTREAM_TAKE_N
        /\ queueContents = {}
        /\ streams =         [
                     enqueue |-> [
                       state |-> QStateRunning,
                       requestedN |-> 0,
                       receivedEls |-> {}
                       ],
                     dequeue |-> [
                       state |-> QStateRunning,
                       requestedN |-> 0,
                       receivedEls |-> {}
                       ]
                     ]
        (* Process enqueue *)
        /\ el_ = [self \in {"enqueue"} |-> NULL]
        /\ takeN_ = [self \in {"enqueue"} |-> observerTakeN]
        /\ upstreamPending = [self \in {"enqueue"} |-> UpstreamPending]
        /\ enqueuedN = [self \in {"enqueue"} |-> 0]
        (* Process dequeue *)
        /\ el = [self \in {"dequeue"} |-> NULL]
        /\ takeN = [self \in {"dequeue"} |-> downstreamTakeN]
        /\ pc = [self \in ProcSet |-> CASE self \in {"concurrent"} -> "Loop"
                                        [] self \in {"enqueue"} -> "CheckFinished"
                                        [] self \in {"dequeue"} -> "Take"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF streams[ConcurrentLeft].state = QStateRunning /\ streams[ConcurrentRight].state = QStateRunning
                    THEN /\ pc' = [pc EXCEPT ![self] = "CheckLeftCompleted"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                              downstreamTakeN, queueContents, streams, el_, 
                              takeN_, upstreamPending, enqueuedN, el, takeN >>

CheckLeftCompleted(self) == /\ pc[self] = "CheckLeftCompleted"
                            /\ IF streams[ConcurrentLeft].state = QStateCompleted /\ streams[ConcurrentRight].state = QStateRunning
                                  THEN /\ streams' = [streams EXCEPT ![ConcurrentRight].state = QStateCancelled]
                                  ELSE /\ IF streams[ConcurrentRight].state = QStateErrored
                                             THEN /\ streams' = [streams EXCEPT ![ConcurrentLeft].state = QStateErrored]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED streams
                            /\ pc' = [pc EXCEPT ![self] = "Loop"]
                            /\ UNCHANGED << upstreamEls, observerTakeN, 
                                            upstreamN, downstreamTakeN, 
                                            queueContents, el_, takeN_, 
                                            upstreamPending, enqueuedN, el, 
                                            takeN >>

concurrent(self) == Loop(self) \/ CheckLeftCompleted(self)

CheckFinished(self) == /\ pc[self] = "CheckFinished"
                       /\ IF streams["enqueue"].requestedN < takeN_[self] /\ streams["enqueue"].state = QStateRunning
                             THEN /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeRequest_"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Complete"]
                       /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                       downstreamTakeN, queueContents, streams, 
                                       el_, takeN_, upstreamPending, enqueuedN, 
                                       el, takeN >>

CheckCancellationBeforeRequest_(self) == /\ pc[self] = "CheckCancellationBeforeRequest_"
                                         /\ IF streams["dequeue"].state = QStateCancelled
                                               THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled_"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "Request_"]
                                         /\ UNCHANGED << upstreamEls, 
                                                         observerTakeN, 
                                                         upstreamN, 
                                                         downstreamTakeN, 
                                                         queueContents, 
                                                         streams, el_, takeN_, 
                                                         upstreamPending, 
                                                         enqueuedN, el, takeN >>

Request_(self) == /\ pc[self] = "Request_"
                  /\ streams' = [streams EXCEPT !["enqueue"].requestedN = streams["enqueue"].requestedN + 1]
                  /\ IF Len(upstreamPending[self]) > 0
                        THEN /\ el_' = [el_ EXCEPT ![self] = Head(upstreamPending[self])]
                             /\ upstreamPending' = [upstreamPending EXCEPT ![self] = Tail(upstreamPending[self])]
                             /\ upstreamEls' = (upstreamEls \union {el_'[self]})
                             /\ pc' = [pc EXCEPT ![self] = "CheckUpstreamError"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "SpinComplete"]
                             /\ UNCHANGED << upstreamEls, el_, upstreamPending >>
                  /\ UNCHANGED << observerTakeN, upstreamN, downstreamTakeN, 
                                  queueContents, takeN_, enqueuedN, el, takeN >>

CheckUpstreamError(self) == /\ pc[self] = "CheckUpstreamError"
                            /\ IF el_[self] = ERROR
                                  THEN /\ streams' = [streams EXCEPT !["enqueue"].state = QStateErrored]
                                       /\ pc' = [pc EXCEPT ![self] = "Errored"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "Spin_"]
                                       /\ UNCHANGED streams
                            /\ UNCHANGED << upstreamEls, observerTakeN, 
                                            upstreamN, downstreamTakeN, 
                                            queueContents, el_, takeN_, 
                                            upstreamPending, enqueuedN, el, 
                                            takeN >>

Spin_(self) == /\ pc[self] = "Spin_"
               /\ IF streams["dequeue"].requestedN <= enqueuedN[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "CheckCancellationInSpin_"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforePut"]
               /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                               downstreamTakeN, queueContents, streams, el_, 
                               takeN_, upstreamPending, enqueuedN, el, takeN >>

CheckCancellationInSpin_(self) == /\ pc[self] = "CheckCancellationInSpin_"
                                  /\ IF streams["dequeue"].state = QStateCancelled
                                        THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled_"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "Spin_"]
                                  /\ UNCHANGED << upstreamEls, observerTakeN, 
                                                  upstreamN, downstreamTakeN, 
                                                  queueContents, streams, el_, 
                                                  takeN_, upstreamPending, 
                                                  enqueuedN, el, takeN >>

CheckCancellationBeforePut(self) == /\ pc[self] = "CheckCancellationBeforePut"
                                    /\ IF streams["dequeue"].state = QStateCancelled
                                          THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled_"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "Put"]
                                    /\ UNCHANGED << upstreamEls, observerTakeN, 
                                                    upstreamN, downstreamTakeN, 
                                                    queueContents, streams, 
                                                    el_, takeN_, 
                                                    upstreamPending, enqueuedN, 
                                                    el, takeN >>

Put(self) == /\ pc[self] = "Put"
             /\ enqueuedN' = [enqueuedN EXCEPT ![self] = enqueuedN[self] + 1]
             /\ queueContents' = (queueContents \union {el_[self]})
             /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeSend"]
             /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                             downstreamTakeN, streams, el_, takeN_, 
                             upstreamPending, el, takeN >>

CheckCancellationBeforeSend(self) == /\ pc[self] = "CheckCancellationBeforeSend"
                                     /\ IF streams["dequeue"].state = QStateCancelled
                                           THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled_"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "Send"]
                                     /\ UNCHANGED << upstreamEls, 
                                                     observerTakeN, upstreamN, 
                                                     downstreamTakeN, 
                                                     queueContents, streams, 
                                                     el_, takeN_, 
                                                     upstreamPending, 
                                                     enqueuedN, el, takeN >>

Send(self) == /\ pc[self] = "Send"
              /\ streams' = [streams EXCEPT !["enqueue"].receivedEls = streams["enqueue"].receivedEls \union {el_[self]}]
              /\ pc' = [pc EXCEPT ![self] = "CheckFinished"]
              /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                              downstreamTakeN, queueContents, el_, takeN_, 
                              upstreamPending, enqueuedN, el, takeN >>

SpinComplete(self) == /\ pc[self] = "SpinComplete"
                      /\ IF streams["dequeue"].requestedN <= enqueuedN[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "CheckCancellationInSpinComplete"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforePutComplete"]
                      /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                      downstreamTakeN, queueContents, streams, 
                                      el_, takeN_, upstreamPending, enqueuedN, 
                                      el, takeN >>

CheckCancellationInSpinComplete(self) == /\ pc[self] = "CheckCancellationInSpinComplete"
                                         /\ IF streams["dequeue"].state = QStateCancelled
                                               THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled_"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "SpinComplete"]
                                         /\ UNCHANGED << upstreamEls, 
                                                         observerTakeN, 
                                                         upstreamN, 
                                                         downstreamTakeN, 
                                                         queueContents, 
                                                         streams, el_, takeN_, 
                                                         upstreamPending, 
                                                         enqueuedN, el, takeN >>

CheckCancellationBeforePutComplete(self) == /\ pc[self] = "CheckCancellationBeforePutComplete"
                                            /\ IF streams["dequeue"].state = QStateCancelled
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled_"]
                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "PutComplete"]
                                            /\ UNCHANGED << upstreamEls, 
                                                            observerTakeN, 
                                                            upstreamN, 
                                                            downstreamTakeN, 
                                                            queueContents, 
                                                            streams, el_, 
                                                            takeN_, 
                                                            upstreamPending, 
                                                            enqueuedN, el, 
                                                            takeN >>

PutComplete(self) == /\ pc[self] = "PutComplete"
                     /\ enqueuedN' = [enqueuedN EXCEPT ![self] = enqueuedN[self] + 1]
                     /\ queueContents' = (queueContents \union {NONE})
                     /\ pc' = [pc EXCEPT ![self] = "Complete"]
                     /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                     downstreamTakeN, streams, el_, takeN_, 
                                     upstreamPending, el, takeN >>

Complete(self) == /\ pc[self] = "Complete"
                  /\ streams' = [streams EXCEPT !["enqueue"].state = QStateCompleted]
                  /\ pc' = [pc EXCEPT ![self] = "Cancelled_"]
                  /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                  downstreamTakeN, queueContents, el_, takeN_, 
                                  upstreamPending, enqueuedN, el, takeN >>

Cancelled_(self) == /\ pc[self] = "Cancelled_"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Errored"]
                    /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                    downstreamTakeN, queueContents, streams, 
                                    el_, takeN_, upstreamPending, enqueuedN, 
                                    el, takeN >>

Errored(self) == /\ pc[self] = "Errored"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                 downstreamTakeN, queueContents, streams, el_, 
                                 takeN_, upstreamPending, enqueuedN, el, takeN >>

enqueue(self) == CheckFinished(self)
                    \/ CheckCancellationBeforeRequest_(self)
                    \/ Request_(self) \/ CheckUpstreamError(self)
                    \/ Spin_(self) \/ CheckCancellationInSpin_(self)
                    \/ CheckCancellationBeforePut(self) \/ Put(self)
                    \/ CheckCancellationBeforeSend(self) \/ Send(self)
                    \/ SpinComplete(self)
                    \/ CheckCancellationInSpinComplete(self)
                    \/ CheckCancellationBeforePutComplete(self)
                    \/ PutComplete(self) \/ Complete(self)
                    \/ Cancelled_(self) \/ Errored(self)

Take(self) == /\ pc[self] = "Take"
              /\ IF streams["dequeue"].requestedN < takeN[self] /\ streams["dequeue"].state = QStateRunning
                    THEN /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeRequest"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Completed"]
              /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                              downstreamTakeN, queueContents, streams, el_, 
                              takeN_, upstreamPending, enqueuedN, el, takeN >>

CheckCancellationBeforeRequest(self) == /\ pc[self] = "CheckCancellationBeforeRequest"
                                        /\ IF streams["dequeue"].state = QStateCancelled
                                              THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "Request"]
                                        /\ UNCHANGED << upstreamEls, 
                                                        observerTakeN, 
                                                        upstreamN, 
                                                        downstreamTakeN, 
                                                        queueContents, streams, 
                                                        el_, takeN_, 
                                                        upstreamPending, 
                                                        enqueuedN, el, takeN >>

Request(self) == /\ pc[self] = "Request"
                 /\ streams' = [streams EXCEPT !["dequeue"].requestedN = streams["dequeue"].requestedN + 1]
                 /\ pc' = [pc EXCEPT ![self] = "Spin"]
                 /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                 downstreamTakeN, queueContents, el_, takeN_, 
                                 upstreamPending, enqueuedN, el, takeN >>

Spin(self) == /\ pc[self] = "Spin"
              /\ IF queueContents = {}
                    THEN /\ pc' = [pc EXCEPT ![self] = "CheckCancellationInSpin"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeGet"]
              /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                              downstreamTakeN, queueContents, streams, el_, 
                              takeN_, upstreamPending, enqueuedN, el, takeN >>

CheckCancellationInSpin(self) == /\ pc[self] = "CheckCancellationInSpin"
                                 /\ IF streams["dequeue"].state = QStateCancelled
                                       THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Spin"]
                                 /\ UNCHANGED << upstreamEls, observerTakeN, 
                                                 upstreamN, downstreamTakeN, 
                                                 queueContents, streams, el_, 
                                                 takeN_, upstreamPending, 
                                                 enqueuedN, el, takeN >>

CheckCancellationBeforeGet(self) == /\ pc[self] = "CheckCancellationBeforeGet"
                                    /\ IF streams["dequeue"].state = QStateCancelled
                                          THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "Get"]
                                    /\ UNCHANGED << upstreamEls, observerTakeN, 
                                                    upstreamN, downstreamTakeN, 
                                                    queueContents, streams, 
                                                    el_, takeN_, 
                                                    upstreamPending, enqueuedN, 
                                                    el, takeN >>

Get(self) == /\ pc[self] = "Get"
             /\ el' = [el EXCEPT ![self] = CHOOSE x \in queueContents : TRUE]
             /\ queueContents' = queueContents \ {el'[self]}
             /\ pc' = [pc EXCEPT ![self] = "CheckCompletion"]
             /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                             downstreamTakeN, streams, el_, takeN_, 
                             upstreamPending, enqueuedN, takeN >>

CheckCompletion(self) == /\ pc[self] = "CheckCompletion"
                         /\ IF el[self] = NONE
                               THEN /\ pc' = [pc EXCEPT ![self] = "Completed"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "CheckCancellationBeforeReceive"]
                         /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                         downstreamTakeN, queueContents, 
                                         streams, el_, takeN_, upstreamPending, 
                                         enqueuedN, el, takeN >>

CheckCancellationBeforeReceive(self) == /\ pc[self] = "CheckCancellationBeforeReceive"
                                        /\ IF streams["dequeue"].state = QStateCancelled
                                              THEN /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "Receive"]
                                        /\ UNCHANGED << upstreamEls, 
                                                        observerTakeN, 
                                                        upstreamN, 
                                                        downstreamTakeN, 
                                                        queueContents, streams, 
                                                        el_, takeN_, 
                                                        upstreamPending, 
                                                        enqueuedN, el, takeN >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ streams' = [streams EXCEPT !["dequeue"].receivedEls = streams["dequeue"].receivedEls \union {el[self] }]
                 /\ pc' = [pc EXCEPT ![self] = "Take"]
                 /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                 downstreamTakeN, queueContents, el_, takeN_, 
                                 upstreamPending, enqueuedN, el, takeN >>

Completed(self) == /\ pc[self] = "Completed"
                   /\ streams' = [streams EXCEPT !["dequeue"].state = QStateCompleted]
                   /\ pc' = [pc EXCEPT ![self] = "Cancelled"]
                   /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                   downstreamTakeN, queueContents, el_, takeN_, 
                                   upstreamPending, enqueuedN, el, takeN >>

Cancelled(self) == /\ pc[self] = "Cancelled"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << upstreamEls, observerTakeN, upstreamN, 
                                   downstreamTakeN, queueContents, streams, 
                                   el_, takeN_, upstreamPending, enqueuedN, el, 
                                   takeN >>

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

Next == (\E self \in {"concurrent"}: concurrent(self))
           \/ (\E self \in {"enqueue"}: enqueue(self))
           \/ (\E self \in {"dequeue"}: dequeue(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"concurrent"} : WF_vars(concurrent(self))
        /\ \A self \in {"enqueue"} : WF_vars(enqueue(self))
        /\ \A self \in {"dequeue"} : WF_vars(dequeue(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Jan 06 14:13:19 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
