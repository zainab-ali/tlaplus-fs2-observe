---------------------------- MODULE ObserveSpec ----------------------------
(* This TLA+ Spec lists the properties that any implementation of observe must satisfy.

 - [ ] If in is finite, then out terminates
 - [ ] If the in is finite and the observer requests the same number of elements as the out, then the output and observer should both complete.
*)

EXTENDS Integers, Sequences

\* There are three parts to the system: the input stream, the output stream and the observer
CONSTANTS Streams, PIn, POut, PObs

\* Each stream can be in several states
CONSTANTS States, SRunning, SErrored, SCancelled, SSucceeded

VARIABLES streams

(* Invariants *)

\* No more elements are pulled from the input than are requested by the output
InSendsOnlyElementsThanOutRequests ==
  Len(streams.PIn.sent) <= streams.POut.nRequested

\* No more elements are pulled from the input than are requested by the observer
InSendsOnlyElementsThanObsRequests ==
  Len(streams[PIn].sent) <= streams[PObs].nRequested

\* The number of elements pulled from the input is at most one greater than the number of elements requested by the output
InSendsAtMostOneMoreThanOutReceives ==
  Len(streams[PIn].sent) <= 1 + Len(streams[POut].received)

\* If the output terminates successfully, then the elements pulled by it should be equal to those pulled from the input
OutSucceedsThenOutElementsEqualsInElements ==
  streams[POut].state = SSucceeded
  => streams[POut].received = streams[PIn].sent

\* If the observer terminates successfully, then the elements it receives by it should be equal to those sent from the input
ObserverSucceedsThenObserverElementsEqualsInElements ==
  streams[PObs].state = SSucceeded
  => streams[PObs].received = streams[PIn].sent

(* Temporal Properties *)

\* If the input terminates then the output eventually terminates
InTerminatesThenOutEventuallyTerminates == ~ streams[PIn].state = SRunning ~> ~ streams[POut].state = SRunning

\* If the input terminates then the observer eventually terminates
InTerminatesThenObserverEventuallyTerminates ==
  ~ streams[PIn].state = SRunning ~> ~ streams[PObs].state = SRunning

\* If the input terminates with an error then the output eventually terminates with an error
InTerminatesWithErrorThenOutEventuallyTerminatesWithError ==
  /\ streams[PIn].state = SErrored
  /\ streams[POut].state = SRunning
  ~> streams[POut.state]  = SErrored

\* If the observer terminates with an error then the output eventually terminates with an error
ObserverTerminatesWithErrorThenOutEventuallyTerminatesWithError ==
  /\ streams[PObs].state = SErrored
  /\ streams[POut].state = SRunning
  ~> streams[POut.state]  = SErrored

\* If the output has succeeded, but the observer is still requesting elements, then the observer should be cancelled.
ObserverRequestsMoreElementsThanOutThenObserverEventuallyTerimnatesWithCancel ==
  /\ streams[POut].state = SSucceeded
  /\ streams[PObs].nRequested > streams[POut].nRequested
  ~> streams[PObs].state = SCancelled

\* If the observer is cancelled then the output should also be cancelled.
ObserverIsCancelledThenOutputEventuallyTerminatesWithCancel ==
  /\ streams[PObs].state = SCancelled
  /\ streams[POut].state = SRunning
  ~> streams[POut].state = SCancelled

\* If the output is cancelled then the observer should also be cancelled.
OuIsCancelledThenObserverEventuallyTerminatesWithCancel ==
  /\ streams[POut].state = SCancelled
  /\ streams[PObs].state = SRunning
  ~> streams[PObs].state = SCancelled

=============================================================================
\* Modification History
\* Last modified Fri Jan 07 15:21:55 GMT 2022 by zainab
\* Created Fri Jan 07 10:51:41 GMT 2022 by zainab
