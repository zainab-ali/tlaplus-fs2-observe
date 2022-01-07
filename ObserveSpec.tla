---------------------------- MODULE ObserveSpec ----------------------------
(* This TLA+ Spec lists the properties that any implementation of observe must satisfy.

 - [ ] If in is finite, then out terminates
 - [ ] If the in is finite and the observer requests the same number of elements as the out, then the output and observer should both complete.
*)

EXTENDS Integers, Sequences

\* There are three parts to the system: the input stream, the output stream and the observer
CONSTANTS Streams, P_in, P_out, P_obs

\* Each stream can be in several states
CONSTANTS States, S_Running, S_Errored, S_Cancelled, S_Succeeded

VARIABLES streams

(* Invariants *)

\* No more elements are pulled from the input than are requested by the output
InSendsOnlyElementsThanOutRequests ==
  Len(streams[P_in].sent) <= streams[P_out].nRequested

\* No more elements are pulled from the input than are requested by the observer
InSendsOnlyElementsThanObsRequests ==
  Len(streams[P_in].sent) <= streams[P_obs].nRequested

\* The number of elements pulled from the input is at most one greater than the number of elements requested by the output
InSendsAtMostOneMoreThanOutReceives ==
  Len(streams[P_in].sent) <= 1 + Len(streams[P_out].received)

\* If the output terminates successfully, then the elements pulled by it should be equal to those pulled from the input
OutSucceedsThenOutElementsEqualsInElements ==
  streams[P_out].state = S_Succeeded
  => streams[P_out].received = streams[P_in].sent

\* If the observer terminates successfully, then the elements it receives by it should be equal to those sent from the input
ObserverSucceedsThenObserverElementsEqualsInElements ==
  streams[P_obs].state = S_Succeeded
  => streams[P_obs].received = streams[P_in].sent

(* Temporal Properties *)

\* If the input terminates then the output eventually terminates
InTerminatesThenOutEventuallyTerminates == ~ streams[P_in].state = S_Running ~> ~ streams[P_out].state = S_Running

\* If the input terminates then the observer eventually terminates
InTerminatesThenObserverEventuallyTerminates ==
  ~ streams[P_in].state = S_Running ~> ~ streams[P_obs].state = S_Running

\* If the input terminates with an error then the output eventually terminates with an error
InTerminatesWithErrorThenOutEventuallyTerminatesWithError ==
  /\ streams[P_in].state = S_Errored
  /\ streams[P_out].state = S_Running
  ~> streams[P_out.state]  = S_Errored

\* If the observer terminates with an error then the output eventually terminates with an error
ObserverTerminatesWithErrorThenOutEventuallyTerminatesWithError ==
  /\ streams[P_obs].state = S_Errored
  /\ streams[P_out].state = S_Running
  ~> streams[P_out.state]  = S_Errored

\* If the output has succeeded, but the observer is still requesting elements, then the observer should be cancelled.
ObserverRequestsMoreElementsThanOutThenObserverEventuallyTerimnatesWithCancel ==
  /\ streams[P_out].state = S_Succeeded
  /\ streams[P_obs].nRequested > streams[P_out].nRequested
  ~> streams[P_obs].state = S_Cancelled

\* If the observer is cancelled then the output should also be cancelled.
ObserverIsCancelledThenOutputEventuallyTerminatesWithCancel ==
  /\ streams[P_obs].state = S_Cancelled
  /\ streams[P_out].state = S_Running
  ~> streams[P_out].state = S_Cancelled

\* If the output is cancelled then the observer should also be cancelled.
OuIsCancelledThenObserverEventuallyTerminatesWithCancel ==
  /\ streams[P_out].state = S_Cancelled
  /\ streams[P_obs].state = S_Running
  ~> streams[P_obs].state = S_Cancelled

=============================================================================
\* Modification History
\* Last modified Fri Jan 07 14:37:10 GMT 2022 by zainab
\* Created Fri Jan 07 10:51:41 GMT 2022 by zainab
