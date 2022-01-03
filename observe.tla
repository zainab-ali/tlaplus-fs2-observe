------------------------------ MODULE observe ------------------------------
EXTENDS Integers
(* This TLA+ Spec verifies

Stream(1, 2, 3) // UPSTREAM
.compile.drain  // DOWNSTREAM
*)

\* Constants
Done == "done"

(* --algorithm observe
variables upstreamPending = <<1, 2, 3>>,
          upstreamPulled = {}, \* The elements pulled from upstream
          downstreamNRequests = 0, \* The number of elements requested by downstream
          downstreamReceived = {}, \* The elements received by downstream from upstream
          \* Temporary variables
          element = FALSE, 
define
\* Invariants
(* All elements that have been pulled from upstream were requested by downstream 

Given that the value of an element corresponds to its index, this can be translated into:

For all elements in the set of "elements pulled from upstream"
The "number of elements requested from downstream" is greater than or equal to the element
*)
PulledRequestedInvariant == \A e \in upstreamPulled : e >= downstreamNRequests

\* Operators
\* Downstream has finished when it has received a "done" message
DownstreamFinished == Done \in downstreamReceived
end define 
begin
  \* While downstream has not finished
  CheckFinished: while ~DownstreamFinished do
    downstreamReceived := {Done};
    \* TODO: Make a request from downstream to upstream
    \* TODO: If there is an element upstream, pull the element
    \* TODO:  Deliver that element downstream
    \* TODO: Else respond with "done"
  end while;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "4a41aab1" /\ chksum(tla) = "62b9ad58")
VARIABLES upstreamPending, upstreamPulled, downstreamNRequests, 
          downstreamReceived, element, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamPulled : e >= downstreamNRequests



DownstreamFinished == Done \in downstreamReceived


vars == << upstreamPending, upstreamPulled, downstreamNRequests, 
           downstreamReceived, element, pc >>

Init == (* Global variables *)
        /\ upstreamPending = <<1, 2, 3>>
        /\ upstreamPulled = {}
        /\ downstreamNRequests = 0
        /\ downstreamReceived = {}
        /\ element = FALSE
        /\ pc = "CheckFinished"

CheckFinished == /\ pc = "CheckFinished"
                 /\ IF ~DownstreamFinished
                       THEN /\ downstreamReceived' = {Done}
                            /\ pc' = "CheckFinished"
                       ELSE /\ pc' = "Done"
                            /\ UNCHANGED downstreamReceived
                 /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                 downstreamNRequests, element >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CheckFinished
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Jan 03 19:29:30 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
