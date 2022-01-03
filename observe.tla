------------------------------ MODULE observe ------------------------------
EXTENDS Integers, Sequences
(* This TLA+ Spec verifies

Stream(1, 2, 3) // UPSTREAM
.compile.drain  // DOWNSTREAM
*)


(* --algorithm observe
variables upstreamPending = <<1, 2, 3>>, \* The elements in the upstream Stream(1, 2, 3)
          upstreamPulled = {}, \* The elements pulled from upstream
          downstreamNRequests = 0, \* The number of elements requested by downstream
          downstreamReceived = {}, \* The elements received by downstream from upstream
          downstreamFinished = FALSE, \* Whether downstream has received a "done" message
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
      \* Deliver the element downstream
      downstreamReceived := downstreamReceived \union {element};
    else 
      \* Else deliver "done" downstream
      downstreamFinished := TRUE
    end if;
  end while;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "e209fcec" /\ chksum(tla) = "6ee4d55c")
VARIABLES upstreamPending, upstreamPulled, downstreamNRequests, 
          downstreamReceived, downstreamFinished, element, pc

(* define statement *)
PulledRequestedInvariant == \A e \in upstreamPulled : e <= downstreamNRequests


DoneInvariant == ~downstreamFinished


vars == << upstreamPending, upstreamPulled, downstreamNRequests, 
           downstreamReceived, downstreamFinished, element, pc >>

Init == (* Global variables *)
        /\ upstreamPending = <<1, 2, 3>>
        /\ upstreamPulled = {}
        /\ downstreamNRequests = 0
        /\ downstreamReceived = {}
        /\ downstreamFinished = FALSE
        /\ element = FALSE
        /\ pc = "CheckFinished"

CheckFinished == /\ pc = "CheckFinished"
                 /\ IF ~downstreamFinished
                       THEN /\ pc' = "MakeRequest"
                       ELSE /\ pc' = "Done"
                 /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                 downstreamNRequests, downstreamReceived, 
                                 downstreamFinished, element >>

MakeRequest == /\ pc = "MakeRequest"
               /\ downstreamNRequests' = downstreamNRequests + 1
               /\ IF Len(upstreamPending) > 0
                     THEN /\ element' = Head(upstreamPending)
                          /\ upstreamPending' = Tail(upstreamPending)
                          /\ upstreamPulled' = (upstreamPulled \union {element'})
                          /\ downstreamReceived' = (downstreamReceived \union {element'})
                          /\ UNCHANGED downstreamFinished
                     ELSE /\ downstreamFinished' = TRUE
                          /\ UNCHANGED << upstreamPending, upstreamPulled, 
                                          downstreamReceived, element >>
               /\ pc' = "CheckFinished"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CheckFinished \/ MakeRequest
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Jan 03 19:57:44 GMT 2022 by zainab
\* Created Mon Jan 03 18:56:25 GMT 2022 by zainab
