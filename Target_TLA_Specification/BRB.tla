-------------------------------- MODULE BRB --------------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS 
    Correct,  \* Set of correct processes
    Faulty,   \* Set of Byzantine faulty processes
    V         \* Set of values that may be broadcast

VARIABLES
    sender,       \* The designated broadcaster process L
    receivedS,    \* Mapping from each process to the value it has received from the sender
    delivered,    \* Delivered value of each correct process, or empty string if undecided
    receivedVote  \* receivedVote[p][v] is the set of processes whose signed vote for v has been received by p

vars == <<sender, receivedS, delivered, receivedVote>>

P == Correct \cup Faulty  \* All processes
N == Cardinality(P)       \* Total number of processes
F == Cardinality(Faulty)  \* Number of faulty processes

(* Type definitions *)
TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> V \cup {""}]
    /\ delivered \in [Correct -> V \cup {""}]
    /\ receivedVote \in [Correct -> [V -> SUBSET P]]

(* Initial state *)
Init ==
    /\ sender \in (Faulty \cup {CHOOSE p \in Correct : TRUE})
    /\ IF sender \in Correct
       THEN LET val == CHOOSE v \in V : TRUE
            IN receivedS = [p \in Correct |-> val]
       ELSE receivedS \in [Correct -> V \cup {""}]
    /\ delivered = [p \in Correct |-> ""]
    /\ receivedVote = [p \in Correct |-> [v \in V |-> {}]]

(* Action: SendVote - a correct process votes for the value it received *)
SendVote(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in V
    /\ \A v \in V : self \notin receivedVote[self][v]
    /\ receivedVote' = [p \in Correct |-> 
                         [v \in V |-> IF v = receivedS[self]
                                      THEN receivedVote[p][v] \cup {self}
                                      ELSE receivedVote[p][v]]]
    /\ UNCHANGED <<sender, receivedS, delivered>>

(* Action: StepCommit - a correct process commits when it has n-f votes *)
StepCommit(self) ==
    /\ self \in Correct
    /\ delivered[self] = ""
    /\ \E v \in V : Cardinality(receivedVote[self][v]) >= N - F
    /\ LET commitVal == CHOOSE v \in V : Cardinality(receivedVote[self][v]) >= N - F
       IN /\ receivedVote' = [p \in Correct |-> 
                               [v \in V |-> IF v = commitVal
                                            THEN receivedVote[p][v] \cup receivedVote[self][v]
                                            ELSE receivedVote[p][v]]]
          /\ delivered' = [delivered EXCEPT ![self] = commitVal]
    /\ UNCHANGED <<sender, receivedS>>

(* Action: ByzantineVote - a faulty process can inject arbitrary votes *)
ByzantineVote(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, v \in V :
        /\ self \notin receivedVote[d][v]
        /\ receivedVote' = [receivedVote EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered>>

(* Next state relation *)
Next ==
    \/ \E self \in Correct : SendVote(self) \/ StepCommit(self)
    \/ \E self \in Faulty : ByzantineVote(self)

(* Specification with fairness *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Correct : WF_vars(SendVote(self) \/ StepCommit(self))

(* Safety Invariant: Consistency *)
Consistency ==
    \A p, q \in Correct : 
        (delivered[p] # "" /\ delivered[q] # "") => delivered[p] = delivered[q]

(* Liveness Property: Totality *)
Totality ==
    (\E p \in Correct : delivered[p] # "") ~> (\A p \in Correct : delivered[p] # "")

(* Liveness Property: Validity *)
Validity ==
    (sender \in Correct) => 
        LET Val == IF sender \in Correct THEN receivedS[sender] ELSE ""
        IN <>(\A p \in Correct : delivered[p] = Val)

=============================================================================
