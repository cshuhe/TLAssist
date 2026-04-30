---------------------- MODULE AEB ----------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS Correct, Faulty, V

VARIABLES sender, receivedS, delivered, receivedE

vars == <<sender, receivedS, delivered, receivedE>>

N == Cardinality(Correct \cup Faulty)
F == Cardinality(Faulty)
P == Correct \cup Faulty

-----------------------------------------------------------------------------

TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> V \cup {""}]
    /\ delivered \in [Correct -> V \cup {""}]
    /\ receivedE \in [Correct -> [V -> SUBSET P]]

-----------------------------------------------------------------------------

Init ==
    /\ sender \in (Faulty \cup {CHOOSE p \in Correct : TRUE})
    /\ IF sender \in Correct
       THEN receivedS = [p \in Correct |-> CHOOSE v \in V : TRUE]
       ELSE receivedS \in [Correct -> V \cup {""}]
    /\ delivered = [p \in Correct |-> ""]
    /\ receivedE = [p \in Correct |-> [v \in V |-> {}]]

-----------------------------------------------------------------------------

SendEcho(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in V
    /\ \A v \in V : self \notin receivedE[self][v]
    /\ receivedE' = [p \in Correct |->
                      [v \in V |-> IF v = receivedS[self]
                                   THEN receivedE[p][v] \cup {self}
                                   ELSE receivedE[p][v]]]
    /\ UNCHANGED <<sender, receivedS, delivered>>

StepDeliver(self) ==
    /\ self \in Correct
    /\ delivered[self] = ""
    /\ \E v \in V : Cardinality(receivedE[self][v]) > (N + F) \div 2
    /\ LET v == CHOOSE v \in V : Cardinality(receivedE[self][v]) > (N + F) \div 2
       IN delivered' = [delivered EXCEPT ![self] = v]
    /\ UNCHANGED <<sender, receivedS, receivedE>>

ByzantineEcho(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, v \in V :
        /\ self \notin receivedE[d][v]
        /\ receivedE' = [receivedE EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered>>

-----------------------------------------------------------------------------

Next ==
    \/ \E self \in Correct : SendEcho(self) \/ StepDeliver(self)
    \/ \E self \in Faulty : ByzantineEcho(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Correct : WF_vars(SendEcho(self) \/ StepDeliver(self))

-----------------------------------------------------------------------------

Consistency ==
    \A p, q \in Correct :
        (delivered[p] # "" /\ delivered[q] # "") => delivered[p] = delivered[q]

Validity ==
    (sender \in Correct) =>
        LET Val == IF sender \in Correct THEN receivedS[sender] ELSE ""
        IN <>((\A p \in Correct : delivered[p] = Val))

=============================================================================