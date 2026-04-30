----------------------------- MODULE ADB -----------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    Correct,
    Faulty,
    V

VARIABLES
    sender,
    receivedS,
    delivered,
    receivedE,
    receivedR

vars == <<sender, receivedS, delivered, receivedE, receivedR>>

P == Correct \cup Faulty
F == Cardinality(Faulty)
N == Cardinality(P)

ASSUME N = 3 * F + 1


TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> V \cup {""}]
    /\ delivered \in [Correct -> V \cup {""}]
    /\ receivedE \in [Correct -> [V -> SUBSET P]]
    /\ receivedR \in [Correct -> [V -> SUBSET P]]


Init ==
    /\ sender \in (Faulty \cup {CHOOSE p \in Correct : TRUE})
    /\ IF sender \in Correct
       THEN receivedS = [p \in Correct |-> CHOOSE v \in V : TRUE]
       ELSE receivedS \in [Correct -> V \cup {""}]
    /\ delivered = [p \in Correct |-> ""]
    /\ receivedE = [p \in Correct |-> [v \in V |-> {}]]
    /\ receivedR = [p \in Correct |-> [v \in V |-> {}]]


SendEcho(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in V
    /\ \A v \in V : self \notin receivedE[self][v]
    /\ LET val == receivedS[self]
       IN receivedE' = [p \in Correct |-> [v \in V |->
                        IF v = val
                        THEN receivedE[p][v] \cup {self}
                        ELSE receivedE[p][v]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedR>>

SendReady(self) ==
    /\ self \in Correct
    /\ \A v \in V : self \notin receivedR[self][v]
    /\ \E v \in V :
        \/ Cardinality(receivedE[self][v]) >= 2 * F + 1
        \/ Cardinality(receivedR[self][v]) >= F + 1
    /\ LET val == CHOOSE v \in V :
                    Cardinality(receivedE[self][v]) >= 2 * F + 1
                    \/ Cardinality(receivedR[self][v]) >= F + 1
       IN receivedR' = [p \in Correct |-> [v \in V |->
                         IF v = val
                         THEN receivedR[p][v] \cup {self}
                         ELSE receivedR[p][v]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE>>

StepCommit(self) ==
    /\ self \in Correct
    /\ delivered[self] = ""
    /\ \E v \in V : Cardinality(receivedR[self][v]) >= 2 * F + 1
    /\ LET val == CHOOSE v \in V : Cardinality(receivedR[self][v]) >= 2 * F + 1
       IN delivered' = [delivered EXCEPT ![self] = val]
    /\ UNCHANGED <<sender, receivedS, receivedE, receivedR>>

ByzantineEcho(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, v \in V :
        /\ self \notin receivedE[d][v]
        /\ receivedE' = [receivedE EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedR>>

ByzantineReady(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, v \in V :
        /\ self \notin receivedR[d][v]
        /\ receivedR' = [receivedR EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE>>

Next ==
    \/ \E self \in Correct :
        \/ SendEcho(self)
        \/ SendReady(self)
        \/ StepCommit(self)
    \/ \E self \in Faulty :
        \/ ByzantineEcho(self)
        \/ ByzantineReady(self)

Fairness ==
    /\ \A self \in Correct : WF_vars(SendEcho(self) \/ SendReady(self) \/ StepCommit(self))

Spec == Init /\ [][Next]_vars /\ Fairness


Consistency ==
    \A p, q \in Correct :
        (delivered[p] # "" /\ delivered[q] # "") => delivered[p] = delivered[q]


Totality ==
    (\E p \in Correct : delivered[p] # "") ~> (\A p \in Correct : delivered[p] # "")

Validity ==
    (sender \in Correct) =>
        LET Val == IF sender \in Correct
                           THEN receivedS[sender]
                           ELSE ""
        IN <>(\A p \in Correct : delivered[p] = Val)
=============================================================================
