------------------------- MODULE OptimisticRBC -------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC   

CONSTANTS
    Correct,    \* Set of correct processes
    Faulty,     \* Set of Byzantine faulty processes
    V           \* Set of values that may be broadcast

VARIABLES
    sender,  \* The designated sender process
    receivedS,     \* Mapping from each process to the value it has received from the sender
    delivered,    \* Delivered value of each correct process, or empty string if undecided
    receivedE,     \* receivedE[p][v] is the set of processes whose ECHO(v) has been received by p
    receivedV,     \* receivedV[p][v] is the set of processes whose VOTE(v) has been received by p
    receivedR     \* receivedR[p][v] is the set of processes whose READY(v) has been received by p

vars == <<sender, receivedS, delivered, receivedE, receivedV, receivedR>>

P == Correct \cup Faulty
N == Cardinality(P)
F == Cardinality(Faulty)

Ceiling(x, y) == IF x % y = 0 THEN x \div y ELSE (x \div y) + 1

TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> V \cup {""}]
    /\ delivered \in [Correct -> V \cup {""}]
    /\ receivedE \in [Correct -> [V -> SUBSET P]]
    /\ receivedV \in [Correct -> [V -> SUBSET P]]
    /\ receivedR \in [Correct -> [V -> SUBSET P]]

Init ==
    /\ sender \in (Faulty \cup {CHOOSE p \in Correct : TRUE})
    /\ IF sender \in Correct
       THEN receivedS = [p \in Correct |-> CHOOSE v \in V : TRUE]
       ELSE receivedS \in [Correct -> V \cup {""}]
    /\ delivered = [p \in Correct |-> ""]
    /\ receivedE = [p \in Correct |-> [v \in V |-> {}]]
    /\ receivedV = [p \in Correct |-> [v \in V |-> {}]]
    /\ receivedR = [p \in Correct |-> [v \in V |-> {}]]

SendEcho(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in V
    /\ \A v \in V : self \notin receivedE[self][v]
    /\ LET val == receivedS[self]
       IN receivedE' = [p \in Correct |-> [v \in V |-> 
            IF v = val THEN receivedE[p][v] \cup {self}
            ELSE receivedE[p][v]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedV, receivedR>>

SendVote(self) ==
    /\ self \in Correct
    /\ \A v \in V : self \notin receivedV[self][v]
    /\ \E v \in V : 
        Cardinality({p \in receivedE[self][v] : p /= sender}) >= Ceiling(N, 2)
    /\ LET val == CHOOSE v \in V : 
            Cardinality({p \in receivedE[self][v] : p /= sender}) >= Ceiling(N, 2)
       IN receivedV' = [p \in Correct |-> [v \in V |-> 
            IF v = val THEN receivedV[p][v] \cup {self}
            ELSE receivedV[p][v]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR>>

SendReady(self) ==
    /\ self \in Correct
    /\ \A v \in V : self \notin receivedR[self][v]
    /\ \E v \in V : 
        \/ Cardinality({p \in receivedE[self][v] : p /= sender}) >= Ceiling(N + F - 1, 2)
        \/ Cardinality({p \in receivedV[self][v] : p /= sender}) >= Ceiling(N + F - 1, 2)
        \/ Cardinality(receivedR[self][v]) >= F + 1
    /\ LET val == CHOOSE v \in V : 
            \/ Cardinality({p \in receivedE[self][v] : p /= sender}) >= Ceiling(N + F - 1, 2)
            \/ Cardinality({p \in receivedV[self][v] : p /= sender}) >= Ceiling(N + F - 1, 2)
            \/ Cardinality(receivedR[self][v]) >= F + 1
       IN receivedR' = [p \in Correct |-> [v \in V |-> 
            IF v = val THEN receivedR[p][v] \cup {self}
            ELSE receivedR[p][v]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedV>>

OptCommit(self) ==
    /\ self \in Correct
    /\ delivered[self] = ""
    /\ \E v \in V : 
        Cardinality({p \in receivedE[self][v] : p /= sender}) >= Ceiling(N + 2*F - 2, 2)
    /\ LET val == CHOOSE v \in V : 
            Cardinality({p \in receivedE[self][v] : p /= sender}) >= Ceiling(N + 2*F - 2, 2)
       IN delivered' = [delivered EXCEPT ![self] = val]
    /\ UNCHANGED <<sender, receivedS, receivedE, receivedV, receivedR>>

StepCommit(self) ==
    /\ self \in Correct
    /\ delivered[self] = ""
    /\ \E v \in V : Cardinality(receivedR[self][v]) >= 2*F + 1
    /\ LET val == CHOOSE v \in V : Cardinality(receivedR[self][v]) >= 2*F + 1
       IN delivered' = [delivered EXCEPT ![self] = val]
    /\ UNCHANGED <<sender, receivedS, receivedE, receivedV, receivedR>>

ByzantineEcho(self) ==
    /\ self \in Faulty \ {sender}
    /\ \E d \in Correct, v \in V :
        /\ self \notin receivedE[d][v]
        /\ receivedE' = [receivedE EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedV, receivedR>>

ByzantineVote(self) ==
    /\ self \in Faulty \ {sender}
    /\ \E d \in Correct, v \in V :
        /\ self \notin receivedV[d][v]
        /\ receivedV' = [receivedV EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR>>

ByzantineReady(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, v \in V :
        /\ self \notin receivedR[d][v]
        /\ receivedR' = [receivedR EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedV>>

Next ==
    \/ \E self \in Correct : 
        \/ SendEcho(self)
        \/ SendVote(self)
        \/ SendReady(self)
        \/ OptCommit(self)
        \/ StepCommit(self)
    \/ \E self \in Faulty :
        \/ ByzantineEcho(self)
        \/ ByzantineVote(self)
        \/ ByzantineReady(self)

Fairness ==
    /\ \A self \in Correct : WF_vars(SendEcho(self))
    /\ \A self \in Correct : WF_vars(SendVote(self))
    /\ \A self \in Correct : WF_vars(SendReady(self))
    /\ \A self \in Correct : WF_vars(OptCommit(self))
    /\ \A self \in Correct : WF_vars(StepCommit(self))

Spec == Init /\ [][Next]_vars /\ Fairness

Consistency ==
    \A p, q \in Correct : 
        (delivered[p] /= "" /\ delivered[q] /= "") => delivered[p] = delivered[q]

Totality ==
    (\E p \in Correct : delivered[p] /= "") ~> (\A p \in Correct : delivered[p] /= "")

Validity ==
    (sender \in Correct) => 
        LET Val == IF sender \in Correct 
                           THEN receivedS[sender] 
                           ELSE ""  
        IN <>(\A p \in Correct : delivered[p] = Val) 
=============================================================================
