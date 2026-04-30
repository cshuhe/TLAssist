------------------------------- MODULE ADDRBC -------------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    Correct,  \* Set of correct processes
    Faulty,   \* Set of Byzantine faulty processes
    V         \* Set of values that may be broadcast

VARIABLES
    sender,      \* The designated sender process
    receivedS,   \* Mapping from each process to the value it has received from the sender
    delivered,   \* Delivered value of each correct process, or empty string if undecided
    receivedE,   \* receivedE[p][h] is the set of processes whose ECHO(h) has been received by p
    receivedR,   \* receivedR[p][h] is the set of processes whose READY(h) has been received by p
    addInput     \* addInput[p] records the input to ADD for process p: either a value from V or ⊥

vars == <<sender, receivedS, delivered, receivedE, receivedR, addInput>>

\* Process set
P == Correct \cup Faulty

\* Fault tolerance parameter
F == Cardinality(Faulty)

\* Hash abstraction: deterministic mapping from values to hashes
Hashes == V \cup {"h_bottom"}

Hash(m) == IF m \in V THEN m ELSE "h_bottom"

\* Predicate P(M) - assumed to hold for all values in V
Predicate(m) == m \in V

\* Bottom value for ADD
Bottom == "bottom"

\* -----------------------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------------------

Init ==
    /\ sender \in (Faulty \cup {CHOOSE p \in Correct : TRUE})
    /\ receivedS \in IF sender \in Correct
                     THEN LET val == CHOOSE v \in V : TRUE
                          IN {[p \in Correct |-> val]}
                     ELSE [Correct -> V \cup {""}]
    /\ delivered = [p \in Correct |-> ""]
    /\ receivedE = [p \in Correct |-> [h \in Hashes |-> {}]]
    /\ receivedR = [p \in Correct |-> [h \in Hashes |-> {}]]
    /\ addInput = [p \in Correct |-> ""]

\* -----------------------------------------------------------------------------
\* Type invariant
\* -----------------------------------------------------------------------------

TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> V \cup {""}]
    /\ delivered \in [Correct -> V \cup {""}]
    /\ receivedE \in [Correct -> [Hashes -> SUBSET P]]
    /\ receivedR \in [Correct -> [Hashes -> SUBSET P]]
    /\ addInput \in [Correct -> V \cup {Bottom, ""}]

\* -----------------------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------------------

SendEcho(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in V
    /\ Predicate(receivedS[self])
    /\ \A h \in Hashes : self \notin receivedE[self][h]
    /\ LET h == Hash(receivedS[self])
       IN receivedE' = [p \in Correct |-> [hh \in Hashes |->
                           IF hh = h THEN receivedE[p][hh] \cup {self}
                           ELSE receivedE[p][hh]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedR, addInput>>

SendReady(self) ==
    /\ self \in Correct
    /\ \A h \in Hashes : self \notin receivedR[self][h]
    /\ \E h \in Hashes :
        \/ Cardinality(receivedE[self][h]) >= 2 * F + 1
        \/ Cardinality(receivedR[self][h]) >= F + 1
    /\ LET h == CHOOSE hh \in Hashes :
                    \/ Cardinality(receivedE[self][hh]) >= 2 * F + 1
                    \/ Cardinality(receivedR[self][hh]) >= F + 1
       IN receivedR' = [p \in Correct |-> [hh \in Hashes |->
                           IF hh = h THEN receivedR[p][hh] \cup {self}
                           ELSE receivedR[p][hh]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, addInput>>

StepCommit(self) ==
    /\ self \in Correct
    /\ addInput[self] = ""
    /\ \E h \in Hashes : Cardinality(receivedR[self][h]) >= 2 * F + 1
    /\ LET h == CHOOSE hh \in Hashes : Cardinality(receivedR[self][hh]) >= 2 * F + 1
       IN addInput' = [addInput EXCEPT ![self] =
                          IF receivedS[self] \in V /\ h = Hash(receivedS[self])
                          THEN receivedS[self]
                          ELSE Bottom]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR>>

FinalDeliver(self) ==
    /\ self \in Correct
    /\ addInput[self] \in V \cup {Bottom}
    /\ delivered[self] = ""
    /\ delivered' = [delivered EXCEPT ![self] =
                        IF addInput[self] \in V
                        THEN addInput[self]
                        ELSE ""]
    /\ UNCHANGED <<sender, receivedS, receivedE, receivedR, addInput>>

ByzantineEcho(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, h \in Hashes :
        /\ self \notin receivedE[d][h]
        /\ receivedE' = [receivedE EXCEPT ![d][h] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedR, addInput>>

ByzantineReady(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, h \in Hashes :
        /\ self \notin receivedR[d][h]
        /\ receivedR' = [receivedR EXCEPT ![d][h] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, addInput>>

\* -----------------------------------------------------------------------------
\* Next state relation
\* -----------------------------------------------------------------------------

Next ==
    \/ \E self \in Correct :
        \/ SendEcho(self)
        \/ SendReady(self)
        \/ StepCommit(self)
        \/ FinalDeliver(self)
    \/ \E self \in Faulty :
        \/ ByzantineEcho(self)
        \/ ByzantineReady(self)

\* -----------------------------------------------------------------------------
\* Fairness and specification
\* -----------------------------------------------------------------------------

Fairness ==
    /\ \A self \in Correct : WF_vars(SendEcho(self))
    /\ \A self \in Correct : WF_vars(SendReady(self))
    /\ \A self \in Correct : WF_vars(StepCommit(self))
    /\ \A self \in Correct : WF_vars(FinalDeliver(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* -----------------------------------------------------------------------------
\* Safety invariants
\* -----------------------------------------------------------------------------

Consistency ==
    \A p, q \in Correct :
        (delivered[p] # "" /\ delivered[q] # "") => delivered[p] = delivered[q]

\* -----------------------------------------------------------------------------
\* Liveness properties
\* -----------------------------------------------------------------------------

Totality ==
    (\E p \in Correct : delivered[p] # "") ~> (\A p \in Correct : delivered[p] # "")

Validity ==
    (sender \in Correct) =>
        LET Val == IF sender \in Correct THEN receivedS[sender] ELSE ""
        IN <>((\A p \in Correct : delivered[p] = Val))

=============================================================================
