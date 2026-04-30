------------------------------- MODULE SigBRB -------------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC         

CONSTANTS 
    Correct,    \* Set of correct nodes
    Faulty,     \* Set of Byzantine nodes
    Symbols,    \* Set of symbols used as ECC shares
    V          \* Set of values

P == Correct \cup Faulty
F == Cardinality(Faulty)
N == Cardinality(P)


\* Canonical mapping assigning each node its unique share symbol
SymbolOf == CHOOSE f \in [P -> Symbols] : 
    \A p, q \in P : (p # q) => (f[p] # f[q])

\* Variables
VARIABLES
    sender,           \* The designated sender process
    receivedS,        \* Mapping from each correct process to the value it has received from the sender (BCB-SEND)
    receivedRep,      \* receivedRep[p][v] is the set of processes whose BCB-REP signature share for v has been received by p
    receivedFinal,    \* receivedFinal[p][v] is TRUE if p has received a valid BCB-FINAL(v, σ) from sender
    receivedDis,      \* receivedDis[p][sym] is the set of senders who sent DISPERSE(sym) to p
    mStar,            \* Each node's fixed dispersed share ("" if not yet fixed)
    receivedRec,      \* receivedRec[p] is the set of RECONSTRUCT messages <<src, shard>> received by p
    receivedReady,    \* receivedReady[p] is the set of processes whose READY has been received by p
    val,              \* Each node's reconstructed value ("" if not yet reconstructed)
    delivered,        \* Each correct node's decision output ("" if not yet decided)
    decodeRound       \* Current online error-correction round r for each node

vars == <<sender, receivedS, receivedRep, receivedFinal, receivedDis, mStar, 
          receivedRec, receivedReady, val, delivered, decodeRound>>

\* ECC Decoding abstraction
\* ECCDec(recSet, r) returns a value v if decoding succeeds with r errors, otherwise ""
ECCDec(recSet, r) ==
    LET validShares == {item \in recSet : item[2] = SymbolOf[item[1]]}
    IN IF \E v \in V : 
          /\ Cardinality(recSet) >= 2 * F + r + 1
          /\ Cardinality(validShares) >= 2 * F + 1
       THEN CHOOSE v \in V : TRUE
       ELSE ""

\* Type invariant
TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> V \cup {""}]
    /\ receivedRep \in [Correct -> [V -> SUBSET P]]
    /\ receivedFinal \in [Correct -> [V -> BOOLEAN]]
    /\ receivedDis \in [P -> [Symbols -> SUBSET P]]
    /\ mStar \in [P -> Symbols \cup {""}]
    /\ receivedRec \in [P -> SUBSET (P \times Symbols)]
    /\ receivedReady \in [P -> SUBSET P]
    /\ val \in [P -> V \cup {""}]
    /\ delivered \in [Correct -> V \cup {""}]
    /\ decodeRound \in [P -> 0..F]

\* Initial state
Init ==
    /\ sender \in P
    /\ IF sender \in Correct 
       THEN \E v \in V : receivedS = [p \in Correct |-> v]
       ELSE receivedS \in [Correct -> V \cup {""}]
    /\ receivedRep = [p \in Correct |-> [v \in V |-> {}]]
    /\ receivedFinal = [p \in Correct |-> [v \in V |-> FALSE]]
    /\ receivedDis = [p \in P |-> [sym \in Symbols |-> {}]]
    /\ mStar = [p \in P |-> ""]
    /\ receivedRec = [p \in P |-> {}]
    /\ receivedReady = [p \in P |-> {}]
    /\ val = [p \in P |-> ""]
    /\ delivered = [p \in Correct |-> ""]
    /\ decodeRound = [p \in P |-> 0]

\* Actions for correct processes

SendRep(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in V
    /\ sender \in Correct
    /\ self \notin receivedRep[sender][receivedS[self]]
    /\ receivedRep' = [receivedRep EXCEPT 
        ![sender][receivedS[self]] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, receivedFinal, receivedDis, mStar, 
                   receivedRec, receivedReady, val, delivered, decodeRound>>

SendFinal(self) ==
    /\ self \in Correct
    /\ self = sender
    /\ \E v \in V : 
        /\ receivedS[self] = v
        /\ Cardinality(receivedRep[self][v]) >= N - F
        /\ \A p \in Correct : ~receivedFinal[p][v]
        /\ receivedFinal' = [p \in Correct |-> 
            [w \in V |-> IF w = v THEN TRUE ELSE receivedFinal[p][w]]]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedDis, mStar, 
                   receivedRec, receivedReady, val, delivered, decodeRound>>

SendDisperse(self) ==
    /\ self \in Correct
    /\ \E v \in V : 
        /\ receivedS[self] = v
        /\ receivedFinal[self][v] = TRUE
    /\ mStar[self] = ""
    /\ mStar' = [mStar EXCEPT ![self] = SymbolOf[self]]
    /\ receivedDis' = [p \in P |-> 
        [sym \in Symbols |-> 
            IF sym = SymbolOf[p] 
            THEN receivedDis[p][sym] \cup {self}
            ELSE receivedDis[p][sym]]]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, 
                   receivedRec, receivedReady, val, delivered, decodeRound>>

ReceiveDisperse(self) ==
    /\ self \in Correct
    /\ mStar[self] = ""
    /\ \E sym \in Symbols : 
        /\ Cardinality(receivedDis[self][sym]) >= F + 1
        /\ mStar' = [mStar EXCEPT ![self] = sym]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, receivedDis, 
                   receivedRec, receivedReady, val, delivered, decodeRound>>

SendReconstruct(self) ==
    /\ self \in Correct
    /\ mStar[self] # ""
    /\ \A p \in P : <<self, mStar[self]>> \notin receivedRec[p]
    /\ receivedRec' = [p \in P |-> receivedRec[p] \cup {<<self, mStar[self]>>}]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, receivedDis, 
                   mStar, receivedReady, val, delivered, decodeRound>>

TryDecode(self) ==
    /\ self \in Correct
    /\ val[self] = ""
    /\ LET r == decodeRound[self]
       IN /\ r <= F
          /\ Cardinality(receivedRec[self]) >= 2 * F + r + 1
          /\ \E v \in V : 
              /\ ECCDec(receivedRec[self], r) = v
              /\ val' = [val EXCEPT ![self] = v]
              /\ receivedReady' = [p \in P |-> receivedReady[p] \cup {self}]
              /\ IF self # sender 
                 THEN /\ mStar' = [mStar EXCEPT ![self] = SymbolOf[self]]
                      /\ receivedDis' = [p \in P |-> 
                          [sym \in Symbols |-> 
                              IF sym = SymbolOf[p] 
                              THEN receivedDis[p][sym] \cup {self}
                              ELSE receivedDis[p][sym]]]
                 ELSE /\ UNCHANGED <<mStar, receivedDis>>
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, 
                   receivedRec, delivered, decodeRound>>

IncrementDecodeRound(self) ==
    /\ self \in Correct
    /\ val[self] = ""
    /\ decodeRound[self] < F
    /\ LET r == decodeRound[self]
       IN /\ Cardinality(receivedRec[self]) >= 2 * F + r + 1
          /\ \A v \in V : ECCDec(receivedRec[self], r) # v
          /\ decodeRound' = [decodeRound EXCEPT ![self] = @ + 1]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, receivedDis, 
                   mStar, receivedRec, receivedReady, val, delivered>>

Decide(self) ==
    /\ self \in Correct
    /\ val[self] \in V
    /\ Cardinality(receivedReady[self]) >= N - F
    /\ delivered[self] = ""
    /\ delivered' = [delivered EXCEPT ![self] = val[self]]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, receivedDis, 
                   mStar, receivedRec, receivedReady, val, decodeRound>>

\* Actions for Byzantine processes

ByzantineRep(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, v \in V :
        /\ d \in Correct
        /\ self \notin receivedRep[d][v]
        /\ receivedRep' = [receivedRep EXCEPT ![d][v] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, receivedFinal, receivedDis, mStar, 
                   receivedRec, receivedReady, val, delivered, decodeRound>>

ByzantineFinal(self) ==
    /\ self \in Faulty
    /\ self = sender
    /\ \E v \in V :
        /\ \E d \in Correct :  
            /\ ~receivedFinal[d][v]
            /\ receivedFinal' = [receivedFinal EXCEPT ![d][v] = TRUE]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedDis, mStar, 
                   receivedRec, receivedReady, val, delivered, decodeRound>>

ByzantineDisperse(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct :
        LET wrongSym == CHOOSE s \in Symbols : s # SymbolOf[d]
        IN \E sym \in { SymbolOf[d], wrongSym } :
            receivedDis' = [receivedDis EXCEPT ![d][sym] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, mStar, 
                   receivedRec, receivedReady, val, delivered, decodeRound>>

ByzantineReconstruct(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct :
        LET wrongSym == CHOOSE s \in Symbols : s # SymbolOf[d]
        IN \E sym \in { SymbolOf[d], wrongSym } :
           receivedRec' = [receivedRec EXCEPT ![d] = @ \cup {<<self, sym>>}]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, receivedDis, 
                   mStar, receivedReady, val, delivered, decodeRound>>

ByzantineReady(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct :
        /\ self \notin receivedReady[d]
        /\ receivedReady' = [receivedReady EXCEPT ![d] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, receivedRep, receivedFinal, receivedDis, 
                   mStar, receivedRec, val, delivered, decodeRound>>

\* Next state relation
Next ==
    \/ \E self \in Correct : 
        \/ SendRep(self)
        \/ SendFinal(self)
        \/ SendDisperse(self)
        \/ ReceiveDisperse(self)
        \/ SendReconstruct(self)
        \/ TryDecode(self)
        \/ IncrementDecodeRound(self)
        \/ Decide(self)
    \/ \E self \in Faulty :
        \/ ByzantineRep(self)
        \/ ByzantineFinal(self)
        \/ ByzantineDisperse(self)
        \/ ByzantineReconstruct(self)
        \/ ByzantineReady(self)

\* Fairness conditions for correct processes
Fairness == 
    \A self \in Correct : 
        WF_vars(SendRep(self) \/ SendFinal(self) \/ SendDisperse(self) \/ 
                ReceiveDisperse(self) \/ SendReconstruct(self) \/ 
                TryDecode(self) \/ IncrementDecodeRound(self) \/ Decide(self))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Invariants
Consistency ==
    \A p, q \in Correct : 
        (delivered[p] # "" /\ delivered[q] # "") => delivered[p] = delivered[q]

\* Properties
Totality ==
    (\E p \in Correct : delivered[p] # "") ~> (\A p \in Correct : delivered[p] # "")

Validity ==
    (sender \in Correct) => 
        LET Val == IF sender \in Correct THEN receivedS[sender] ELSE ""
        IN <>(Val # "" => \A p \in Correct : delivered[p] = Val)
=============================================================================