------------------------------- MODULE ADDRBC -------------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    Correct,   \* Set of correct processes
    Faulty,    \* Set of Byzantine faulty processes
    V,         \* Set of values that may be broadcast
    Symbols    \* Abstract set of Reed-Solomon share symbols

VARIABLES
    sender,        \* Designated broadcaster
    receivedS,     \* receivedS[p] is proposal received by correct p, or ""
    delivered,     \* delivered[p] is RBC output, or ""
    receivedE,     \* receivedE[p][h] is set of ECHO(h) senders seen by p
    receivedR,     \* receivedR[p][h] is set of READY(h) senders seen by p
    addInput,      \* ADD input of correct p: value, Bottom, or "" before start
    mStar,         \* Fixed reconstruction symbol of each process, or ""
    receivedDis,   \* receivedDis[p][sym] is set of DISPERSE senders
    receivedRec,   \* receivedRec[p] is set of <<source, symbol>> pairs
    decodeRound    \* Current online-error-correction round r

vars ==
    <<sender, receivedS, delivered, receivedE, receivedR, addInput,
      mStar, receivedDis, receivedRec, decodeRound>>

P == Correct \cup Faulty
F == Cardinality(Faulty)

Hashes == V 
Hash(m) == m
Predicate(m) == m \in V

Bottom == "bottom"
SymbolOf ==
    CHOOSE f \in [P -> Symbols] :
        \A p, q \in P : (p # q) => (f[p] # f[q])
RecSenders(p) ==
    {src \in P : \E sym \in Symbols : <<src, sym>> \in receivedRec[p]}
MatchingRecSenders(p) ==
    {src \in P : <<src, SymbolOf[src]>> \in receivedRec[p]}
ADDValues ==
    {m \in V : \E p \in Correct : addInput[p] = m}

DecodedADDValue ==
    CHOOSE m \in ADDValues : TRUE

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
    /\ mStar = [p \in P |-> ""]
    /\ receivedDis = [p \in P |-> [sym \in Symbols |-> {}]]
    /\ receivedRec = [p \in P |-> {}]
    /\ decodeRound = [p \in P |-> 0]

TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> V \cup {""}]
    /\ delivered \in [Correct -> V \cup {""}]
    /\ receivedE \in [Correct -> [Hashes -> SUBSET P]]
    /\ receivedR \in [Correct -> [Hashes -> SUBSET P]]
    /\ addInput \in [Correct -> V \cup {Bottom, ""}]
    /\ mStar \in [P -> Symbols \cup {""}]
    /\ receivedDis \in [P -> [Symbols -> SUBSET P]]
    /\ receivedRec \in [P -> SUBSET (P \X Symbols)]
    /\ decodeRound \in [P -> 0..F]

SendEcho(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in V
    /\ Predicate(receivedS[self])
    /\ \A h \in Hashes : self \notin receivedE[self][h]
    /\ LET h == Hash(receivedS[self])
       IN receivedE' =
            [p \in Correct |->
                [hh \in Hashes |->
                    IF hh = h
                    THEN receivedE[p][hh] \cup {self}
                    ELSE receivedE[p][hh]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedR, addInput,
          mStar, receivedDis, receivedRec, decodeRound>>

SendReady(self) ==
    /\ self \in Correct
    /\ \A h \in Hashes : self \notin receivedR[self][h]
    /\ \E h \in Hashes :
          \/ Cardinality(receivedE[self][h]) >= 2 * F + 1
          \/ Cardinality(receivedR[self][h]) >= F + 1
    /\ LET h == CHOOSE hh \in Hashes :
                    \/ Cardinality(receivedE[self][hh]) >= 2 * F + 1
                    \/ Cardinality(receivedR[self][hh]) >= F + 1
       IN receivedR' =
            [p \in Correct |->
                [hh \in Hashes |->
                    IF hh = h
                    THEN receivedR[p][hh] \cup {self}
                    ELSE receivedR[p][hh]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, addInput,
          mStar, receivedDis, receivedRec, decodeRound>>

StepCommit(self) ==
    /\ self \in Correct
    /\ addInput[self] = ""
    /\ \E h \in Hashes :
          Cardinality(receivedR[self][h]) >= 2 * F + 1
    /\ LET h == CHOOSE hh \in Hashes :
                    Cardinality(receivedR[self][hh]) >= 2 * F + 1
       IN addInput' =
            [addInput EXCEPT![self] =
                    IF receivedS[self] \in V /\ h = Hash(receivedS[self])
                    THEN receivedS[self]
                    ELSE Bottom]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR,
          mStar, receivedDis, receivedRec, decodeRound>>

ByzantineEcho(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, h \in Hashes :
          /\ self \notin receivedE[d][h]
          /\ receivedE' = [receivedE EXCEPT ![d][h] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedR, addInput,
          mStar, receivedDis, receivedRec, decodeRound>>

ByzantineReady(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, h \in Hashes :
          /\ self \notin receivedR[d][h]
          /\ receivedR' = [receivedR EXCEPT ![d][h] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, addInput,
          mStar, receivedDis, receivedRec, decodeRound>>

SendDisperse(self) ==
    /\ self \in Correct
    /\ addInput[self] \in V
    /\ mStar[self] = ""
    /\ mStar' = [mStar EXCEPT ![self] = SymbolOf[self]]
    /\ receivedDis' =
          [p \in P |->
              [sym \in Symbols |->
                  IF sym = SymbolOf[p]
                  THEN receivedDis[p][sym] \cup {self}
                  ELSE receivedDis[p][sym]]]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR,
          addInput, receivedRec, decodeRound>>

ReceiveDisperse(self) ==
    /\ self \in Correct
    /\ addInput[self] = Bottom
    /\ mStar[self] = ""
    /\ \E sym \in Symbols :
          Cardinality(receivedDis[self][sym]) >= F + 1
    /\ LET sym0 == CHOOSE sym \in Symbols :
                        Cardinality(receivedDis[self][sym]) >= F + 1
       IN mStar' = [mStar EXCEPT ![self] = sym0]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR,
          addInput, receivedDis, receivedRec, decodeRound>>

SendReconstruct(self) ==
    /\ self \in Correct
    /\ mStar[self] \in Symbols
    /\ \A p \in P :
          <<self, mStar[self]>> \notin receivedRec[p]
    /\ receivedRec' =
          [p \in P |->
              receivedRec[p] \cup {<<self, mStar[self]>>}]
    /\ delivered' =
          [delivered EXCEPT![self] =
                  IF addInput[self] \in V
                  THEN addInput[self]
                  ELSE delivered[self]]
    /\ UNCHANGED <<sender, receivedS, receivedE, receivedR, addInput,
          mStar, receivedDis, decodeRound>>

TryDecode(self) ==
    /\ self \in Correct
    /\ addInput[self] = Bottom
    /\ delivered[self] = ""
    /\ LET r == decodeRound[self]
           matching == MatchingRecSenders(self)
       IN /\ r <= F
          /\ Cardinality(receivedRec[self]) >= 2 * F + r + 1
          /\ IF Cardinality(matching) >= 2 * F + 1
                THEN /\ ADDValues # {}
                     /\ delivered' = [delivered EXCEPT ![self] = DecodedADDValue]
                     /\ UNCHANGED decodeRound
                ELSE /\ r < F
                     /\ decodeRound' =
                           [decodeRound EXCEPT ![self] = r + 1]
                     /\ UNCHANGED delivered
    /\ UNCHANGED <<sender, receivedS, receivedE, receivedR, addInput,
          mStar, receivedDis, receivedRec>>

ByzantineDisperse(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct :
        LET wrongSym == CHOOSE s \in Symbols : s # SymbolOf[d]
        IN \E sym \in { SymbolOf[d], wrongSym } :
            receivedDis' = [receivedDis EXCEPT ![d][sym] = @ \cup {self}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR,
          addInput, mStar, receivedRec, decodeRound>>

ByzantineReconstruct(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct :
        LET wrongSym == CHOOSE s \in Symbols : s # SymbolOf[d]
        IN \E sym \in { SymbolOf[d], wrongSym } :
           receivedRec' = [receivedRec EXCEPT ![d] = @ \cup {<<self, sym>>}]
    /\ UNCHANGED <<sender, receivedS, delivered, receivedE, receivedR,
          addInput, mStar, receivedDis, decodeRound>>

Next ==
    \/ \E self \in Correct :
          \/ SendEcho(self)
          \/ SendReady(self)
          \/ StepCommit(self)
          \/ SendDisperse(self)
          \/ ReceiveDisperse(self)
          \/ SendReconstruct(self)
          \/ TryDecode(self)
    \/ \E self \in Faulty :
          \/ ByzantineEcho(self)
          \/ ByzantineReady(self)
          \/ ByzantineDisperse(self)
          \/ ByzantineReconstruct(self)

Fairness ==
    /\ \A self \in Correct : WF_vars(SendEcho(self))
    /\ \A self \in Correct : WF_vars(SendReady(self))
    /\ \A self \in Correct : WF_vars(StepCommit(self))
    /\ \A self \in Correct : WF_vars(SendDisperse(self))
    /\ \A self \in Correct : WF_vars(ReceiveDisperse(self))
    /\ \A self \in Correct : WF_vars(SendReconstruct(self))
    /\ \A self \in Correct : WF_vars(TryDecode(self))

Spec == Init /\ [][Next]_vars /\ Fairness

Consistency ==
    \A p, q \in Correct :
        (delivered[p] # "" /\ delivered[q] # "")
        => delivered[p] = delivered[q]

Totality ==
    (\E p \in Correct : delivered[p] # "")
    ~>
    (\A p \in Correct : delivered[p] # "")

Validity ==
    (sender \in Correct) =>
        LET Val == IF sender \in Correct THEN receivedS[sender] ELSE ""
        IN <>((\A p \in Correct : delivered[p] = Val))
=============================================================================
