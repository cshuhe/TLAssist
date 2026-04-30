------------------------------- MODULE HoneyBadgerRBC -------------------------------
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS
    Correct,             
    Faulty,              
    Symbols
    
GoodRoots == {"Good"}
BadRoots == {"Bad"}
P == Correct \cup Faulty
F == Cardinality(Faulty)
N == Cardinality(P)

ASSUME N >= 3 * F + 1
Roots == GoodRoots \cup BadRoots
Payloads == {"M_Good", "M_Bad_1", "M_Bad_2", ""}


SymbolOf == CHOOSE f \in [P -> Symbols] : 
                \A p, q \in P : (p # q) => (f[p] # f[q])


Decode(ShardSet, r) ==
    IF r \in GoodRoots THEN "M_Good"
    ELSE IF SymbolOf[CHOOSE p \in Correct : TRUE] \in ShardSet THEN "M_Bad_1" ELSE "M_Bad_2"

VARIABLES
    sender,         
    receivedS,            
    receivedE,            
    receivedR,           
    delivered            

vars == << sender, receivedS, receivedE, receivedR, delivered >>

TypeInv ==
    /\ sender \in P
    /\ receivedS \in [Correct -> Roots \cup {""}]
    /\ receivedE \in [Correct -> SUBSET (P \times Roots \times Symbols)]
    /\ receivedR \in [Correct -> SUBSET (P \times Roots)]
    /\ delivered \in [Correct -> Payloads]

Init ==
    /\ sender \in Faulty
    /\ IF sender \in Correct
       THEN \E v \in GoodRoots : receivedS = [p \in Correct |-> v]
       ELSE receivedS \in [Correct -> Roots \cup {""}]
    /\ receivedE = [ p \in Correct |-> {} ]
    /\ receivedR = [ p \in Correct |-> {} ]
    /\ delivered = [ p \in Correct |-> "" ]

ReceiveValAndEcho(self) ==
    /\ self \in Correct
    /\ receivedS[self] \in Roots
    /\ ~\E msg \in receivedE[self] : msg[1] = self /\ msg[2] = receivedS[self]
    /\ LET r == receivedS[self] 
           myShard == SymbolOf[self] 
       IN receivedE' = [p \in Correct |-> receivedE[p] \cup {<<self, r, myShard>>}]
    /\ UNCHANGED <<sender, receivedS, receivedR, delivered>>

ReceiveEchoAndReady(self) ==
    /\ self \in Correct
    /\ \E r \in Roots :
        /\ ~\E msg \in receivedR[self] : msg[1] = self /\ msg[2] = r
        /\ LET validEchos == { msg \in receivedE[self] : 
                               msg[2] = r /\ msg[3] = SymbolOf[msg[1]] } IN
           Cardinality(validEchos) >= N - F
        /\ r \in GoodRoots               \* [h' == h]
        /\ receivedR' = [ p \in Correct |-> receivedR[p] \cup {<<self, r>>} ]
    /\ UNCHANGED <<sender, receivedS, receivedE, delivered>>

AmplifyReady(self) ==
    /\ self \in Correct
    /\ \E r \in Roots :
        /\ ~\E msg \in receivedR[self] : msg[1] = self /\ msg[2] = r
        /\ LET matchingReadys == { msg \in receivedR[self] : msg[2] = r } IN
           Cardinality(matchingReadys) >= F + 1
        /\ receivedR' = [ p \in Correct |-> receivedR[p] \cup {<<self, r>>} ]
    /\ UNCHANGED <<sender, receivedS, receivedE, delivered>>

TryDecode(self) ==
    /\ self \in Correct
    /\ delivered[self] = ""
    /\ \E r \in Roots :
        /\ Cardinality({ m \in receivedR[self] : m[2] = r }) >= 2 * F + 1
        /\ LET validEchos == { msg \in receivedE[self] : 
                               msg[2] = r /\ msg[3] = SymbolOf[msg[1]] } IN
           /\ Cardinality(validEchos) >= N - 2 * F
           /\ delivered' = [delivered EXCEPT ![self] = Decode({m[3] : m \in validEchos}, r)]
    /\ UNCHANGED <<sender, receivedS, receivedE, receivedR>>

ByzantineEcho(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, r \in Roots :
        receivedE' = [receivedE EXCEPT ![d] = @ \cup {<<self, r, SymbolOf[self]>>}]
    /\ UNCHANGED <<sender, receivedS, receivedR, delivered>>

ByzantineReady(self) ==
    /\ self \in Faulty
    /\ \E d \in Correct, r \in Roots :
        receivedR' = [receivedR EXCEPT ![d] = @ \cup {<<self, r>>}]
    /\ UNCHANGED <<sender, receivedS, receivedE, delivered>>

Next ==
    \/ \E self \in Correct : 
        \/ ReceiveValAndEcho(self) 
        \/ ReceiveEchoAndReady(self) 
        \/ AmplifyReady(self) 
        \/ TryDecode(self)
    \/ \E self \in Faulty : 
        \/ ByzantineEcho(self) 
        \/ ByzantineReady(self)

Fairness ==
    /\ \A self \in Correct : 
        WF_vars(ReceiveValAndEcho(self) \/ ReceiveEchoAndReady(self) \/ AmplifyReady(self) \/ TryDecode(self))

Spec == Init /\ [][Next]_vars /\ Fairness

Consistency == \A p, q \in Correct : 
    (delivered[p] # "" /\ delivered[q] # "") => delivered[p] = delivered[q]

Validity == (sender \in Correct) => <>(\A p \in Correct : delivered[p] = "M_Good")

Totality == (\E p \in Correct : delivered[p] # "") ~> (\A p \in Correct : delivered[p] # "")
=============================================================================