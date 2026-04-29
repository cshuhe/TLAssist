# Some pseudocode and JSON examples
## 1.Pseudocode:
```pseudocode
Algorithm: RBC
// only broadcaster node
input 𝑀
send ⟨PROPOSE, 𝑀 ⟩ to all
// all nodes
upon receiving ⟨PROPOSE, 𝑀 ⟩ from the broadcaster do
    send ⟨ECHO, 𝑀 ⟩ to all
upon receiving 2𝑡 + 1 ⟨ECHO, 𝑀 ⟩ messages and not having sent a READY message do
    send ⟨READY, 𝑀 ⟩ to all
upon receiving 𝑡 +1 ⟨READY, 𝑀 ⟩ messages and not having sent a READY message do
    send ⟨READY, 𝑀 ⟩ to all
upon receiving 2𝑡 + 1 ⟨READY, 𝑀 ⟩ messages do
    output M
```

## Corresponding JSON:
```json
{
  "CONSTANTS": {
    "Correct": "Set of correct processes ",
    "Faulty": "Set of Byzantine faulty processes ",
    "V": "Set of values that may be broadcast "
  },
  "VARIABLES": {
    "sender": {
      "description": "The designated sender process ",
      "init": "sender \\in (Faulty \\cup {CHOOSE p \\in Correct : TRUE}). "
    },
    "receivedS": {
      "description": "Mapping from each process to the value it has received from the sender ",
      "type": "Correct → V ∪ {\"\"} ",
      "init": "If sender ∈ Correct, receivedS maps all correct processes to a chosen value; otherwise unconstrained mapped to V ∪ {\"\"} "
    },
    "delivered": {
      "description": "Delivered value of each correct process, or empty string if undecided ",
      "type": "Correct → V ∪ {\"\"} ",
      "init": "All correct processes initially map to empty string "
    },
    "receivedE": {
      "description": "receivedE[p][v] is the set of processes whose ECHO(v) has been received by p ",
      "type": "Correct → (V → SUBSET P) ",
      "init": "Initially empty for all p ∈ Correct and v ∈ V "
    },
    "receivedR": {
      "description": "receivedR[p][v] is the set of processes whose READY(v) has been received by p ",
      "type": "Correct → (V → SUBSET P) ",
      "init": "Initially empty for all p ∈ Correct and v ∈ V "
    }
  },
  "Actions": [
    {
      "name": "SendEcho(self)",
      "condition": [
        "self ∈ Correct ",
        "receivedS[self] ∈ V ",
        "∀ v ∈ V : self ∉ receivedE[self][v] "
      ],
      "effect": [
        "∀ p ∈ Correct : receivedE[p][receivedS[self]] := receivedE[p][receivedS[self]] ∪ {self} "
      ]
    },
    {
      "name": "SendReady(self)",
      "condition": [
        "self ∈ Correct ",
        "∀ v ∈ V : self ∉ receivedR[self][v] ",
        "∃ v ∈ V : |receivedE[self][v]| ≥ 2F + 1 OR |receivedR[self][v]| ≥ F + 1 "
      ],
      "effect": [
        "Choose such a v ",
        "∀ p ∈ Correct : receivedR[p][v] := receivedR[p][v] ∪ {self} "
      ]
    },
    {
      "name": "StepCommit(self)",
      "condition": [
        "self ∈ Correct ",
        "delivered[self] = \"\" ",
        "∃ v ∈ V : |receivedR[self][v]| ≥ 2F + 1 "
      ],
      "effect": [
        "Choose such a v ",
        "delivered[self] := v "
      ]
    },
    {
      "name": "ByzantineEcho(self)",
      "condition": [
        "self ∈ Faulty "
      ],
      "effect": [
        "∃ d ∈ Correct, ∃ v ∈ V : self ∉ receivedE[d][v] ∧ receivedE[d][v] := receivedE[d][v] ∪ {self} "
      ]
    },
    {
      "name": "ByzantineReady(self)",
      "condition": [
        "self ∈ Faulty "
      ],
      "effect": [
        "∃ d ∈ Correct, ∃ v ∈ V : self ∉ receivedR[d][v] ∧ receivedR[d][v] := receivedR[d][v] ∪ {self} "
      ]
    },
    {
      "name": "Next",
      "effect": [
        "(∃ self ∈ Correct : SendEcho(self) OR SendReady(self) OR StepCommit(self)) ",
        "OR",
        "(∃ self ∈ Faulty : ByzantineEcho(self) OR ByzantineReady(self)) "
      ],
      "description": "Global step relation: some correct process executes one of its enabled actions, or some faulty process acts. "
    },
    {
      "name": "Spec",
      "effect": [
        "Init ∧ □[Next]_vars ",
        "∀ self ∈ Correct : WF_vars(SendEcho(self) OR SendReady(self) OR StepCommit(self)) "
      ],
      "description": "Full system spec: initial condition, step relation, and weak fairness for correct-process actions. "
    }
  ],
  "Invariants": [
    {
      "name": "TypeInv",
      "description": "All variables remain within their declared types "
    },
    {
      "name": "Consistency",
      "description": "No two correct processes decide different values ",
      "spec_instance": "∀ p, q ∈ Correct : (delivered[p] ≠ \"\" ∧ delivered[q] ≠ \"\") ⇒ delivered[p] = delivered[q] "
    }
  ],
  "Properties": [
    {
      "name": "Totality",
      "description": "If some correct process decides, eventually all correct processes decide ",
      "spec_instance": "(∃ p ∈ Correct : delivered[p] ≠ \"\") ~> (∀ p ∈ Correct : delivered[p] ≠ \"\") "
    },
    {
      "name": "Validity",
      "description": "If the sender is correct, all correct processes eventually decide its value ",
      "spec_instance": "(sender ∈ Correct) ⇒ LET Val == IF sender ∈ Correct THEN receivedS[sender] ELSE \"\" IN ◇(∀ p ∈ Correct : delivered[p] = Val) "
    }
  ],
  "llm_hint": {
    "receivedS": "based on pseudocode, receivedS[p] can be a set of values modeling Byzantine equivocation: the sender may send multiple different PROPOSE messages to the same process",
    "receivedE": "receivedE[p][v] abstracts the set of senders whose ECHO(v) messages have been received by p",
    "receivedR": "receivedR[p][v] abstracts the set of senders whose READY(v) messages have been received by p",
    "Byzantine_model": "Faulty processes may arbitrarily inject ECHO or READY messages for any value to any correct process, limited by anti-stuttering guards",
    "no_message_queue": "Explicit message queues are abstracted away in favor of set-based reception state"
  }
}
```

## 2.Pseudocode:
```pseudocode
Algorithm: Pseudocode for node 𝑖 in ADD for 𝑛 = 3𝑡 + 1
// encoding phase.
input M_i: either M_i = M or M_i = ⊥
if M_i ≠ ⊥ then
    Let M' := [m_1, m_2,...,m_n] := RSEnc(M_i, n, t + 1)
// dispersal phase
if M_i ≠ ⊥ then
    Let m_i^* := m_i
    send ⟨DISPERSE, m_j⟩ to node j for every j = 1, 2,...,n
else
    upon receiving t + 1 identical ⟨DISPERSE, m_i⟩ do
        Let m_i^* := m_i
// reconstruction phase
send ⟨RECONSTRUCT, m_i^*⟩ to all nodes
if M_i ≠ ⊥ then
    output M and return;

Let T := {}
For every ⟨RECONSTRUCT, m_j^*⟩ received from node j, add (j, m_j^*) to T
for 0 ≤ r ≤ t do   // online Error Correction
    Wait till |T| ≥ 2t + r + 1
    Let p_r(·) := RSDec(t + 1, r, T)
    if 2t + 1 elements (j, a) ∈ T satisfy p_r(j) = a then
        output coefficients of p_r(·) as M and return
```

## Corresponding JSON:
```json
{
  "CONSTANTS": {
    "Correct": "Set of correct nodes",
    "Faulty": "Set of Byzantine nodes",
    "Symbols": "Set of symbols used as shares"
  },
  "OPERATORS": {
    "SymbolOf": {
      "description": "Canonical mapping assigning each node its unique share symbol",
      "instance": "SymbolOf == CHOOSE f \\in [P -> Symbols] : \\A p, q \\in P : (p # q) => (f[p] # f[q])"
    }
  },
  "VARIABLES": {
    "receivedS": {
      "description": "Mapping Correct -> BOOLEAN; nodes with receivedS=TRUE are encoders (Mi ≠ ⊥)",
      "init": "receivedS ∈ [Correct -> BOOLEAN] with Cardinality({ p ∈ Correct : receivedS[p] }) ≥ T + 1"
    },
    "mStar": {
      "description": "Each node's reconstructed symbol (\"\" if not yet fixed)",
      "init": "mStar = [ p ∈ P |-> \"\" ]"
    },
    "delivered": {
      "description": "Each correct node's decision output: \"\" or \"M\"",
      "init": "delivered = [ p ∈ Correct |-> \"\" ]"
    },
    "receivedDis": {
      "description": "For each node p and symbol sym, receivedDis[p][sym] is the set of senders who sent sym to p",
      "init": "receivedDis = [ p ∈ P |-> [ sym ∈ Symbols |-> {} ] ]"
    },
    "receivedRec": {
      "description": "For each node p, set of received reconstruct pairs <<src,val>>",
      "init": "receivedRec = [ p ∈ P |-> {} ]"
    },
    "decodeRound": {
      "description": "Current online error-correction round r for each node",
      "init": "decodeRound = [ p ∈ P |-> 0 ]"
    }
  },
  "ACTIONS": [
    {
      "name": "SendDisperse(self)",
      "condition": [
        "self ∈ Correct",
        "receivedS[self] = TRUE",
        "mStar[self] = \"\""
      ],
      "effect": [
        "mStar'[self] = SymbolOf[self]",
        "For all p ∈ P: receivedDis'[p][SymbolOf[p]] = receivedDis[p][SymbolOf[p]] ∪ {self}"
      ]
    },
    {
      "name": "ReceiveDisperse(self)",
      "condition": [
        "self ∈ Correct",
        "receivedS[self] = FALSE",
        "mStar[self] = \"\"",
        "∃ sym ∈ Symbols : Cardinality(receivedDis[self][sym]) ≥ T + 1"
      ],
      "effect": [
        "Let sym0 be a symbol with ≥ T+1 senders; set mStar'[self] = sym0"
      ]
    },
    {
      "name": "SendReconstruct(self)",
      "condition": [
        "self ∈ Correct",
        "mStar[self] ≠ \"\"",
        "No prior <<self, mStar[self]>> appears in receivedRec of any node"
      ],
      "effect": [
        "For all p ∈ P: receivedRec'[p] = receivedRec[p] ∪ {<<self, mStar[self]>>}",
        "If receivedS[self] = TRUE then delivered'[self] = \"M\""
      ]
    },
    {
      "name": "TryDecode(self)",
      "condition": [
        "self ∈ Correct",
        "receivedS[self] = FALSE",
        "delivered[self] = \"\""
      ],
      "effect": [
        "Let r = decodeRound[self]",
        "Require r ≤ T and Cardinality(receivedRec[self]) ≥ 2T + r + 1",
        "Let matching = { p ∈ P : <<p, SymbolOf[p]>> ∈ receivedRec[self] }",
        "If |matching| ≥ 2T + 1 then delivered'[self] = \"M\"",
        "Else if r < T then decodeRound'[self] = r + 1"
      ]
    },
    {
      "name": "ByzantineDisperse(self)",
      "condition": [
        "self ∈ Faulty"
      ],
      "effect": [
        "Choose d ∈ Correct",
        "Let wrongSym be deterministically chosen such that wrongSym ≠ SymbolOf[d]",
        "Add self to receivedDis[d][sym] for some sym ∈ { SymbolOf[d], wrongSym }"
      ]
    },
    {
      "name": "ByzantineReconstruct(self)",
      "condition": [
        "self ∈ Faulty"
      ],
      "effect": [
        "Choose d ∈ Correct",
        "Let wrongSym be deterministically chosen such that wrongSym ≠ SymbolOf[self]",
        "Add <<self, sym>> to receivedRec[d] for some sym ∈ { SymbolOf[self], wrongSym }"
      ]
    },
    {
      "name": "Next",
      "formula": "Disjunction of all enabled actions for correct and faulty nodes",
      "description": "Matches the TLA+ Next definition."
    },
    {
      "name": "Spec",
      "formula": "Init ∧ [][Next]_vars ∧ Fairness",
      "description": "Full system specification with weak fairness for honest actions."
    }
  ],
  "INVARIANTS": [
    {
      "name": "TypeInv",
      "description": "Type correctness of all variables",
      "spec_instance": "receivedS ∈ [Correct → BOOLEAN] ∧ mStar ∈ [P → Symbols ∪ {\"\"}] ∧ delivered ∈ [Correct → {\"\",\"M\"}] ∧ receivedDis ∈ [P → [Symbols → SUBSET P]] ∧ receivedRec ∈ [P → SUBSET (P × Symbols)] ∧ decodeRound ∈ [P → 0..T]"
    },
    {
      "name": "Agreement",
      "description": "No two honest nodes decide different values",
      "spec_instance": "∀ p,q ∈ Correct : (delivered[p] ≠ \"\" ∧ delivered[q] ≠ \"\") ⇒ delivered[p] = delivered[q]"
    }
  ],
  "PROPERTIES": [
    {
      "name": "Termination",
      "description": "Eventually every honest node decides",
      "spec_instance": "◇ (∀ p ∈ Correct : delivered[p] = \"M\")"
    }
  ],
  "llm_hint": {
    "receivedS_semantics": "receivedS[p]=TRUE models nodes with Mi ≠ ⊥ that perform encoding and disperse. Domain restricted to Correct to reduce state space.",
    "disperse_modeling": "receivedDis abstracts message delivery by directly recording sender sets per symbol.",
    "reconstruction_modeling": "receivedRec[p] stores all <<src,val>> pairs received by p.",
    "RS_abstraction": "RSDec is abstracted by cardinality checks against SymbolOf; decoding works up to T rounds.",
    "Byzantine_scope": "Byzantine actions use representative collapse (wrongSym) to severely trim unnecessary state branching while maintaining adversarial severity."
  }
}
```

## 3.Pseudocode:
```pseudocode
Algorithm HoneyBadgerRBC (for party P_i, with sender P_Sender)
upon input(v) (if P_i = P_Sender):
    let {s_j}_{j∈[N]} be the blocks of an (N−2f,N)-erasure coding scheme applied to v
    let h be a Merkle tree root computed over {s_j}
    send VAL(h, b_j, s_j) to each party P_j, where b_j is the j^th Merkle tree branch

upon receiving VAL(h, b_i, s_i) from P_Sender:
    multicast ECHO(h, b_i, s_i)

upon receiving ECHO(h, b_j, s_j) from party P_j:
    check that b_j is a valid Merkle branch for root h and leaf s_j, and otherwise discard

upon receiving valid ECHO(h, ·, ·) messages from N−f distinct parties:
    – interpolate {s'_j} from any N−2f leaves received
    – recompute Merkle root h' and if h' ≠ h then abort
    – if READY(h) has not yet been sent, multicast READY(h)

upon receiving f+1 matching READY(h) messages, if READY has not yet been sent, multicast READY(h)

upon receiving 2f+1 matching READY(h) messages, wait for N−2f ECHO messages, then decode v
```

## Corresponding JSON:
```json
{
  "CONSTANTS": {
    "Correct": "Set of correct (honest) nodes",
    "Faulty": "Set of Byzantine nodes",
    "Symbols": "Set of symbols used as erasure coding shares"
  },
  "OPERATORS": {
    "SymbolOf": {
      "description": "Canonical mapping assigning each node its unique RS share symbol",
      "instance": "SymbolOf == CHOOSE f \\in [P -> Symbols] : \\A p, q \\in P : (p # q) => (f[p] # f[q])"
    },
    "Decode": {
      "description": "Abstracted interpolation decoding function mapping a set of shares and a root to a payload",
      "instance": "Decode(ShardSet, r) == IF r \\in GoodRoots THEN \"M_Good\" ELSE IF SymbolOf[CHOOSE p \\in Correct : TRUE] \\in ShardSet THEN \"M_Bad_1\" ELSE \"M_Bad_2\""
    }
  },
  "VARIABLES": {
    "sender": {
      "description": "The designated sender process (broadcaster)",
      "init": "sender ∈ Faulty (hardcoded for adversarial testing in the current Init)"
    },
    "receivedS": {
      "description": "Mapping Correct -> Roots ∪ {\"\"}; root value received from the sender",
      "init": "If sender ∈ Correct, maps to a chosen v ∈ GoodRoots; else unconstrained in Roots ∪ {\"\"}"
    },
    "receivedE": {
      "description": "receivedE[p] is the set of ECHO messages <<src, root, shard>> received by node p",
      "init": "receivedE = [ p ∈ Correct |-> {} ]"
    },
    "receivedR": {
      "description": "receivedR[p] is the set of READY messages <<src, root>> received by node p",
      "init": "receivedR = [ p ∈ Correct |-> {} ]"
    },
    "delivered": {
      "description": "Each correct node's decision output from Payloads",
      "init": "delivered = [ p ∈ Correct |-> \"\" ]"
    }
  },
  "ACTIONS": [
    {
      "name": "ReceiveValAndEcho(self)",
      "condition": [
        "self ∈ Correct",
        "receivedS[self] ∈ Roots",
        "No prior ECHO message sent by self for receivedS[self]"
      ],
      "effect": [
        "Let r = receivedS[self] and myShard = SymbolOf[self]",
        "For all p ∈ Correct: receivedE'[p] = receivedE[p] ∪ {<<self, r, myShard>>}"
      ]
    },
    {
      "name": "ReceiveEchoAndReady(self)",
      "condition": [
        "self ∈ Correct",
        "∃ r ∈ Roots for which self hasn't sent READY",
        "Cardinality(validEchos) ≥ N - F for root r",
        "r ∈ GoodRoots (Merkle root interpolation check)"
      ],
      "effect": [
        "For all p ∈ Correct: receivedR'[p] = receivedR[p] ∪ {<<self, r>>}"
      ]
    },
    {
      "name": "AmplifyReady(self)",
      "condition": [
        "self ∈ Correct",
        "∃ r ∈ Roots for which self hasn't sent READY",
        "Cardinality(matchingReadys) ≥ F + 1 for root r"
      ],
      "effect": [
        "For all p ∈ Correct: receivedR'[p] = receivedR[p] ∪ {<<self, r>>}"
      ]
    },
    {
      "name": "TryDecode(self)",
      "condition": [
        "self ∈ Correct",
        "delivered[self] = \"\"",
        "∃ r ∈ Roots with ≥ 2F + 1 READYs and ≥ N - 2F valid ECHOs"
      ],
      "effect": [
        "delivered'[self] = Decode({m[3] : m ∈ validEchos}, r)"
      ]
    },
    {
      "name": "ByzantineEcho(self)",
      "condition": [
        "self ∈ Faulty"
      ],
      "effect": [
        "Choose d ∈ Correct and r ∈ Roots",
        "Add <<self, r, SymbolOf[self]>> to receivedE[d]"
      ]
    },
    {
      "name": "ByzantineReady(self)",
      "condition": [
        "self ∈ Faulty"
      ],
      "effect": [
        "Choose d ∈ Correct and r ∈ Roots",
        "Add <<self, r>> to receivedR[d]"
      ]
    },
    {
      "name": "Next",
      "formula": "Disjunction of all enabled actions for correct and faulty nodes",
      "description": "Matches the TLA+ Next definition."
    },
    {
      "name": "Spec",
      "formula": "Init ∧ [][Next]_vars ∧ Fairness",
      "description": "Full system specification with weak fairness for honest actions."
    }
  ],
  "INVARIANTS": [
    {
      "name": "TypeInv",
      "description": "Type correctness of all variables",
      "spec_instance": "sender ∈ P ∧ receivedS ∈ [Correct → Roots ∪ {\"\"}] ∧ receivedE ∈ [Correct → SUBSET (P × Roots × Symbols)] ∧ receivedR ∈ [Correct → SUBSET (P × Roots)] ∧ delivered ∈ [Correct → Payloads]"
    },
    {
      "name": "Consistency",
      "description": "No two honest nodes decide different values",
      "spec_instance": "∀ p, q ∈ Correct : (delivered[p] ≠ \"\" ∧ delivered[q] ≠ \"\") ⇒ delivered[p] = delivered[q]"
    }
  ],
  "PROPERTIES": [
    {
      "name": "Validity",
      "description": "If the sender is correct, all correct nodes eventually decide M_Good",
      "spec_instance": "(sender ∈ Correct) ⇒ ◇(∀ p ∈ Correct : delivered[p] = \"M_Good\")"
    },
    {
      "name": "Totality",
      "description": "If some correct process decides, eventually all correct processes decide",
      "spec_instance": "(∃ p ∈ Correct : delivered[p] ≠ \"\") ~> (∀ p ∈ Correct : delivered[p] ≠ \"\")"
    }
  ],
  "llm_hint": {
    "merkle_root_abstraction": "GoodRoots and BadRoots abstract the Merkle tree validation. r ∈ GoodRoots in ReceiveEchoAndReady simulates the successful h' == h branch interpolation check.",
    "erasure_coding_abstraction": "Valid ECHOs must carry the expected SymbolOf[sender]. Decode() abstracts polynomial interpolation by mapping the shard subset to predefined Payloads.",
    "state_space_optimization": "Message sets receivedE and receivedR use Correct nodes as their domain to reduce state space, and record tuples instead of complex nested mappings."
  }
}
```