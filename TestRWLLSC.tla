----------------------------- MODULE TestRWLLSC -----------------------------
EXTENDS Integers, FiniteSets, TLAPS
CONSTANT N
VARIABLES pc, ll, X, x, v, S, ret
ASSUME NPosInt == N \in Nat \ {0}

vars == <<pc, ll, X, x, v, S, ret>>
Bot == -15
Ack == -20
ProcSet == 1..N

Init == /\ pc \in [ProcSet -> {1, 3}]
        /\ ll = [p \in ProcSet |-> FALSE]
        /\ X = 0
\*        /\ X \in Nat
        /\ x = [p \in ProcSet |-> 0]
\*        /\ x \in [ProcSet -> Nat]
        /\ v \in [ProcSet -> Nat]
        /\ S = X
        /\ ret = [p \in ProcSet |-> Bot]
\*        /\ ret \in [ProcSet -> Nat] ???

\* `^x_p \gets X^'
L1(p) == /\ pc[p] = 1
         /\ pc' = [pc EXCEPT ![p] = 2]
         /\ x' = [x EXCEPT ![p] = X]
         /\ ret' = [ret EXCEPT ![p] = X]
         /\ UNCHANGED <<ll, X, v, S>>

\* `^{\bf return} x_p^'         
L2(p) == /\ pc[p] = 2
         /\ \E Line \in {1, 3} : pc' = [pc EXCEPT ![p] = Line]
         /\ ret' = [ret EXCEPT ![p] = Bot]
         /\ UNCHANGED <<ll, X, x, v, S>>
         
         
\* `^X.LL_p()^'
L3(p) == /\ pc[p] = 3
         /\ pc' = [pc EXCEPT ![p] = 4]
         /\ ll' = [ll EXCEPT ![p] = TRUE]
         /\ UNCHANGED <<X, x, v, S, ret>>

\* `^X.SC_p(v_p)^'
L4(p) == \/ (/\ pc[p] = 4
             /\ ll[p] = TRUE
             /\ pc' = [pc EXCEPT ![p] = 5]
             /\ ll' = [q \in ProcSet |-> FALSE]
             /\ X' = v[p]
             /\ S' = v[p]
             /\ ret' = [q \in ProcSet |-> IF (/\ pc[q] = 4
                                              /\ ll[q] = TRUE) THEN Ack ELSE ret[q]]
             /\ UNCHANGED <<x, v>>)
         \/ (/\ pc[p] = 4
             /\ ll[p] = FALSE
             /\ pc' = [pc EXCEPT ![p] = 5]
             /\ UNCHANGED <<ll, X, x, v, S, ret>>)

\* `^{\bf return} ack^'              
L5(p) == /\ pc[p] = 5
         /\ \E Line \in {1, 3} : pc' = [pc EXCEPT ![p] = Line]
         /\ ret' = [ret EXCEPT ![p] = Bot]
         /\ \E v_pr \in Nat : v' = [v EXCEPT ![p] = v_pr]
         /\ UNCHANGED <<ll, X, x, S>>
         
Step(p) == \/ L1(p)
           \/ L2(p)
           \/ L3(p)
           \/ L4(p)
           \/ L5(p)
           
Next == (\E p \in ProcSet : Step(p))

Spec == /\ Init
        /\ [][Next]_vars
        
\* Invariants

Inv1 == X = S

Inv2 == \A p \in ProcSet : /\ pc[p] \in {1, 3} => ret[p] = Bot
\*                           /\ pc[p] \in {2, 5} => ret[p] /= Bot
                           /\ pc[p] = 2 => ret[p] /= Bot
                           /\ pc[p] = 5 => ret[p] = Ack
                           
Inv3 == \A p \in ProcSet : ((/\ pc[p] = 4
                             /\ ll[p] = TRUE) => ret[p] = Bot)
                             
Inv4 == \A p \in ProcSet : ((/\ pc[p] = 4
                             /\ ll[p] = FALSE) => ret[p] = Ack)
                             
\* Inductive invariant

Lines == {1, 2, 3, 4, 5}

TypeOK == /\ pc \in [ProcSet -> Lines]
          /\ ll \in [ProcSet -> BOOLEAN]
          /\ X \in Nat
          /\ x \in [ProcSet -> Nat]
          /\ v \in [ProcSet -> Nat]
          /\ S \in Nat
          /\ ret \in [ProcSet -> Nat \union {Ack, Bot}]

IInv == /\ TypeOK
        /\ Inv1
        /\ Inv2
        /\ Inv3
        /\ Inv4
        
ISpec == /\ IInv
         /\ [][Next]_vars
         
\* Type correctness

THEOREM TypeCorrectness == Spec => []TypeOK
<1> USE NPosInt DEFS ProcSet, Lines, TypeOK
<1>1. Init => TypeOK
  PROOF BY DEF Init
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW p \in ProcSet,
               L1(p)
        PROVE  TypeOK'
    PROOF BY <2>1 DEF Next, vars, Step, L1, L2, L3, L4, L5
  <2>2. ASSUME NEW p \in ProcSet,
               L2(p)
        PROVE  TypeOK'
    PROOF BY <2>2 DEF Next, vars, Step, L1, L2, L3, L4, L5
  <2>3. ASSUME NEW p \in ProcSet,
               L3(p)
        PROVE  TypeOK'
    PROOF BY <2>3 DEF Next, vars, Step, L1, L2, L3, L4, L5
  <2>4. ASSUME NEW p \in ProcSet,
               L4(p)
        PROVE  TypeOK'
    <3>1. CASE /\ pc[p] = 4
               /\ ll[p] = TRUE
               /\ pc' = [pc EXCEPT ![p] = 5]
               /\ ll' = [q \in ProcSet |-> FALSE]
               /\ X' = v[p]
               /\ S' = v[p]
               /\ ret' = [q \in ProcSet |-> IF (/\ pc[q] = 4
                                                /\ ll[q] = TRUE) THEN Ack ELSE ret[q]]
               /\ UNCHANGED <<x, v>>
      PROOF BY <3>1, <2>4 DEF Next, vars, Step, L1, L2, L3, L4, L5
    <3>2. CASE /\ pc[p] = 4
               /\ ll[p] = FALSE
               /\ pc' = [pc EXCEPT ![p] = 5]
               /\ UNCHANGED <<ll, X, x, v, S, ret>>
      PROOF BY <3>2, <2>4 DEF Next, vars, Step, L1, L2, L3, L4, L5
    <3>3. QED
      BY <2>4, <3>1, <3>2 DEF L4
    
  <2>5. ASSUME NEW p \in ProcSet,
               L5(p)
        PROVE  TypeOK'
    PROOF BY <2>5 DEF Next, vars, Step, L1, L2, L3, L4, L5
  <2>6. CASE UNCHANGED vars
    PROOF BY <2>6 DEF Next, vars, Step, L1, L2, L3, L4, L5
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, Step
<1>3. QED
  PROOF BY <1>1, <1>2, PTL DEF Spec
  

THEOREM Spec => []IInv
<1> USE NPosInt DEFS ProcSet, Lines, TypeOK, IInv, Inv1, Inv2, Inv3, Inv4, Bot, Ack
<1>1. Init => IInv
  PROOF BY DEF Init
<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>1. ASSUME NEW p \in ProcSet,
               L1(p)
        PROVE  IInv'
    PROOF BY <2>1 DEF Next, vars, L1, L2, L3, L4, L5  
  <2>2. ASSUME NEW p \in ProcSet,
               L2(p)
        PROVE  IInv'
    PROOF BY <2>2 DEF Next, vars, L1, L2, L3, L4, L5
  <2>3. ASSUME NEW p \in ProcSet,
               L3(p)
        PROVE  IInv'
    PROOF BY <2>3 DEF Next, vars, L1, L2, L3, L4, L5
  <2>4. ASSUME NEW p \in ProcSet,
               L4(p)
        PROVE  IInv'
    <3>1. CASE /\ pc[p] = 4
               /\ ll[p] = TRUE
               /\ pc' = [pc EXCEPT ![p] = 5]
               /\ ll' = [q \in ProcSet |-> FALSE]
               /\ X' = v[p]
               /\ S' = v[p]
               /\ ret' = [q \in ProcSet |-> IF (/\ pc[q] = 4
                                                /\ ll[q] = TRUE) THEN Ack ELSE ret[q]]
               /\ UNCHANGED <<x, v>>
      PROOF BY <3>1, <2>4 DEF Next, vars, L1, L2, L3, L4, L5
    <3>2. CASE /\ pc[p] = 4
               /\ ll[p] = FALSE
               /\ pc' = [pc EXCEPT ![p] = 5]
               /\ UNCHANGED <<ll, X, x, v, S, ret>>
      PROOF BY <3>2, <2>4 DEF Next, vars, L1, L2, L3, L4, L5
    <3>3. QED
      BY <2>4, <3>1, <3>2 DEF L4
    
  <2>5. ASSUME NEW p \in ProcSet,
               L5(p)
        PROVE  IInv'
    PROOF BY <2>5 DEF Next, vars, L1, L2, L3, L4, L5
  <2>6. CASE UNCHANGED vars
    PROOF BY <2>6 DEF Next, vars, L1, L2, L3, L4, L5
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, Step
  
<1>3. QED
  PROOF BY <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Wed May 05 00:04:45 EDT 2021 by uguryavuz
\* Created Tue May 04 21:45:09 EDT 2021 by uguryavuz
