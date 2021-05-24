------------------------------ MODULE T_RWCAS ------------------------------
EXTENDS Integers, FiniteSets, TLAPS
CONSTANT N
VARIABLES pc, X, x, v, T
ASSUME NPosInt == N \in Nat \ {0}

vars == <<pc, X, x, v, T>>
ProcSet == 1..N
Bot == -15
Ack == -20

Init   == /\ pc \in [ProcSet -> {1, 4}]
          /\ X \in Nat
          /\ x \in [ProcSet -> Nat]
          /\ v \in [ProcSet -> Nat]
          /\ T = {[State |-> X, 
                   Ret |-> [p \in ProcSet |-> Bot]]}
          
Inv01  == T /= {}
Inv02  == \A t \in T : t.State = X
Inv03  == \E t \in T : (\A q \in ProcSet : pc[q] = 3 => t.Ret[q] = Ack)     
          
Inv1   == \A p \in ProcSet : pc[p] = 1 => (\A t \in T : t.Ret[p] = Bot)

L1(p)  == /\ pc[p] = 1
          /\ pc' = [pc EXCEPT ![p] = 2]
          /\ x' = [x EXCEPT ![p] = X]
          /\ UNCHANGED <<X, v, T>>
          
Inv21  == \A p \in ProcSet : pc[p] = 2 => (\E t \in T : t.Ret[p] = Bot)
Inv22  == \A p \in ProcSet : pc[p] = 2 => (X /= x[p] => (\E t \in T : t.Ret[p] = Ack))
Inv25  == \A p \in ProcSet : pc[p] = 2 => (X /= x[p] 
                                             => (\A t \in T : t.Ret[p] = Bot
                                                              => (\E u \in T : u = [State |-> t.State, 
                                                                                    Ret |-> [t.Ret EXCEPT ![p] = Ack]])))
Inv23  == \A p \in ProcSet : pc[p] = 2 => (\A t \in T : t.Ret[p] \in {Bot, Ack})
Inv24  == \A p \in ProcSet : pc[p] = 2 => (\A t \in T : t.Ret[p] = Ack 
                                                        => (\E u \in T : u = [State |-> t.State, 
                                                                              Ret |-> [t.Ret EXCEPT ![p] = Bot]]))

L2(p)  == \/ (/\ pc[p] = 2
              /\ X = x[p]
              /\ pc' = [pc EXCEPT ![p] = 3]
              /\ X' = v[p]
              /\ T' = {u \in [State : {v[p]}, 
                              Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                         /\ u.Ret[p] = Ack
                         /\ u.State = v[p]
                         /\ (\E t \in T : /\ t.Ret[p] = Bot
                                          /\ t.State = x[p]
                                          /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                      \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                 /\ (/\ pc[q] = 2
                                                                     /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
              /\ UNCHANGED <<x, v>>)
          \/ (/\ pc[p] = 2
              /\ X /= x[p]
              /\ pc' = [pc EXCEPT ![p] = 3]
              /\ UNCHANGED <<X, x, v, T>>)
              
Inv3   == \A p \in ProcSet : pc[p] = 3 => (\E t \in T : t.Ret[p] = Ack)

L3(p)  == /\ pc[p] = 3
          /\ \E LineNum \in {1, 4} : pc' = [pc EXCEPT ![p] = LineNum]
          /\ \E vNew \in Nat : v' = [v EXCEPT ![p] = vNew]
          /\ T' = {[State |-> t.State, Ret |-> [t.Ret EXCEPT ![p] = Bot]] : t \in {u \in T : u.Ret[p] = Ack}}
          /\ UNCHANGED <<X, x>>
          
Inv4   == \A p \in ProcSet : pc[p] = 4 => (\A t \in T : t.Ret[p] = Bot) 

L4(p)  == /\ pc[p] = 4
          /\ pc' = [pc EXCEPT ![p] = 5]
          /\ x' = [x EXCEPT ![p] = X]
          /\ T' = {[State |-> t.State, Ret |-> [t.Ret EXCEPT ![p] = X]] : t \in T}
          /\ UNCHANGED <<X, v>>
          
Inv5   == \A p \in ProcSet : pc[p] = 5 => (\A t \in T : t.Ret[p] = x[p])

L5(p)  == /\ pc[p] = 5
          /\ \E LineNum \in {1, 4} : pc' = [pc EXCEPT ![p] = LineNum]
          /\ T' = {[State |-> t.State, Ret |-> [t.Ret EXCEPT ![p] = Bot]] : t \in T}
          /\ UNCHANGED <<X, x, v>>
          
\* Algorithm

Step(p) == \/ L1(p)
           \/ L2(p)
           \/ L3(p)
           \/ L4(p)
           \/ L5(p)
           
Next    == \E p \in ProcSet : Step(p)

Spec    == /\ Init
           /\ [][Next]_vars
           
\* Inductive Invariance

Lines  == {1, 2, 3, 4, 5}
        
TypeOK == /\ pc \in [ProcSet -> Lines]
          /\ X \in Nat
          /\ x \in [ProcSet -> Nat]
          /\ v \in [ProcSet -> Nat]
          /\ T \in SUBSET [State : Nat, Ret : [ProcSet -> Nat \cup {Bot, Ack}]]

IInv   == /\ TypeOK
          /\ Inv01
          /\ Inv02
          /\ Inv1
          /\ Inv21
          /\ Inv22
          /\ Inv23
          /\ Inv24
          /\ Inv3
          /\ Inv4
          /\ Inv5
          /\ Inv25
          /\ Inv03
          
ISpec  == /\ IInv
          /\ [][Next]_vars
          
\* WARNING: Cannot feasibly model check, because T \in SUBSET [...]

\*THEOREM TypeCorrectness == Spec => []TypeOK
\*<1> USE NPosInt DEFS ProcSet, Lines, TypeOK, Bot, Ack
\*<1> SUFFICES /\ (Init => TypeOK)
\*             /\ (TypeOK /\ [Next]_vars => TypeOK')
\*      PROOF BY PTL DEF Spec
\*<1>1. Init => TypeOK
\*  PROOF BY DEF Init
\*<1>2. TypeOK /\ [Next]_vars => TypeOK'
\*  <2> SUFFICES ASSUME TypeOK,
\*                      [Next]_vars
\*               PROVE  TypeOK'
\*    OBVIOUS
\*  <2>1. ASSUME NEW p \in ProcSet,
\*               L1(p)
\*        PROVE  TypeOK'
\*    PROOF BY <2>1 DEF L1
\*  <2>2. ASSUME NEW p \in ProcSet,
\*               L2(p)
\*        PROVE  TypeOK'
\*    PROOF BY <2>2 DEF L2
\*  <2>3. ASSUME NEW p \in ProcSet,
\*               L3(p)
\*        PROVE  TypeOK'
\*    PROOF BY <2>3 DEF L3
\*  <2>4. ASSUME NEW p \in ProcSet,
\*               L4(p)
\*        PROVE  TypeOK'
\*    PROOF BY <2>4 DEF L4
\*  <2>5. ASSUME NEW p \in ProcSet,
\*               L5(p)
\*        PROVE  TypeOK'
\*    PROOF BY <2>5 DEF L5
\*  <2>6. CASE UNCHANGED vars
\*    PROOF BY <2>6 DEF vars
\*  <2>7. QED
\*    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, Step
\*<1>3. QED
\*  PROOF BY <1>1, <1>2

THEOREM Spec => []TypeOK
<1> USE NPosInt DEFS ProcSet, Lines, Bot, Ack, TypeOK
<1>1. Init => TypeOK
  BY DEF Init
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW p \in ProcSet,
               L1(p)
        PROVE  TypeOK'
    BY <2>1 DEF L1
  <2>2. ASSUME NEW p \in ProcSet,
               L2(p)
        PROVE  TypeOK'
    BY <2>2 DEF L2
  <2>3. ASSUME NEW p \in ProcSet,
               L3(p)
        PROVE  TypeOK'
    BY <2>3 DEF L3
  <2>4. ASSUME NEW p \in ProcSet,
               L4(p)
        PROVE  TypeOK'
    BY <2>4 DEF L4
  <2>5. ASSUME NEW p \in ProcSet,
               L5(p)
        PROVE  TypeOK'
    <3>1. SUFFICES ASSUME NEW LineNum \in {1, 4},
                        pc' = [pc EXCEPT ![p] = LineNum]
                   PROVE  TypeOK'
      BY <2>5 DEF L5
    <3> QED
      BY <2>5, <3>1 DEF L5
    
  <2>6. CASE UNCHANGED vars
    BY <2>6 DEF Next, vars, L1, L2, L3, L4, L5
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, Step
  
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []IInv
<1> USE NPosInt DEFS ProcSet, Lines, Bot, Ack, IInv
<1> SUFFICES /\ (Init => IInv)
             /\ (IInv /\ [Next]_vars => IInv')
      PROOF BY PTL DEF Spec
<1>1. Init => IInv
  <2> SUFFICES ASSUME Init
               PROVE  IInv
    OBVIOUS
  <2>1. TypeOK
    PROOF BY DEF Init, TypeOK
  <2>2. Inv01
    PROOF BY Isa DEF Init, Inv01
  <2>3. Inv02
    PROOF BY DEF Init, Inv02
  <2>4. Inv1
    PROOF BY DEF Init, Inv1
  <2>5. Inv21
    PROOF BY DEF Init, Inv21
  <2>6. Inv22
    PROOF BY DEF Init, Inv22
  <2>7. Inv23
    PROOF BY DEF Init, Inv23
  <2>8. Inv24
    PROOF BY DEF Init, Inv24
  <2>9. Inv3
    PROOF BY DEF Init, Inv3
  <2>10. Inv4
    PROOF BY DEF Init, Inv4
  <2>11. Inv5
    PROOF BY DEF Init, Inv5
  <2>12. Inv03
    PROOF BY DEF Init, Inv03
  <2>13. Inv25
    PROOF BY DEF Init, Inv25
  <2>14. QED
    BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF IInv  
<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv /\ [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2> USE DEF Next, Step, vars
  <2>1. TypeOK'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  TypeOK'
      PROOF BY <3>1 DEF TypeOK, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  TypeOK'
      PROOF BY <3>2 DEF TypeOK, L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  TypeOK'
      PROOF BY <3>3 DEF TypeOK, L3
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  TypeOK'
      PROOF BY <3>4 DEF TypeOK, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  TypeOK'
      PROOF BY <3>5 DEF TypeOK, L5
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF TypeOK, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step  
  <2>2. Inv01'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv01'
      PROOF BY <3>1 DEF Inv01, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv01'
      <4>1. CASE /\ pc[p] = 2
                 /\ X = x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ X' = v[p]
                 /\ T' = {u \in [State : {v[p]}, 
                                 Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                            /\ u.Ret[p] = Ack
                            /\ u.State = v[p]
                            /\ (\E t \in T : /\ t.Ret[p] = Bot
                                             /\ t.State = x[p]
                                             /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                         \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                    /\ (/\ pc[q] = 2
                                                                        /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
                 /\ UNCHANGED <<x, v>>
        <5>1. PICK t \in T : t.Ret[p] = Bot /\ t.State = x[p]
          BY <4>1 DEF Inv02, Inv21
        <5>.  DEFINE u == [State |-> v[p],
                           Ret |-> [[q \in ProcSet |-> IF pc[q] = 2 /\ t.Ret[q] /= Ack 
                                                          THEN Bot 
                                                          ELSE t.Ret[q]] EXCEPT ![p] = Ack]]
        <5>2. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
              /\ u.State = v[p]
              /\ u.Ret[p] = Ack
          BY DEF TypeOK
        <5>3. \A q \in ProcSet : /\ (q /= p) => IF pc[q] = 2 /\ t.Ret[q] /= Ack 
                                                   THEN u.Ret[q] \in {Bot, Ack}
                                                   ELSE u.Ret[q] = t.Ret[q]
                                 /\ (q = p)  => u.Ret[q] = Ack
          OBVIOUS
        <5>4. \A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                      \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                 /\ (/\ pc[q] = 2
                                     /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}
          BY <4>1, <5>2, <5>3
        <5>5. u \in T'
          BY <4>1, <5>1, <5>2, <5>4, Zenon
        <5>6. QED
          BY <5>5 DEF Inv01
      <4>2. CASE /\ pc[p] = 2
                 /\ X /= x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ UNCHANGED <<X, x, v, T>>
        PROOF BY <4>2 DEF Inv01
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv01'
      <4>1. PICK t \in T : t.Ret[p] = Ack
        BY <3>3 DEF L3, Inv03
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = Bot]]
      <4>2. u \in T'
        BY <3>3, <4>1, Zenon DEF L3 
      <4> QED
        BY <4>2 DEF Inv01
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv01'
      PROOF BY <3>4, Isa DEF Inv01, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv01'
      PROOF BY <3>5, Isa DEF Inv01, L5
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF Inv01, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step
  <2>3. Inv02'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv02'
      PROOF BY <3>1, Isa DEF Inv02, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv02'
      PROOF BY <3>2, Isa DEF Inv02, L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv02'
      PROOF BY <3>3, Isa DEF Inv02, L3
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv02'
      PROOF BY <3>4, Isa DEF Inv02, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv02'
      PROOF BY <3>5, Isa DEF Inv02, L5
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6, Isa DEF Inv02, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step  
  <2>4. Inv1'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv1'
      PROOF BY <3>1 DEF TypeOK, Inv1, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv1'
      PROOF BY <3>2 DEF TypeOK, Inv1, L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv1'
      PROOF BY <3>3 DEF TypeOK, Inv1, L3
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv1'
      PROOF BY <3>4 DEF TypeOK, Inv1, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv1'
      PROOF BY <3>5 DEF TypeOK, Inv1, L5
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF TypeOK, Inv1, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step  
  <2>5. Inv21'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv21'
      PROOF BY <3>1 DEF L1, Inv01, Inv1, Inv21
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv21'
      <4>1. CASE /\ pc[p] = 2
                 /\ X = x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ X' = v[p]
                 /\ T' = {u \in [State : {v[p]}, 
                                 Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                            /\ u.Ret[p] = Ack
                            /\ u.State = v[p]
                            /\ (\E t \in T : /\ t.Ret[p] = Bot
                                             /\ t.State = x[p]
                                             /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                         \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                    /\ (/\ pc[q] = 2
                                                                        /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
                 /\ UNCHANGED <<x, v>>
        <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                            (pc[p_1] = 2)'
                     PROVE  (\E t \in T : t.Ret[p_1] = Bot)'
          BY DEF Inv21
        <5>1. PICK t \in T : /\ t.Ret[p] = Bot 
                             /\ t.State = x[p]
          BY <4>1 DEF Inv02, Inv21
        <5>2. /\ pc[p_1] = 2
              /\ p_1 \in ProcSet
              /\ p_1 /= p
              /\ t.Ret[p_1] \in {Bot, Ack}
          BY <4>1 DEF L2, TypeOK, Inv23
        <5>   DEFINE t_1 == [State |-> t.State,
                             Ret |-> [t.Ret EXCEPT ![p_1] = Bot]]
        <5>3. t.Ret[p_1] /= Bot => /\ t_1 \in T
                                   /\ t_1.Ret[p] = Bot
                                   /\ t_1.State = x[p]
          BY <5>1, <5>2 DEF Inv24                       
        <5>4. \E t_ \in T : /\ t_.Ret[p] = Bot
                            /\ t_.Ret[p_1] = Bot
                            /\ t_.State = x[p]
          BY <5>1, <5>2, <5>3 DEF TypeOK
        <5>  PICK t_2 \in T: /\ t_2.Ret[p] = Bot
                             /\ t_2.Ret[p_1] = Bot
                             /\ t_2.State = x[p]
          BY <5>4
        <5>  DEFINE u == [State |-> v[p],
                          Ret |-> [[q \in ProcSet |-> IF pc[q] = 2 /\ t_2.Ret[q] /= Ack 
                                                         THEN Bot 
                                                         ELSE t_2.Ret[q]] EXCEPT ![p] = Ack]]
        <5>5. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
              /\ u.State = v[p]
              /\ u.Ret[p] = Ack
              /\ u.Ret[p_1] = Bot
          BY <5>2 DEF TypeOK
        <5>6. \A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                      \/ t_2.Ret[q] = Ack) => u.Ret[q] = t_2.Ret[q])
                                 /\ (/\ pc[q] = 2
                                     /\ t_2.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}
          BY <4>1
        <5>7. u \in T'
          BY <4>1, <5>5, <5>6, Zenon
        <5>8. QED
          BY <5>5, <5>7 DEF Inv21

      <4>2. CASE /\ pc[p] = 2
                 /\ X /= x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ UNCHANGED <<X, x, v, T>>
        PROOF BY <4>2, <3>2 DEF L2, Inv21
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2   
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv21'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)'
                   PROVE  (\E t \in T : t.Ret[p_1] = Bot)'
        BY DEF Inv21
        <4>1. PICK t \in T : t.Ret[p] = Ack
          BY <3>3 DEF L3, Inv3
        <4>2. t.Ret[p_1] = Ack => \E t_ \in T : t_ = [State |-> t.State,
                                                      Ret |-> [t.Ret EXCEPT ![p_1] = Bot]]
          BY <3>3 DEF L3, Inv24
        <4>3. PICK t_ \in T : /\ t_.Ret[p] = Ack 
                              /\ t_.Ret[p_1] = Bot
          BY <3>3, <4>1, <4>2 DEF L3, Inv23, TypeOK
        <4>   DEFINE u_ == [State |-> t_.State,
                            Ret |-> [t_.Ret EXCEPT ![p] = Bot]]
        <4>4. u_ \in T'
          BY <3>3, <4>3 DEF L3
        <4>5. u_.Ret[p_1] = Bot
          BY <3>3, <4>3 DEF L3
        <4>6. QED
          PROOF BY <4>4, <4>5, Zenon
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv21'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)'
                   PROVE  (\E t \in T : t.Ret[p_1] = Bot)'
        BY DEF Inv21
      <4>1. PICK t \in T : t.Ret[p_1] = Bot
        BY <3>4 DEF L4, Inv21
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = X]]
      <4>2. u \in T'
        BY <3>4, Zenon DEF L4
      <4>3. u.Ret[p_1] = Bot
        BY <3>4, <4>1 DEF L4
      <4>4. QED
        PROOF BY <4>2, <4>3, Zenon
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv21'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)'
                   PROVE  (\E t \in T : t.Ret[p_1] = Bot)'
        BY DEF Inv21
      <4>1. PICK t \in T : t.Ret[p_1] = Bot
        BY <3>5 DEF L5, Inv21
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = Bot]]
      <4>2. u \in T'
        BY <3>5, Zenon DEF L5
      <4>3. u.Ret[p_1] = Bot
        BY <3>5, <4>1 DEF L5
      <4>4. QED
        PROOF BY <4>2, <4>3, Zenon
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF vars, Inv21
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step
  <2>6. Inv22'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv22'
      PROOF BY <3>1 DEF L1, TypeOK, Inv22
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv22'
      <4>1. CASE /\ pc[p] = 2
                 /\ X = x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ X' = v[p]
                 /\ T' = {u \in [State : {v[p]}, 
                                 Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                            /\ u.Ret[p] = Ack
                            /\ u.State = v[p]
                            /\ (\E t \in T : /\ t.Ret[p] = Bot
                                             /\ t.State = x[p]
                                             /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                         \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                    /\ (/\ pc[q] = 2
                                                                        /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
                 /\ UNCHANGED <<x, v>>
        <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                            (pc[p_1] = 2)',
                            (X /= x[p_1])'
                     PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
          BY DEF Inv22
\*        <5> p /= p_1
\*          BY <4>1 DEF L2, TypeOK
\*        <5> x[p_1] /= v[p]
\*          BY <3>2, <4>1 DEF L2, TypeOK
        <5>1. PICK t \in T : /\ t.Ret[p] = Bot 
                             /\ t.State = x[p]
          BY <4>1 DEF Inv02, Inv21
        <5>2. /\ pc[p_1] = 2
              /\ p_1 \in ProcSet
              /\ p_1 /= p
              /\ t.Ret[p_1] \in {Bot, Ack}
          BY <4>1 DEF L2, TypeOK, Inv23
        <5>   DEFINE t_1 == [State |-> t.State,
                             Ret |-> [t.Ret EXCEPT ![p_1] = Bot]]
        <5>3. t.Ret[p_1] /= Bot => /\ t_1 \in T
                                   /\ t_1.Ret[p] = Bot
                                   /\ t_1.State = x[p]
          BY <5>1, <5>2 DEF Inv24                       
        <5>4. \E t_ \in T : /\ t_.Ret[p] = Bot
                            /\ t_.Ret[p_1] = Bot
                            /\ t_.State = x[p]
          BY <5>1, <5>2, <5>3 DEF TypeOK
        <5>  PICK t_2 \in T: /\ t_2.Ret[p] = Bot
                             /\ t_2.Ret[p_1] = Bot
                             /\ t_2.State = x[p]
          BY <5>4
        <5>  DEFINE u == [State |-> v[p],
                          Ret |-> [[[q \in ProcSet |-> IF pc[q] = 2 /\ t_2.Ret[q] /= Ack 
                                                         THEN Bot 
                                                         ELSE t_2.Ret[q]] EXCEPT ![p] = Ack] EXCEPT ![p_1] = Ack]]
        <5>5. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
              /\ u.State = v[p]
              /\ u.Ret[p] = Ack
              /\ u.Ret[p_1] = Ack
          BY <5>2 DEF TypeOK, Zenon
        <5>6. \A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                      \/ t_2.Ret[q] = Ack) => u.Ret[q] = t_2.Ret[q])
                                 /\ (/\ pc[q] = 2
                                     /\ t_2.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}
          BY <3>2, <4>1 DEF L2, TypeOK
        <5>7. u \in T'
          BY <4>1, <5>5, <5>6, Zenon
        <5>8. QED
          BY <5>5, <5>7 DEF Inv22
        
      <4>2. CASE /\ pc[p] = 2
                 /\ X /= x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ UNCHANGED <<X, x, v, T>>
        PROOF BY <4>2, <3>2 DEF L2, TypeOK, Inv22
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2     
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv22'
        <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          (X /= x[p_1])'
                     PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
          BY DEF Inv22
        <4>1. PICK t \in T : t.Ret[p] = Ack
          BY <3>3 DEF L3, Inv3
        <4>2. t.Ret[p_1] = Bot => \E t_ \in T : t_ = [State |-> t.State,
                                                      Ret |-> [t.Ret EXCEPT ![p_1] = Ack]]
          BY <3>3 DEF L3, Inv25
        <4>3. PICK t_ \in T : /\ t_.Ret[p] = Ack 
                              /\ t_.Ret[p_1] = Ack
          BY <3>3, <4>1, <4>2 DEF L3, Inv23, TypeOK
        <4>   DEFINE u_ == [State |-> t_.State,
                            Ret |-> [t_.Ret EXCEPT ![p] = Bot]]
        <4>4. u_ \in T'
          BY <3>3, <4>3, Zenon DEF L3
        <4>5. u_.Ret[p_1] = Ack
          BY <3>3, <4>3 DEF L3
        <4>6. QED
          PROOF BY <4>4, <4>5, Zenon
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv22'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          (X /= x[p_1])'
                   PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
        BY DEF Inv22
      <4>1. PICK t \in T : t.Ret[p_1] = Ack
        BY <3>4 DEF L4, TypeOK, Inv22
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = X]]
      <4>2. u \in T'
        BY <3>4, Zenon DEF L4
      <4>3. u.Ret[p_1] = Ack
        BY <3>4, <4>1 DEF L4
      <4>4. QED
        PROOF BY <4>2, <4>3, Zenon
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv22'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          (X /= x[p_1])'
                   PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
        BY DEF Inv22
      <4>1. PICK t \in T : t.Ret[p_1] = Ack
        BY <3>5 DEF L5, TypeOK, Inv22
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = Bot]]
      <4>2. u \in T'
        BY <3>5, Zenon DEF L5
      <4>3. u.Ret[p_1] = Ack
        BY <3>5, <4>1 DEF L5
      <4>4. QED
        PROOF BY <4>2, <4>3, Zenon
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF vars, TypeOK, Inv22
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step
  <2>7. Inv23'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv23'
      PROOF BY <3>1 DEF TypeOK, Inv1, Inv23, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv23'
      PROOF BY <3>2 DEF TypeOK, Inv23, L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv23'
      PROOF BY <3>3 DEF TypeOK, Inv23, L3
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv23'
      PROOF BY <3>4 DEF TypeOK, Inv23, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv23'
      PROOF BY <3>5 DEF TypeOK, Inv23, L5
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF TypeOK, Inv23, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step  
  <2>8. Inv24'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv24'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          NEW t \in T',
                          (t.Ret[p_1] = Ack)'
                   PROVE  (\E u \in T : u = [State |-> t.State, 
                                         Ret |-> [t.Ret EXCEPT ![p_1] = Bot]])'
        BY DEF Inv24
      <4>1. /\ T = T'
            /\ pc[p_1] = 2
        BY <3>1 DEF L1, TypeOK, Inv1
      <4>2. PICK u \in T : u = [State |-> t.State,
                                Ret |-> [t.Ret EXCEPT ![p_1] = Bot]]
        BY <4>1 DEF Inv24
      <4>4. QED
        BY <4>1, <4>2
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv24'
      <4>1. CASE /\ pc[p] = 2
                 /\ X = x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ X' = v[p]
                 /\ T' = {u \in [State : {v[p]}, 
                                 Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                            /\ u.Ret[p] = Ack
                            /\ u.State = v[p]
                            /\ (\E t \in T : /\ t.Ret[p] = Bot
                                             /\ t.State = x[p]
                                             /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                         \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                    /\ (/\ pc[q] = 2
                                                                        /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
                 /\ UNCHANGED <<x, v>>
        <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                            (pc[p_1] = 2)',
                            NEW t_pr \in T',
                            (t_pr.Ret[p_1] = Ack)'
                     PROVE  \E u \in T' : u = [State |-> t_pr.State, 
                                               Ret |-> [t_pr.Ret EXCEPT ![p_1] = Bot]]
          BY DEF Inv24
        <5>   DEFINE u == [State |-> t_pr.State,
                           Ret |-> [t_pr.Ret EXCEPT ![p_1] = Bot]]
        <5>1. PICK t_ \in T : /\ t_.Ret[p] = Bot
                              /\ t_.State = x[p]
                              /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                          \/ t_.Ret[q] = Ack) => t_pr.Ret[q] = t_.Ret[q])
                                                     /\ (/\ pc[q] = 2
                                                         /\ t_.Ret[q] /= Ack) => t_pr.Ret[q] \in {Bot, Ack})
          BY <4>1
        <5>2. /\ t_.Ret[p_1] \in {Bot, Ack}
              /\ t_.Ret[p_1] = Ack => \E t_1 \in T : t_1 = [State |-> t_.State,
                                                            Ret |-> [t_.Ret EXCEPT ![p_1] = Bot]]
          BY <4>1 DEF L2, Inv23, Inv24
        <5>  DEFINE u_ == [State |-> t_.State,
                           Ret |-> [t_.Ret EXCEPT ![p_1] = Bot]]
        <5>3. /\ u_ \in T
              /\ u_.Ret[p] = Bot
              /\ u_.State = x[p]
          BY <5>1, <5>2 DEF L2, Inv24, TypeOK
        <5>4. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
              /\ u.State = v[p]
              /\ u.Ret[p] = Ack
          BY <4>1 DEF L2, TypeOK
        <5>5. \A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                      \/ u_.Ret[q] = Ack) => u.Ret[q] = u_.Ret[q])
                                 /\ (/\ pc[q] = 2
                                     /\ u_.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}
          BY <5>1, <5>4 DEF TypeOK
        <5>6. /\ u_ \in T
              /\ u_.Ret[p] = Bot
              /\ u_.State = x[p]
              /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                          \/ u_.Ret[q] = Ack) => u.Ret[q] = u_.Ret[q])
                                     /\ (/\ pc[q] = 2
                                         /\ u_.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack})
          BY <5>3, <5>4, <5>5
        <5>7. (\E t \in T : /\ t.Ret[p] = Bot
                            /\ t.State = x[p]
                            /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                        \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                   /\ (/\ pc[q] = 2
                                                       /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))
          BY <5>6
        <5>8. u \in T'
          BY <4>1, <5>4, <5>7, Isa DEF TypeOK, L2 
        <5> QED
          BY <5>8 DEF Inv24
      <4>2. CASE /\ pc[p] = 2
                 /\ X /= x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ UNCHANGED <<X, x, v, T>>
        PROOF BY <4>2, <3>2 DEF TypeOK, Inv24, L2
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2
      
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv24'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          NEW t \in T',
                          (t.Ret[p_1] = Ack)'
                   PROVE  (\E u \in T : u = [State |-> t.State, 
                                             Ret |-> [t.Ret EXCEPT ![p_1] = Bot]])'
        BY DEF Inv24
      <4>   DEFINE t_ == [State |-> t.State,
                          Ret |-> [t.Ret EXCEPT ![p] = Ack]]
      <4>1. t_ \in T
        BY <3>3, Z3 DEF L3, TypeOK
      <4>2. PICK u_ \in T : u_ = [State |-> t_.State,
                                  Ret |-> [t_.Ret EXCEPT ![p_1] = Bot]]
        BY <3>3, <4>1 DEF L3, Inv24
      <4>3. u_ \in {u \in T : u.Ret[p] = Ack}
        BY <4>2 DEF TypeOK
      <4>4. PICK u \in T' : u = [State |-> u_.State,
                                 Ret |-> [u_.Ret EXCEPT ![p] = Bot]]
        BY <3>3, <4>3, Zenon DEF L3
      <4>5. QED
        BY <4>2, <4>4
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv24'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          NEW t \in T',
                          (t.Ret[p_1] = Ack)'
                   PROVE  (\E u \in T : u = [State |-> t.State, 
                                             Ret |-> [t.Ret EXCEPT ![p_1] = Bot]])'
        BY DEF Inv24
        <4>  DEFINE t_ == [State |-> t.State,
                           Ret |-> [t.Ret EXCEPT ![p] = Bot]]
        <4>1. t_ \in T
          BY <3>4, Z3 DEF TypeOK, Inv4, L4
        <4>2. PICK u_ \in T : u_ = [State |-> t_.State,
                                    Ret |-> [t_.Ret EXCEPT ![p_1] = Bot]]
          BY <3>4, <4>1 DEF Inv24, L4
        <4>   DEFINE u == [State |-> u_.State,
                           Ret |-> [u_.Ret EXCEPT ![p] = X]]
        <4>3. u \in T'
          BY <3>4, <4>1, Zenon DEF L4
        <4>4. u = [State |-> t.State,
                   Ret |-> [t.Ret EXCEPT ![p_1] = Bot]]
          BY <4>2, <4>3 DEF TypeOK
        <4>5. QED
          BY <4>3, <4>4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv24'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          NEW t \in T',
                          (t.Ret[p_1] = Ack)'
                   PROVE  (\E u \in T : u = [State |-> t.State, 
                                             Ret |-> [t.Ret EXCEPT ![p_1] = Bot]])'
        BY DEF Inv24
        <4>  DEFINE t_ == [State |-> t.State,
                           Ret |-> [t.Ret EXCEPT ![p] = x[p]]]
        <4>1. t_ \in T
          BY <3>5, Z3 DEF TypeOK, Inv5, L5
        <4>2. PICK u_ \in T : u_ = [State |-> t_.State,
                                    Ret |-> [t_.Ret EXCEPT ![p_1] = Bot]]
          BY <3>5, <4>1 DEF Inv24, L5
        <4>   DEFINE u == [State |-> u_.State,
                           Ret |-> [u_.Ret EXCEPT ![p] = Bot]]
        <4>3. u \in T'
          BY <3>5, <4>1, Zenon DEF L5
        <4>4. u = [State |-> t.State,
                   Ret |-> [t.Ret EXCEPT ![p_1] = Bot]]
          BY <4>2, <4>3 DEF TypeOK
        <4>5. QED
          BY <4>3, <4>4
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF TypeOK, Inv24, L1
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step  
  <2>9. Inv3'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv3'
      PROOF BY <3>1 DEF Inv3, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv3'
      <4>1. CASE /\ pc[p] = 2
                 /\ X = x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ X' = v[p]
                 /\ T' = {u \in [State : {v[p]}, 
                                 Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                            /\ u.Ret[p] = Ack
                            /\ u.State = v[p]
                            /\ (\E t \in T : /\ t.Ret[p] = Bot
                                             /\ t.State = x[p]
                                             /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                         \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                    /\ (/\ pc[q] = 2
                                                                        /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
                 /\ UNCHANGED <<x, v>>
        <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                            (pc[p_1] = 3)'
                     PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
          BY DEF Inv3
        <5>1. CASE p = p_1
          <6>1. PICK t \in T : /\ t.State = x[p]
                               /\ t.Ret[p] = Bot
                               /\ t.Ret[p_1] = Bot
            BY <4>1, <5>1 DEF Inv02, Inv21
          <6>   DEFINE u == [State |-> v[p],
                             Ret |-> [[q \in ProcSet |-> IF pc[q] = 2 /\ t.Ret[q] /= Ack 
                                                            THEN Bot 
                                                            ELSE t.Ret[q]] EXCEPT ![p] = Ack]]
          <6>2. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
                /\ u.State = v[p]
                /\ u.Ret[p] = Ack
                /\ u.Ret[p_1] = Ack
            BY <5>1 DEF TypeOK
          <6>3. \A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                        \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                   /\ (/\ pc[q] = 2
                                       /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack} 
            BY <4>1
          <6>4. u \in T'
            BY <3>2, <4>1, <5>1, <6>1, <6>2, <6>3 DEF TypeOK, L2, Zenon
          <6>5. QED
            BY <6>2, <6>4
        <5>2. CASE p /= p_1
          <6>1. PICK t_ \in T : /\ t_.State = x[p]
                                /\ t_.Ret[p_1] = Ack
            BY <4>1, <5>2 DEF L2, TypeOK, Inv02, Inv3
          <6>2. t_.Ret[p] = Ack => \E u \in T : u = [State |-> t_.State,
                                                     Ret |-> [t_.Ret EXCEPT ![p] = Bot]]
            BY <4>1 DEF L2, Inv24, TypeOK
          <6>3. PICK t \in T : /\ t.State = x[p]
                               /\ t.Ret[p] = Bot
                               /\ t.Ret[p_1] = Ack
            BY <4>1, <5>2, <6>1, <6>2 DEF Inv23, TypeOK
          <6>   DEFINE u == [State |-> v[p],
                             Ret |-> [[q \in ProcSet |-> IF pc[q] = 2 /\ t.Ret[q] /= Ack 
                                                            THEN Bot 
                                                            ELSE t.Ret[q]] EXCEPT ![p] = Ack]]              
          <6>4. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
                /\ u.State = v[p]
                /\ u.Ret[p] = Ack
            BY DEF TypeOK
          <6>5. \A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                        \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                   /\ (/\ pc[q] = 2
                                       /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack} 
            BY <4>1
          <6>6. u \in T'
            BY <3>2, <4>1, <5>2, <6>3, <6>4, <6>5 DEF TypeOK, L2, Zenon
          <6> QED
            BY <6>3, <6>6 DEF Inv3, Zenon
        <5>3. QED
          BY <5>1, <5>2
      <4>2. CASE /\ pc[p] = 2
                 /\ X /= x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ UNCHANGED <<X, x, v, T>>
        BY <4>2 DEF Inv22, Inv3
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv3'
        <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 3)'
                   PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
        BY DEF Inv3
        <4>1. PICK t \in T : /\ t.Ret[p] = Ack
                             /\ t.Ret[p_1] = Ack
          BY <3>3 DEF L3, Inv03
        <4>   DEFINE u == [State |-> t.State,
                           Ret |-> [t.Ret EXCEPT ![p] = Bot]]
        <4>2. u \in T'
          BY <3>3, <4>1, Zenon DEF L3
        <4>3. p_1 /= p
          BY <3>3 DEF L3, TypeOK
        <4>4. u.Ret[p_1] = Ack
          BY <3>3, <4>1, <4>3 DEF L3
        <4>5. QED
          PROOF BY <4>2, <4>4, Zenon
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv3'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 3)'
                   PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
        BY DEF Inv3
      <4>1. PICK t \in T : t.Ret[p_1] = Ack
        BY <3>4 DEF L4, Inv3
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = X]]
      <4>2. u \in T'
        BY <3>4, Zenon DEF L4
      <4>3. u.Ret[p_1] = Ack
        BY <3>4, <4>1 DEF L4
      <4>4. QED
        PROOF BY <4>2, <4>3, Zenon
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv3'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 3)'
                   PROVE  (\E t \in T : t.Ret[p_1] = Ack)'
        BY DEF Inv3
      <4>1. PICK t \in T : t.Ret[p_1] = Ack
        BY <3>5 DEF L5, Inv3
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = Bot]]
      <4>2. u \in T'
        BY <3>5, Zenon DEF L5
      <4>3. u.Ret[p_1] = Ack
        BY <3>5, <4>1 DEF L5
      <4>4. QED
        PROOF BY <4>2, <4>3, Zenon
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF L4, Inv3, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step
  <2>10. Inv4'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv4'
      PROOF BY <3>1 DEF Inv4, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv4'
      PROOF BY <3>2 DEF TypeOK, Inv4, L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv4'
      PROOF BY <3>3 DEF TypeOK, Inv4, L3
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv4'
      PROOF BY <3>4 DEF TypeOK, Inv4, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv4'
      PROOF BY <3>5 DEF TypeOK, Inv4, L5
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF Inv4, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step
  <2>11. Inv5'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv5'
      PROOF BY <3>1 DEF Inv5, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv5'
      PROOF BY <3>2 DEF TypeOK, Inv5, L2
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv5'
      PROOF BY <3>3 DEF TypeOK, Inv5, L3
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv5'
      PROOF BY <3>4 DEF TypeOK, Inv5, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv5'
      PROOF BY <3>5 DEF TypeOK, Inv5, L5
    <3>6. CASE UNCHANGED vars
      PROOF BY <3>6 DEF Inv5, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step  
  <2>12. Inv25'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv25'
      BY <3>1 DEF TypeOK, Inv25, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv25'
      <4>1. CASE /\ pc[p] = 2
                 /\ X = x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ X' = v[p]
                 /\ T' = {u \in [State : {v[p]}, 
                                 Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                            /\ u.Ret[p] = Ack
                            /\ u.State = v[p]
                            /\ (\E t \in T : /\ t.Ret[p] = Bot
                                             /\ t.State = x[p]
                                             /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                         \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                    /\ (/\ pc[q] = 2
                                                                        /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
                 /\ UNCHANGED <<x, v>>
        <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                            (pc[p_1] = 2)',
                            (X /= x[p_1])',
                            NEW t_pr \in T',
                            (t_pr.Ret[p_1] = Bot)'
                     PROVE  (\E u \in T : u = [State |-> t_pr.State, 
                                               Ret |-> [t_pr.Ret EXCEPT ![p_1] = Ack]])'
          BY DEF Inv25
        <5>   DEFINE u == [State |-> t_pr.State,
                           Ret |-> [t_pr.Ret EXCEPT ![p_1] = Ack]]
        <5>1. PICK t_1 \in T : /\ t_1.Ret[p] = Bot
                               /\ t_1.State = x[p]
                               /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                           \/ t_1.Ret[q] = Ack) => t_pr.Ret[q] = t_1.Ret[q])
                                                      /\ (/\ pc[q] = 2
                                                          /\ t_1.Ret[q] /= Ack) => t_pr.Ret[q] \in {Bot, Ack})
          BY <4>1
        <5>2. /\ t_1.Ret[p_1] \in {Bot, Ack}
              /\ t_1.Ret[p_1] = Ack => \E t_ \in T : t_ = [State |-> t_1.State,
                                                           Ret |-> [t_1.Ret EXCEPT ![p_1] = Bot]]
          BY <4>1 DEF L2, TypeOK, Inv23, Inv24
        <5>3. PICK u_ \in T : /\ u_.Ret[p] = Bot
                              /\ u_.Ret[p_1] = Bot
                              /\ u_.State = x[p]
                              /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                          \/ u_.Ret[q] = Ack) => t_pr.Ret[q] = u_.Ret[q])
                                                     /\ (/\ pc[q] = 2
                                                         /\ u_.Ret[q] /= Ack) => t_pr.Ret[q] \in {Bot, Ack})
          BY <5>1, <5>2
\*        <5>4. pc[p_1] = 2
\*          BY <4>1 DEF L2, TypeOK
        <5>4.  /\ u_ \in T
               /\ u_.Ret[p] = Bot
               /\ u_.State = x[p]
               /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                           \/ u_.Ret[q] = Ack) => u.Ret[q] = u_.Ret[q])
                                      /\ (/\ pc[q] = 2
                                          /\ u_.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack})
          BY <4>1, <5>3 DEF L2, TypeOK
        <5>5. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
              /\ u.State = v[p]
              /\ u.Ret[p] = Ack
          BY <4>1 DEF L2, TypeOK
        <5>6. (\E t \in T : /\ t.Ret[p] = Bot
                            /\ t.State = x[p]
                            /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                        \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                   /\ (/\ pc[q] = 2
                                                       /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))
          BY <5>3, <5>4
        <5>7. u \in T'
          BY <4>1, <5>4, <5>6 DEF TypeOK, L2
        <5>8. QED
          BY <5>7 DEF Inv25
      <4>2. CASE /\ pc[p] = 2
                 /\ X /= x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ UNCHANGED <<X, x, v, T>>
        BY <4>2, <3>2 DEF TypeOK, Inv25, L2
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2
      
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv25'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          (X /= x[p_1])',
                          NEW t \in T',
                          (t.Ret[p_1] = Bot)'
                   PROVE  (\E u \in T : u = [State |-> t.State, 
                                             Ret |-> [t.Ret EXCEPT ![p_1] = Ack]])'
        BY DEF Inv25
      <4>   DEFINE t_ == [State |-> t.State,
                          Ret |-> [t.Ret EXCEPT ![p] = Ack]]
      <4>1. t_ \in T
        BY <3>3, Z3 DEF L3, TypeOK
      <4>2. PICK u_ \in T : u_ = [State |-> t_.State,
                                  Ret |-> [t_.Ret EXCEPT ![p_1] = Ack]]
        BY <3>3, <4>1 DEF L3, Inv25
      <4>3. u_ \in {u \in T : u.Ret[p] = Ack}
        BY <4>2 DEF TypeOK
      <4>4. PICK u \in T' : u = [State |-> u_.State,
                                 Ret |-> [u_.Ret EXCEPT ![p] = Bot]]
        BY <3>3, <4>3, Zenon DEF L3
      <4>5. QED
        BY <4>2, <4>4
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv25'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          (X /= x[p_1])',
                          NEW t \in T',
                          (t.Ret[p_1] = Bot)'
                   PROVE  (\E u \in T : u = [State |-> t.State, 
                                             Ret |-> [t.Ret EXCEPT ![p_1] = Ack]])'
        BY DEF Inv25
      <4> DEFINE t_ == [State |-> t.State,
                        Ret |-> [t.Ret EXCEPT ![p] = Bot]]
      <4>1. t_ \in T
        BY <3>4, Z3 DEF TypeOK, Inv4, L4
      <4>2. PICK u_ \in T : u_ = [State |-> t_.State,
                                  Ret |-> [t_.Ret EXCEPT ![p_1] = Ack]]
        BY <3>4, <4>1 DEF Inv25, L4
      <4>   DEFINE u == [State |-> u_.State,
                         Ret |-> [u_.Ret EXCEPT ![p] = X]]
      <4>3. u \in T'
        BY <3>4, <4>1, Zenon DEF L4
      <4>4. u = [State |-> t.State,
                 Ret |-> [t.Ret EXCEPT ![p_1] = Ack]]
        BY <4>2, <4>3 DEF TypeOK
      <4>5. QED
        BY <4>3, <4>4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv25'
      <4> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] = 2)',
                          (X /= x[p_1])',
                          NEW t \in T',
                          (t.Ret[p_1] = Bot)'
                   PROVE  (\E u \in T : u = [State |-> t.State, 
                                             Ret |-> [t.Ret EXCEPT ![p_1] = Ack]])'
        BY DEF Inv25
      <4>  DEFINE t_ == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = x[p]]]
      <4>1. t_ \in T
        BY <3>5, Z3 DEF TypeOK, Inv5, L5
      <4>2. PICK u_ \in T : u_ = [State |-> t_.State,
                                  Ret |-> [t_.Ret EXCEPT ![p_1] = Bot]]
        BY <3>5, <4>1 DEF Inv25, L5
      <4>   DEFINE u == [State |-> u_.State,
                         Ret |-> [u_.Ret EXCEPT ![p] = Bot]]
      <4>3. u \in T'
        BY <3>5, <4>1, Zenon DEF L5
      <4>4. u = [State |-> t.State,
                 Ret |-> [t.Ret EXCEPT ![p_1] = Ack]]
        BY <4>2, <4>3 DEF TypeOK
      <4>5. QED
        BY <4>3, <4>4
    <3>6. CASE UNCHANGED vars
      BY <3>6 DEF TypeOK, Inv25
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step
  <2>13. Inv03'
    <3>1. ASSUME NEW p \in ProcSet,
                 L1(p)
          PROVE  Inv03'
      BY <3>1 DEF TypeOK, Inv03, L1
    <3>2. ASSUME NEW p \in ProcSet,
                 L2(p)
          PROVE  Inv03'
      <4>1. CASE /\ pc[p] = 2
                 /\ X = x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ X' = v[p]
                 /\ T' = {u \in [State : {v[p]}, 
                                 Ret : [ProcSet -> Nat \cup {Bot, Ack}]] : 
                            /\ u.Ret[p] = Ack
                            /\ u.State = v[p]
                            /\ (\E t \in T : /\ t.Ret[p] = Bot
                                             /\ t.State = x[p]
                                             /\ (\A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                                                         \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                                                    /\ (/\ pc[q] = 2
                                                                        /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}))}
                 /\ UNCHANGED <<x, v>>
\*        BY <4>1, <3>2 DEF TypeOK, Inv03, L2
        <5>1. PICK t_1 \in T : (\A q \in ProcSet : pc[q] = 3 => t_1.Ret[q] = Ack)
          BY <3>2 DEF Inv03
        <5>2. /\ t_1.Ret[p] \in {Bot, Ack}
              /\ t_1.Ret[p] = Ack => \E u \in T : u = [State |-> t_1.State,
                                                       Ret |-> [t_1.Ret EXCEPT ![p] = Bot]]
          BY <4>1, <5>1 DEF Inv23, Inv24, TypeOK
        <5>3. PICK t \in T : /\ (\A q \in ProcSet : pc[q] = 3 => t.Ret[q] = Ack)
                             /\ t.Ret[p] = Bot
                             /\ t.State = x[p]
          BY <4>1, <5>1, <5>2 DEF TypeOK, Inv02
        <5>   DEFINE u == [State |-> v[p],
                           Ret |-> [t.Ret EXCEPT ![p] = Ack]]
        <5>4. \A q \in ProcSet : /\ ((\/ pc[q] /= 2
                                      \/ t.Ret[q] = Ack) => u.Ret[q] = t.Ret[q])
                                 /\ (/\ pc[q] = 2
                                     /\ t.Ret[q] /= Ack) => u.Ret[q] \in {Bot, Ack}               
          BY <4>1 DEF Inv23
        <5>5. /\ u \in [State : {v[p]}, Ret : [ProcSet -> Nat \cup {Bot, Ack}]] 
              /\ u.State = v[p]
              /\ u.Ret[p] = Ack
          BY <4>1 DEF TypeOK
        <5>6. u \in T'
          BY <4>1, <5>3, <5>4, <5>5
        <5>7. \A q \in ProcSet : pc'[q] = 3 => u.Ret[q] = Ack
          BY <4>1, <5>3 DEF TypeOK
        <5>8. QED
          BY <5>6, <5>7 DEF Inv03
      <4>2. CASE /\ pc[p] = 2
                 /\ X /= x[p]
                 /\ pc' = [pc EXCEPT ![p] = 3]
                 /\ UNCHANGED <<X, x, v, T>>
        <5>1. PICK t \in T : (\A q \in ProcSet : pc[q] = 3 => t.Ret[q] = Ack)
          BY <3>2 DEF Inv03
        <5>2. /\ t.Ret[p] \in {Bot, Ack}
              /\ t.Ret[p] = Bot => \E u \in T : u = [State |-> t.State,
                                                     Ret |-> [t.Ret EXCEPT ![p] = Ack]]
          BY <4>2 DEF Inv23, Inv25
        <5>3. PICK u \in T : /\ (\A q \in ProcSet : pc[q] = 3 => u.Ret[q] = Ack)
                             /\ u.Ret[p] = Ack
          BY <5>1, <5>2 DEF TypeOK
        <5>4. u \in T'
          BY <4>2
        <5>5. \A q \in ProcSet : pc'[q] = 3 => u.Ret[q] = Ack
          BY <4>2, <5>3 DEF TypeOK
        <5>6. QED
          BY <5>4, <5>5 DEF Inv03
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2  
    <3>3. ASSUME NEW p \in ProcSet,
                 L3(p)
          PROVE  Inv03'
      <4>1. PICK t \in T : \A q \in ProcSet : pc[q] = 3 => t.Ret[q] = Ack
        BY <3>3 DEF Inv03
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = Bot]]
      <4>2. u \in T'
        BY <3>3, <4>1, Zenon DEF L3
      <4>3. \A q \in ProcSet : pc'[q] = 3 => u.Ret[q] = Ack
        BY <3>3, <4>1 DEF L3, TypeOK
      <4> QED
        BY <3>3, <4>2, <4>3, Zenon DEF Inv03, L3               
    <3>4. ASSUME NEW p \in ProcSet,
                 L4(p)
          PROVE  Inv03'
      <4>1. PICK t \in T : \A q \in ProcSet : pc[q] = 3 => t.Ret[q] = Ack
        BY <3>4 DEF Inv03
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = X]]
      <4>2. u \in T'
        BY <3>4, Zenon DEF L4
      <4>3. \A q \in ProcSet : pc'[q] = 3 => u.Ret[q] = Ack
        BY <3>4, <4>1 DEF L4
      <4> QED
        BY <3>4, <4>2, <4>3, Zenon DEF Inv03, L4
    <3>5. ASSUME NEW p \in ProcSet,
                 L5(p)
          PROVE  Inv03'
      <4>1. PICK t \in T : \A q \in ProcSet : pc[q] = 3 => t.Ret[q] = Ack
        BY <3>5 DEF Inv03
      <4>   DEFINE u == [State |-> t.State,
                         Ret |-> [t.Ret EXCEPT ![p] = Bot]]
      <4>2. u \in T'
        BY <3>5, Zenon DEF L5
      <4>3. \A q \in ProcSet : pc'[q] = 3 => u.Ret[q] = Ack
        BY <3>5, <4>1 DEF L5
      <4>4. QED
        BY <3>5, <4>2, <4>3, Zenon DEF Inv03, L5
    <3>6. CASE UNCHANGED vars
      BY <3>6 DEF TypeOK, Inv03, vars
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, Step  
  <2>14. QED
    BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF IInv  
<1>3. QED
  PROOF BY <1>1, <1>2

=============================================================================
\* Modification History
\* Last modified Fri May 14 11:33:08 EDT 2021 by uguryavuz
\* Created Thu May 06 15:11:18 EDT 2021 by uguryavuz
