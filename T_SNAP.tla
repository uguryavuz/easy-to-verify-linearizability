------------------------------- MODULE T_SNAP -------------------------------
EXTENDS Integers, FiniteSets, TLAPS
VARIABLES pc, X, A, B, v, a, b, T

vars == <<pc, X, A, B, v, a, b, T>>
ProcSet == {"S", "W"}
Bot == -10
Ack == -15

Init == /\ pc = [p \in ProcSet |-> IF p = "W" THEN 1 ELSE 5]
        /\ X = FALSE
        /\ A \in Nat
        /\ B \in Nat \union {Bot}
        /\ a \in Nat
        /\ b \in Nat \union {Bot}
        /\ v \in Nat
        /\ T = {[State |-> A,
                 RetW  |-> Bot,
                 RetS  |-> Bot]}
                 
\* Original algorithm
\* `^write(v)^'
\*    `^A \gets v^'
\*    `^{\bf if} X^'   
\*       `^B \gets v^'
\*    `^{\bf return} ack^'
\* `^scan()^'
\*    `^X \gets true^'
\*    `^B \gets \bot^'
\*    `^a \gets A^'
\*    `^X \gets false^'
\*    `^b \gets B^'
\*    `^{\bf if} b = \bot $\bf{ return }$ a $\bf{ else }$ b^'  

Inv1A == pc["W"] = 1 => (\E t \in T : /\ t.State = A
                                      /\ t.RetW = Bot)
Inv1B == pc["W"] = 1 => (\A t \in T : /\ t.State = A
                                      /\ t.RetW = Bot)
                
L1   == \/ (/\ pc["W"] = 1    
            /\ pc' = [pc EXCEPT !["W"] = 2]
            /\ A' = v
            /\ (\/ X = FALSE
                \/ pc["S"] = 6
                \/ (/\ pc["S"] = 7 
                    /\ B = Bot)
                \/ B = v
                \/ (/\ pc["S"] = 8 
                    /\ B = Bot
                    /\ a = v))
            /\ T' = {[State |-> v,
                      RetW  |-> Ack,
                      RetS  |-> t.RetS] : t \in T}
            /\ UNCHANGED <<X, B, v, a, b>>)
            
        \/ (/\ pc["W"] = 1    
            /\ pc' = [pc EXCEPT !["W"] = 2]
            /\ A' = v
            /\ (/\ X = TRUE
                /\ pc["S"] /= 6
                /\ (\/ pc["S"] /= 7 
                    \/ B /= Bot)
                /\ B /= v
                /\ (\/ pc["S"] /= 8 
                    \/ B /= Bot 
                    \/ a /= v))
            /\ T' = {[State |-> v,
                      RetW  |-> Ack,
                      RetS  |-> t.RetS] : t \in T} \union T
            /\ UNCHANGED <<X, B, v, a, b>>)

Inv2A == pc["W"] = 2 => A = v
Inv2B == pc["W"] = 2 => (\E t \in T : /\ t.State = v
                                      /\ t.RetW = Ack)
Inv2C == pc["W"] = 2 => (X = FALSE => (\A t \in T : /\ t.State = v
                                                    /\ t.RetW = Ack))
Inv2D == pc["W"] = 2 => (\E t \in T : t.RetW = Bot => (\/ (/\ pc["S"] \in {7, 8}
                                                           /\ B /= Bot
                                                           /\ B /= v)
                                                       \/ (/\ pc["S"] = 8
                                                           /\ A /= a
                                                           /\ B = Bot)))
           
L2   == \/ (/\ pc["W"] = 2
            /\ X = TRUE
            /\ pc' = [pc EXCEPT !["W"] = 3]
            /\ UNCHANGED <<X, A, B, v, a, b, T>>)
        \/ (/\ pc["W"] = 2
            /\ X = FALSE
            /\ pc' = [pc EXCEPT !["W"] = 4]
            /\ UNCHANGED <<X, A, B, v, a, b, T>>)

Inv3A == pc["W"] = 3 => A = v
Inv3B == pc["W"] = 3 => (\E t \in T : /\ t.State = v
                                      /\ t.RetW = Ack)
Inv3C == pc["W"] = 3 => (pc["S"] \in {9, 10} => (\E t \in T : /\ t.State = v
                                                              /\ t.RetW = Ack
                                                              /\ t.RetS = v))
Inv3D == pc["W"] = 3 => (\E t \in T : t.RetW = Bot => (\/ (/\ pc["S"] \in {7, 8}
                                                           /\ B /= Bot
                                                           /\ B /= v)
                                                       \/ (/\ pc["S"] = 8
                                                           /\ A /= a
                                                           /\ B = Bot)))

L3   == /\ pc["W"] = 3
        /\ pc' = [pc EXCEPT !["W"] = 4]
        /\ B' = v
        /\ T' = {t \in T : t.RetW = Ack}
        /\ UNCHANGED <<X, A, v, a, b>>
        
Inv4A == pc["W"] = 4 => A = v    
Inv4B == pc["W"] = 4 => (\E t \in T : /\ t.State = A
                                      /\ t.RetW = Ack)
Inv4C == pc["W"] = 4 => (\A t \in T : /\ t.State = A
                                      /\ t.RetW = Ack)
        
L4   == /\ pc["W"] = 4
        /\ pc' = [pc EXCEPT !["W"] = 1]
        /\ v' \in Nat
        /\ T' = {[State |-> t.State,
                  RetW  |-> Bot,
                  RetS  |-> t.RetS] : t \in T}
        /\ UNCHANGED <<X, A, B, a, b>>
        
Inv5A == pc["S"] = 5 => X = FALSE
Inv5B == pc["S"] = 5 => (\A t \in T : t.RetS = Bot)
Inv5C == pc["S"] = 5 => (\A t \in T : /\ t.State = A
                                      /\ (pc["W"] /= 1 => t.RetW = Ack))
        
L5   == /\ pc["S"] = 5
        /\ pc' = [pc EXCEPT !["S"] = 6]
        /\ X' = TRUE
        /\ UNCHANGED <<A, B, v, a, b, T>>
        
Inv6A == pc["S"] = 6 => X = TRUE
Inv6B == pc["S"] = 6 => (\A t \in T : t.RetS = Bot)
        
L6   == /\ pc["S"] = 6
        /\ pc' = [pc EXCEPT !["S"] = 7]
        /\ B' = Bot
        /\ UNCHANGED <<A, X, v, a, b, T>>
        
Inv7A == pc["S"] = 7 => X = TRUE
Inv7B == pc["S"] = 7 => (\A t \in T : t.RetS = Bot)
Inv7C == pc["S"] = 7 => (B /= Bot => \E t \in T : t.State = B)
Inv7D == pc["S"] = 7 => (B = Bot => (\E t \in T : t.State = A))
        
L7   == /\ pc["S"] = 7
        /\ pc' = [pc EXCEPT !["S"] = 8]
        /\ a' = A
        /\ UNCHANGED <<A, B, X, v, b, T>>
        
Inv8A == pc["S"] = 8 => X = TRUE
Inv8B == pc["S"] = 8 => (\A t \in T : t.RetS = Bot)
Inv8C == pc["S"] = 8 => (B /= Bot => (\E t \in T : t.State = B))
Inv8D == pc["S"] = 8 => (B = Bot  => (\E t \in T : t.State = a))
        
L8   == /\ pc["S"] = 8
        /\ pc' = [pc EXCEPT !["S"] = 9]
        /\ X' = FALSE
        /\ T' = {u \in [State : Nat,
                        RetW  : {Bot, Ack},
                        RetS  : Nat \union {Bot}] : \E t \in T : (\/ (/\ t.RetW = Bot
                                                                      /\ pc["W"] /= 1
                                                                      /\ u.RetW = Ack
                                                                      /\ u.RetS = t.State
                                                                      /\ u.State = v)
                                                                  \/ (/\ t.RetW = Bot
                                                                      /\ pc["W"] = 1
                                                                      /\ u.RetW = Bot
                                                                      /\ u.State = t.State
                                                                      /\ u.RetS = t.State)
                                                                  \/ (/\ t.RetW = Ack
                                                                      /\ u.RetW = Ack
                                                                      /\ u.State = t.State
                                                                      /\ u.RetS = t.State))}
        /\ UNCHANGED <<A, B, v, a, b>>    
        
Inv9A == pc["S"] = 9 => X = FALSE
Inv9B == pc["S"] = 9 => (\A t \in T : t.RetS /= Bot)
Inv9C == pc["S"] = 9 => (B /= Bot => (\E t \in T : t.RetS = B))
Inv9D == pc["S"] = 9 => (B = Bot  => (\E t \in T : t.RetS = a))
Inv9E == pc["S"] = 9 => (\A t \in T : /\ t.State = A
                                      /\ (pc["W"] /= 1 => t.RetW = Ack))

L9   == /\ pc["S"] = 9
        /\ pc' = [pc EXCEPT !["S"] = 10]
        /\ b' = B
        /\ UNCHANGED <<X, A, B, v, a, T>>
        
Inv10A == pc["S"] = 10 => X = FALSE
Inv10B == pc["S"] = 10 => (\A t \in T : t.RetS /= Bot)
Inv10C == pc["S"] = 10 => (b /= Bot => (\E t \in T : t.RetS = b))
Inv10D == pc["S"] = 10 => (b = Bot  => (\E t \in T : t.RetS = a))
Inv10E == pc["S"] = 10 => (\A t \in T : /\ t.State = A
                                        /\ (pc["W"] /= 1 => t.RetW = Ack))
         
L10  == /\ pc["S"] = 10
        /\ pc' = [pc EXCEPT !["S"] = 5]
        /\ T' = {[State |-> t.State,
                  RetW  |-> t.RetW,
                  RetS  |-> Bot] : t \in {t_1 \in T : t_1.RetS /= Bot}}
\*                  RetS  |-> Bot] : t \in T}
        /\ UNCHANGED <<X, A, B, v, a, b>>
        
Next == \/ L1
        \/ L2
        \/ L3
        \/ L4
        \/ L5
        \/ L6
        \/ L7
        \/ L8
        \/ L9
        \/ L10
        
Spec == /\ Init
        /\ [][Next]_vars
        
TypeOK == /\ pc \in [ProcSet -> {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}]
          /\ pc["W"] \in {1, 2, 3, 4}
          /\ pc["S"] \in {5, 6, 7, 8, 9, 10}
          /\ X \in BOOLEAN
          /\ A \in Nat
          /\ B \in Nat \union {Bot}
          /\ a \in Nat
          /\ b \in Nat \union {Bot}
          /\ v \in Nat
          /\ T \in SUBSET [State : Nat,
                           RetW  : {Bot, Ack},
                           RetS  : Nat \union {Bot}]
                           
Inv0A == /\ \A t1, t2, t3 \in T : ~(/\ t1 /= t2 
                                    /\ t1 /= t3 
                                    /\ t2 /= t3)
Inv0B == /\ \A t \in T : t.RetW = Ack => t.State = A

IInv == /\ TypeOK
\*        /\ Inv0A
        /\ Inv0B
        /\ Inv1A
        /\ Inv1B
        /\ Inv2A
        /\ Inv2B
        /\ Inv2C
        /\ Inv2D
        /\ Inv3A
        /\ Inv3B
        /\ Inv3C
        /\ Inv3D
        /\ Inv4A
        /\ Inv4B
        /\ Inv4C
        /\ Inv5A
        /\ Inv5B
        /\ Inv5C
        /\ Inv6A
        /\ Inv6B
        /\ Inv7A
        /\ Inv7B
        /\ Inv7C
        /\ Inv7D \* NEW
        /\ Inv8A
        /\ Inv8B
        /\ Inv8C
        /\ Inv8D
        /\ Inv9A
        /\ Inv9B
        /\ Inv9C
        /\ Inv9D
        /\ Inv9E
        /\ Inv10A
        /\ Inv10B
        /\ Inv10C
        /\ Inv10D
        /\ Inv10E

ISpec == /\ IInv
         /\ [][Next]_vars
         
THEOREM TypeCorrectness == Spec => []TypeOK
<1> USE DEFS ProcSet, Bot, Ack, TypeOK
<1>1. Init => TypeOK
  <2> SUFFICES ASSUME Init
               PROVE  TypeOK
    OBVIOUS
  <2>1. pc \in [ProcSet -> {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}]
    PROOF BY DEF Init
  <2>2. pc["W"] \in {1, 2, 3, 4}
    PROOF BY DEF Init
  <2>3. pc["S"] \in {5, 6, 7, 8, 9, 10}
    PROOF BY DEF Init
  <2>4. X \in BOOLEAN
    PROOF BY DEF Init
  <2>5. A \in Nat
    PROOF BY DEF Init
  <2>6. B \in Nat \union {Bot}
    PROOF BY DEF Init
  <2>7. a \in Nat
    PROOF BY DEF Init
  <2>8. b \in Nat \union {Bot}
    PROOF BY DEF Init
  <2>9. v \in Nat
    PROOF BY DEF Init
  <2>10. T \in SUBSET [State : Nat,
                       RetW  : {Bot, Ack},
                       RetS  : Nat \union {Bot}]
    PROOF BY DEF Init
  <2>11. QED
    BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>1. QED
    <3> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <3>1. CASE L1
      PROOF BY <3>1 DEF Next, vars, L1
    <3>2. CASE L2
      PROOF BY <3>2 DEF Next, vars, L2
    <3>3. CASE L3
      PROOF BY <3>3 DEF Next, vars, L3
    <3>4. CASE L4
      PROOF BY <3>4 DEF Next, vars, L4
    <3>5. CASE L5
      PROOF BY <3>5 DEF Next, vars, L5
    <3>6. CASE L6
      PROOF BY <3>6 DEF Next, vars, L6
    <3>7. CASE L7
      PROOF BY <3>7 DEF Next, vars, L7
    <3>8. CASE L8
      PROOF BY <3>8 DEF Next, vars, L8
    <3>9. CASE L9
      PROOF BY <3>9 DEF Next, vars, L9
    <3>10. CASE L10
      PROOF BY <3>10 DEF Next, vars, L10
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF Next, vars
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []IInv
<1> USE DEFS ProcSet, Bot, Ack, TypeOK
<1>1. Init => IInv
  <2> SUFFICES ASSUME Init
               PROVE  IInv
    OBVIOUS
  <2>1. TypeOK
    BY Isa DEF Init
  <2>2. Inv0A
    BY DEF Init, Inv0A
  <2>3. Inv0B
    BY DEF Init, Inv0B
  <2>4. Inv1A
    BY DEF Init, Inv1A
  <2>5. Inv1B
    BY DEF Init, Inv1B
  <2>6. Inv2A
    BY DEF Init, Inv2A
  <2>7. Inv2B
    BY DEF Init, Inv2B
  <2>8. Inv2C
    BY DEF Init, Inv2C
  <2>9. Inv2D
    BY DEF Init, Inv2D
  <2>10. Inv3A
    BY DEF Init, Inv3A
  <2>11. Inv3B
    BY DEF Init, Inv3B
  <2>12. Inv3C
    BY DEF Init, Inv3C
  <2>13. Inv3D
    BY DEF Init, Inv3D
  <2>14. Inv4A
    BY DEF Init, Inv4A
  <2>15. Inv4B
    BY DEF Init, Inv4B
  <2>16. Inv4C
    BY DEF Init, Inv4C
  <2>17. Inv5A
    BY DEF Init, Inv5A
  <2>18. Inv5B
    BY DEF Init, Inv5B
  <2>19. Inv5C
    BY DEF Init, Inv5C
  <2>20. Inv6A
    BY DEF Init, Inv6A
  <2>21. Inv6B
    BY DEF Init, Inv6B
  <2>22. Inv7A
    BY DEF Init, Inv7A
  <2>23. Inv7B
    BY DEF Init, Inv7B
  <2>24. Inv7C
    BY DEF Init, Inv7C
  <2>25. Inv8A
    BY DEF Init, Inv8A
  <2>26. Inv8B
    BY DEF Init, Inv8B
  <2>27. Inv8C
    BY DEF Init, Inv8C
  <2>28. Inv8D
    BY DEF Init, Inv8D
  <2>29. Inv9A
    BY DEF Init, Inv9A
  <2>30. Inv9B
    BY DEF Init, Inv9B
  <2>31. Inv9C
    BY DEF Init, Inv9C
  <2>32. Inv9D
    BY DEF Init, Inv9D
  <2>33. Inv9E
    BY DEF Init, Inv9E
  <2>34. Inv10A
    BY DEF Init, Inv10A
  <2>35. Inv10B
    BY DEF Init, Inv10B
  <2>36. Inv10C
    BY DEF Init, Inv10C
  <2>37. Inv10D
    BY DEF Init, Inv10D
  <2>38. Inv10E
    BY DEF Init, Inv10E
  <2>39. Inv7D
    BY DEF Init, Inv7D
  <2>40. QED
    BY <2>1, <2>39, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, <2>19, <2>2, <2>20, <2>21, <2>22, <2>23, <2>24, <2>25, <2>26, <2>27, <2>28, <2>29, <2>3, <2>30, <2>31, <2>32, <2>33, <2>34, <2>35, <2>36, <2>37, <2>38, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF IInv
<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv /\ [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2> USE DEF IInv, Next, vars, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10
  <2>1. TypeOK'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
\*  <2>2. Inv0A'
\*    OMITTED
  <2>3. Inv0B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv0B, Inv1B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv0B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv0B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv0B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv0B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv0B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv0B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv0B, Inv2A, Inv3A, Inv4A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv0B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv0B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv0B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>4. Inv1A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv1A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv1A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv1A
    <3>4. CASE L4
      PROOF BY <3>4, Isa DEF TypeOK, Inv1A, Inv4A, Inv4B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv1A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv1A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv1A
    <3>8. CASE L8
      <4> USE DEF L8
      <4> SUFFICES ASSUME pc["W"] = 1
                   PROVE  \E t \in T' : /\ t.State = A'
                                        /\ t.RetW = Bot
        BY <3>8 DEF L8, Inv1A
      <4>1. PICK t \in T : /\ t.State = A
                           /\ t.RetW = Bot
        BY DEF Inv1A
      <4>2. DEFINE u == [State |-> t.State,
                         RetW  |-> Bot,
                         RetS  |-> t.State]
      <4>3. u \in T'
        BY <3>8, <4>1
      <4>4. QED
        BY <3>8, <4>1, <4>3
        
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv1A
    <3>10. CASE L10
      <4> SUFFICES ASSUME (pc["W"] = 1)'
                   PROVE  (\E t \in T : /\ t.State = A
                                        /\ t.RetW = Bot)'
        BY DEF Inv1A
      <4>1. PICK t \in T : /\ t.State = A
                           /\ t.RetW = Bot
        BY <3>10 DEF L10, Inv1A
      <4>2. t.RetS /= Bot
        BY <3>10 DEF L10, Inv10B
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> t.RetW,
                         RetS  |-> Bot]
      <4>3. u \in T'
        BY <3>10, <4>1, <4>2 DEF L10
      <4>4. QED
        BY <4>1, <4>3
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv1A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>5. Inv1B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv1B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv1B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv1B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv1B, Inv4A, Inv4B, Inv4C
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv1B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv1B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv1B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv1B
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv1B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv1B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv1B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>6. Inv2A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv2A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv2A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv2A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv2A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv2A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv2A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv2A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv2A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv2A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv2A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv2A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>7. Inv2B'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>1, <3>1, Isa DEF TypeOK, Inv1A, Inv1B, Inv2B
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1, IsaT(60) DEF TypeOK, Inv1A, Inv1B, Inv2B
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv2B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv2B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv2B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv2B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv2B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv2B
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["W"] = 2
                   PROVE  \E t \in T' : /\ t.State = v'
                                        /\ t.RetW = Ack
        BY <3>8 DEF L8, Inv2B
      <4>1. PICK t \in T : /\ t.State = v
                           /\ t.RetW = Ack
        BY DEF Inv2B
      <4>2. DEFINE u == [State |-> t.State,
                         RetW  |-> Ack,
                         RetS  |-> t.State]
      <4>3. u \in T'
        BY <3>8, <4>1
      <4>4. QED
        BY <3>8, <4>1, <4>3
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv2B
    <3>10. CASE L10
      <4> SUFFICES ASSUME (pc["W"] = 2)'
                   PROVE  (\E t \in T : /\ t.State = v
                                        /\ t.RetW = Ack)'
        BY DEF Inv2B
      <4>1. PICK t \in T : /\ t.State = v
                           /\ t.RetW = Ack
        BY <3>10 DEF L10, Inv2B
      <4>2. t.RetS /= Bot
        BY <3>10 DEF L10, Inv10B
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> t.RetW,
                         RetS  |-> Bot]
      <4>3. u \in T'
        BY <3>10, <4>1, <4>2 DEF L10
      <4>4. QED
        BY <4>1, <4>3
      
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv2B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>8. Inv2C'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv2C
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv2C
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv2C
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv2C
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv2C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv2C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv2C
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc'["W"] = 2,
                          X' = FALSE,
                          NEW t_pr \in T'
                   PROVE  (/\ t_pr.State = v
                           /\ t_pr.RetW = Ack)'
        BY DEF Inv2C
      <4>1. t_pr.State = v'
        PROOF BY <3>8 DEF Inv2A, Inv0B
      <4>2. t_pr.RetW = Ack
        PROOF BY <3>8 DEF TypeOK, Inv2C
      <4>3. QED
        BY <4>1, <4>2
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv2C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv2C
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv2C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>9. Inv2D'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5>1. PICK t \in T : TRUE
          BY <3>1 DEF Inv1A
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>2. u \in T'
          BY <3>1, <4>1, <5>1
        <5>3. QED
          BY <5>1, <5>2 DEF Inv2D
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5>1. PICK t \in T : TRUE
          BY <3>1 DEF Inv1A
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>2. u \in T'
          BY <3>1, <4>2, <5>1
        <5>3. QED
          BY <5>1, <5>2 DEF Inv2D
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv2D
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv2D
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv2D
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv2D
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv2D
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv2D
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["W"] = 2
                   PROVE  (\E t \in T : t.RetW = Bot => (\/ (/\ pc["S"] \in {7, 8}
                                                             /\ B /= Bot
                                                             /\ B /= v)
                                                         \/ (/\ pc["S"] = 8
                                                             /\ A /= a
                                                             /\ B = Bot)))'
        BY <3>8 DEF Inv2D, L8
      <4>1. PICK t \in T : /\ t.State = v
                           /\ t.RetW = Ack
        BY DEF Inv2B
      <4>2. DEFINE u == [State |-> t.State,
                         RetW  |-> Ack,
                         RetS  |-> t.State]
      <4>3. u \in T'
        BY <3>8, <4>1
      <4>4. QED
        BY <3>8, <4>1, <4>3 DEF Inv2D
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv2D
    <3>10. CASE L10       
      <4> SUFFICES ASSUME pc["W"] = 2
                   PROVE  (\E t \in T : t.RetW = Bot => (\/ (/\ pc["S"] \in {7, 8}
                                                             /\ B /= Bot
                                                             /\ B /= v)
                                                         \/ (/\ pc["S"] = 8
                                                             /\ A /= a
                                                             /\ B = Bot)))'
        BY <3>10 DEF Inv2D, L10
      <4>1. PICK t \in T : /\ t.RetW = Ack
                           /\ t.RetS /= Bot
        BY <3>10 DEF Inv2B, Inv10B, Inv10E, L10
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> t.RetW,
                         RetS  |-> Bot]
      <4>2. u \in T'
        BY <3>10, <4>1 DEF L10
      <4>3. QED
        BY <4>1, <4>2
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv2D
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>10. Inv3A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv3A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv3A, Inv2A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv3A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv3A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv3A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv3A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv3A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv3A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv3A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv3A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv3A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>11. Inv3B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv3B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv3B, Inv2B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv3B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv3B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv3B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv3B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv3B
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["W"] = 3
                   PROVE  \E t \in T' : /\ t.State = v'
                                        /\ t.RetW = Ack
        BY <3>8 DEF L8, Inv3B
      <4>1. PICK t \in T : /\ t.State = v
                           /\ t.RetW = Ack
        BY DEF Inv3B
      <4>2. DEFINE u == [State |-> t.State,
                         RetW  |-> Ack,
                         RetS  |-> t.State]
      <4>3. u \in T'
        BY <3>8, <4>1
      <4>4. QED
        BY <4>1, <4>3
        
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv3B
    <3>10. CASE L10
      <4> SUFFICES ASSUME (pc["W"] = 3)'
                   PROVE  (\E t \in T : /\ t.State = v
                                        /\ t.RetW = Ack)'
        BY DEF Inv3B
      <4>1. PICK t \in T : /\ t.State = v
                           /\ t.RetW = Ack
        BY <3>10 DEF L10, Inv3B
      <4>2. t.RetS /= Bot
        BY <3>10 DEF L10, Inv10B
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> t.RetW,
                         RetS  |-> Bot]
      <4>3. u \in T'
        BY <3>10, <4>1, <4>2 DEF L10
      <4>4. QED
        BY <4>1, <4>3
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv3B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>12. Inv3C'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv3C
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv3C, Inv9A, Inv10A 
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv3C
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv3C
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv3C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv3C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv3C
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["W"] = 3,
                          pc'["S"] \in {9, 10}
                   PROVE  \E t \in T' : /\ t.State = v'
                                        /\ t.RetW = Ack
                                        /\ t.RetS = v'
        BY <3>8 DEF Inv3C
      <4>1. PICK t \in T : /\ t.State = v
                           /\ t.RetW = Ack
        BY DEF Inv3B
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> Ack,
                         RetS  |-> t.State]
      <4>2. u \in T'
        BY <3>8, <4>1
      <4>3. QED
        BY <3>8, <4>1, <4>2
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv3C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv3C
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv3C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>13. Inv3D'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv3D
    <3>2. CASE L2
      <4>1. CASE /\ pc["W"] = 2
                 /\ X = TRUE
                 /\ pc' = [pc EXCEPT !["W"] = 3]
                 /\ UNCHANGED <<X, A, B, v, a, b, T>>
        PROOF BY <4>1, <3>2 DEF TypeOK, Inv3D, Inv2D
      <4>2. CASE /\ pc["W"] = 2
                 /\ X = FALSE
                 /\ pc' = [pc EXCEPT !["W"] = 4]
                 /\ UNCHANGED <<X, A, B, v, a, b, T>>
        PROOF BY <4>2, <3>2 DEF TypeOK, Inv3D
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2
      
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv3D
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv3D
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv3D
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv3D
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv3D
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["W"] = 3
                   PROVE  (\E t \in T : t.RetW = Bot => (\/ (/\ pc["S"] \in {7, 8}
                                                             /\ B /= Bot
                                                             /\ B /= v)
                                                         \/ (/\ pc["S"] = 8
                                                             /\ A /= a
                                                             /\ B = Bot)))'
        BY <3>8 DEF Inv3D, L8
      <4>1. PICK t \in T : /\ t.State = v
                           /\ t.RetW = Ack
        BY DEF Inv3B
      <4>2. DEFINE u == [State |-> t.State,
                         RetW  |-> Ack,
                         RetS  |-> t.State]
      <4>3. u \in T'
        BY <3>8, <4>1
      <4>4. QED
        BY <3>8, <4>1, <4>3
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv3D
    <3>10. CASE L10
      <4> SUFFICES ASSUME pc["W"] = 3
                   PROVE  (\E t \in T : t.RetW = Bot => (\/ (/\ pc["S"] \in {7, 8}
                                                             /\ B /= Bot
                                                             /\ B /= v)
                                                         \/ (/\ pc["S"] = 8
                                                             /\ A /= a
                                                             /\ B = Bot)))'
        BY <3>10 DEF Inv3D, L10
      <4>1. PICK t \in T : /\ t.RetW = Ack
                           /\ t.RetS /= Bot
        BY <3>10 DEF Inv3B, Inv10B, Inv10E, L10
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> t.RetW,
                         RetS  |-> Bot]
      <4>2. u \in T'
        BY <3>10, <4>1 DEF L10
      <4>3. QED
        BY <4>1, <4>2
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv3D
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>14. Inv4A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv4A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv4A, Inv2A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv4A, Inv3A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv4A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv4A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv4A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv4A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv4A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv4A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv4A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv4A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>15. Inv4B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv4B
    <3>2. CASE L2
      <4>1. CASE /\ pc["W"] = 2
                 /\ X = TRUE
                 /\ pc' = [pc EXCEPT !["W"] = 3]
                 /\ UNCHANGED <<X, A, B, v, a, b, T>>
        PROOF BY <4>1, <3>1 DEF TypeOK, Inv4B
      <4>2. CASE /\ pc["W"] = 2
                 /\ X = FALSE
                 /\ pc' = [pc EXCEPT !["W"] = 4]
                 /\ UNCHANGED <<X, A, B, v, a, b, T>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv4B, Inv2B, Inv2A
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2
      
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv4B, Inv3B, Inv3A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv4B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv4B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv4B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv4B
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["W"] = 4
                   PROVE  \E t \in T' : /\ t.State = A'
                                        /\ t.RetW = Ack
        BY <3>8 DEF Inv4B
      <4>1. PICK t \in T : /\ t.State = A
                           /\ t.RetW = Ack 
        BY <3>8 DEF Inv4B
      <4>2. DEFINE u == [State |-> t.State,
                         RetW  |-> Ack,
                         RetS  |-> t.State]
      <4>3. u \in T'
        BY <3>8, <4>1
      <4>4. QED
        BY <4>1, <4>3
    
       
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv4B
    <3>10. CASE L10
      <4> SUFFICES ASSUME (pc["W"] = 4)'
                   PROVE  (\E t \in T : /\ t.State = A
                                        /\ t.RetW = Ack)'
        BY DEF Inv4B
      <4>1. PICK t \in T : /\ t.State = A
                           /\ t.RetW = Ack
        BY <3>10 DEF L10, Inv4B
      <4>2. t.RetS /= Bot
        BY <3>10 DEF L10, Inv10B
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> t.RetW,
                         RetS  |-> Bot]
      <4>3. u \in T'
        BY <3>10, <4>1, <4>2 DEF L10
      <4>4. QED
        BY <4>1, <4>3
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv4B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>16. Inv4C'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv4C
    <3>2. CASE L2
      <4>1. CASE /\ pc["W"] = 2
                 /\ X = TRUE
                 /\ pc' = [pc EXCEPT !["W"] = 3]
                 /\ UNCHANGED <<X, A, B, v, a, b, T>>
        PROOF BY <4>1, <3>2 DEF TypeOK, Inv4C
      <4>2. CASE /\ pc["W"] = 2
                 /\ X = FALSE
                 /\ pc' = [pc EXCEPT !["W"] = 4]
                 /\ UNCHANGED <<X, A, B, v, a, b, T>>
        PROOF BY <4>2, <3>2 DEF TypeOK, Inv4C, Inv2C, Inv2A
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF L2
       
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv4C, Inv0B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv4C
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv4C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv4C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv4C
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv4C
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv4C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv4C
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv4C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>17. Inv5A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv5A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv5A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv5A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv5A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv5A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv5A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv5A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv5A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv5A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv5A, Inv10A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv5A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>18. Inv5B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv5B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv5B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv5B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv5B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv5B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv5B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv5B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv5B
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv5B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv5B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv5B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>19. Inv5C'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv5A, Inv5C
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv5C
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv5C
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv5C
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv5C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv5C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv5C
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv5C
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv5C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv5C, Inv10E
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv5C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>20. Inv6A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv6A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv6A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv6A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv6A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv6A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv6A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv6A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv6A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv6A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv6A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv6A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>21. Inv6B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv6B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv6B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv6B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv6B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv6B, Inv5B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv6B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv6B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv6B
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv6B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv6B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv6B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>22. Inv7A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv7A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv7A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv7A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv7A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv7A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv7A, Inv6A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv7A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv7A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv7A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv7A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv7A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>23. Inv7B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv7B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv7B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv7B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv7B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv7B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv7B, Inv6B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv7B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv7B
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv7B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv7B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv7B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>24. Inv7C'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc["S"] = 7,
                            B /= Bot
                     PROVE  \E t \in T' : t.State = B
          BY <4>1 DEF Inv7C
        <5>1. B = v
          BY <4>1 DEF Inv7A
        <5>2. PICK t \in T : TRUE
          BY <4>1 DEF Inv1A
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>3. u \in T'
          BY <4>1, <5>2
        <5>4. QED
          BY <5>1, <5>3
        
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv7C
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv7C
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv7C, Inv3B
    <3>4. CASE L4
      <4> SUFFICES ASSUME pc["S"] = 7,
                          B /= Bot
                   PROVE  \E t \in T' : t.State = B
        BY <3>4 DEF Inv7C
      <4>1. PICK t \in T : t.State = B
        BY <3>4 DEF Inv7C
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> Bot,
                         RetS  |-> t.RetS]
      <4>2. u \in T'
        BY <3>4
      <4>3. QED
       BY <4>1, <4>2
      
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv7C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv7C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv7C
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv7C
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv7C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv7C
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv7C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
  
  <2>2.  Inv7D'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc'["S"] = 7,
                            B' = Bot
                     PROVE  \E t_pr \in T' : t_pr.State = A'
          BY <4>1 DEF Inv7D
        <5>1. PICK t \in T : TRUE
          BY <4>1 DEF Inv1A
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>2. /\ u \in T'
              /\ u.State = A'
          BY <4>1, <5>1
\*        PROOF BY <4>1, <3>1 DEF TypeOK, Inv7D, Inv1A, Inv0B
        <5>3. QED
          BY <5>2
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv7D
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv7D
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv7D
    <3>4. CASE L4
      <4> SUFFICES ASSUME pc["S"] = 7,
                          B = Bot
                   PROVE  \E t_pr \in T' : t_pr.State = A'
        BY <3>4 DEF Inv7D
      <4>1. PICK t \in T : t.State = A
        BY <3>4 DEF Inv7D
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> Bot,
                         RetS  |-> t.RetS]
      <4>2. /\ u \in T'
            /\ u.State = A'
        BY <3>4, <4>1
      <4> QED
        PROOF BY <3>4, <4>2 DEF TypeOK, Inv7D
      
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv7D
    <3>6. CASE L6
      <4>1. CASE pc["W"] = 1
        <5> SUFFICES ASSUME pc["S"] = 6,
                            B' = Bot
                     PROVE  \E t_pr \in T' : t_pr.State = A'
          BY <3>6, <4>1 DEF Inv7D
        <5>1. PICK t \in T : t.State = A
          BY <4>1 DEF Inv1A
        <5> QED
          BY <3>6, <4>1, <5>1
      <4>2. CASE pc["W"] = 2
        <5> SUFFICES ASSUME pc["S"] = 6,
                            B' = Bot
                     PROVE  \E t_pr \in T' : t_pr.State = A'
          BY <3>6, <4>2 DEF Inv7D
        <5>1. PICK t \in T : t.State = A
          BY <4>2 DEF Inv2A, Inv2B
        <5> QED
          BY <3>6, <4>2, <5>1
      <4>3. CASE pc["W"] = 3
        <5> SUFFICES ASSUME pc["S"] = 6,
                            B' = Bot
                     PROVE  \E t_pr \in T' : t_pr.State = A'
          BY <3>6, <4>3 DEF Inv7D
        <5>1. PICK t \in T : t.State = A
          BY <4>3 DEF Inv3A, Inv3B
        <5> QED
          BY <3>6, <4>3, <5>1
      <4>4. CASE pc["W"] = 4
        <5> SUFFICES ASSUME pc["S"] = 6,
                            B' = Bot
                     PROVE  \E t_pr \in T' : t_pr.State = A'
          BY <3>6, <4>4 DEF Inv7D
        <5>1. PICK t \in T : t.State = A
          BY <4>4 DEF Inv4A, Inv4B
        <5> QED
          BY <3>6, <4>3, <5>1
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4 DEF TypeOK
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv7D
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv7D
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv7D
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv7D
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv7D
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>25. Inv8A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv8A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv8A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv8A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv8A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv8A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv8A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv8A, Inv7A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv8A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv8A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv8A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv8A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>26. Inv8B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv8B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv8B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv8B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv8B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv8B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv8B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv8B, Inv7B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv8B
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv8B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv8B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv8B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>27. Inv8C'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc["S"] = 8,
                            B /= Bot
                     PROVE  \E t \in T' : t.State = B
          BY <4>1 DEF Inv8C
        <5>1. B = v
          BY <4>1 DEF Inv8A
        <5>2. PICK t \in T : TRUE
          BY <4>1 DEF Inv1A
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>3. u \in T'
          BY <4>1, <5>2
        <5>4. QED
          BY <5>1, <5>3
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv8C
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv8C
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv8C, Inv3B
    <3>4. CASE L4
      <4> SUFFICES ASSUME pc["S"] = 8,
                          B /= Bot
                   PROVE  \E t \in T' : t.State = B
        BY <3>4 DEF Inv8C
      <4>1. PICK t \in T : t.State = B
        BY <3>4 DEF Inv8C
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> Bot,
                         RetS  |-> t.RetS]
      <4>2. u \in T'
        BY <3>4
      <4>3. QED
       BY <4>1, <4>2
      
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv8C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv8C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv8C, Inv7C
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv8C
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv8C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv8C
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv8C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>28. Inv8D'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc'["S"] = 8,
                            B' = Bot
                     PROVE  \E t \in T' : t.State = a'
          BY <4>1 DEF Inv8D
        <5>1. a = v
          BY <4>1 DEF Inv8A
        <5>2. PICK t \in T : TRUE
          BY <4>1 DEF Inv1A
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>3. u \in T'
          BY <4>1, <5>2
        <5>4. QED
          BY <4>1, <5>1, <5>3      
        
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv8D
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv8D
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv8D
    <3>4. CASE L4
      <4> SUFFICES ASSUME pc["S"] = 8,
                          B = Bot
                   PROVE  \E t_pr \in T' : t_pr.State = a'
        BY <3>4 DEF Inv8D
      <4>1. PICK t \in T : t.State = a
        BY <3>4 DEF Inv8D
      <4>   DEFINE u == [State |-> t.State,
                         RetW  |-> Bot,
                         RetS  |-> t.RetS]
      <4>2. /\ u \in T'
            /\ u.State = a'
        BY <3>4, <4>1
      <4> QED
        PROOF BY <3>4, <4>2
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv8D
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv8D
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv8D, Inv7D
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv8D
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv8D
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv8D
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv8D
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
  
  <2>29. Inv9A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv9A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv9A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv9A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv9A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv9A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv9A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv9A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv9A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv9A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv9A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv9A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>30. Inv9B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv9B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv9B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv9B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv9B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv9B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv9B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv9B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv9B
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv9B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv9B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv9B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>31. Inv9C'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc["S"] = 9,
                            B /= Bot
                     PROVE  \E t \in T' : t.RetS = B
          BY <4>1 DEF Inv9C
        <5>1. PICK t \in T : t.RetS = B
          BY <4>1 DEF Inv9C
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>2. /\ u \in T'
              /\ u.RetS = B
          BY <4>1, <5>1
        <5>3. QED
          BY <5>2
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1, Zenon DEF TypeOK, Inv9C
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv9C
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv9C, Inv3C
    <3>4. CASE L4
      PROOF BY <3>4, Isa DEF TypeOK, Inv9C
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv9C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv9C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv9C
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["S"] = 8,
                          B /= Bot
                   PROVE  \E t_pr \in T' : t_pr.RetS = B
        BY <3>8 DEF Inv9C
      <4>1. PICK t \in T : t.State = B
        BY <3>8 DEF Inv8C
      <4>2. CASE t.RetW = Ack
        <5>1. DEFINE u == [State |-> t.State,
                           RetW  |-> Ack,
                           RetS  |-> t.State]
        <5>2. u \in T'
          BY <3>8, <4>1, <4>2
        <5>3. QED
          BY <4>1, <5>2
      <4>3. CASE t.RetW = Bot /\ pc["W"] = 1
        <5>1. DEFINE u == [State |-> t.State,
                           RetW  |-> Bot,
                           RetS  |-> t.State]
        <5>2. u \in T'
          BY <3>8, <4>1, <4>3
        <5>3. QED
          BY <4>1, <5>2
      <4>4. CASE t.RetW = Bot /\ pc["W"] /= 1
        <5>1. DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.State]
        <5>2. u \in T'
          BY <3>8, <4>1, <4>4
        <5>3. QED
          BY <4>1, <5>2      
      <4>5. QED
        BY <4>2, <4>3, <4>4 DEF TypeOK
       
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv9C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv9C
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv9C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>32. Inv9D'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc["S"] = 9,
                            B = Bot
                     PROVE  \E t \in T' : t.RetS = a
          BY <4>1 DEF Inv9D
        <5>1. PICK t \in T : t.RetS = a
          BY <4>1 DEF Inv9D
        <5>   DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>2. /\ u \in T'
              /\ u.RetS = a
          BY <4>1, <5>1
        <5>3. QED
          BY <5>2
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv9D
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv9D
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv9D
    <3>4. CASE L4
      <4> SUFFICES ASSUME pc["S"] = 9,
                          B = Bot
                   PROVE  \E t \in T' : t.RetS = a
        BY <3>4 DEF Inv9D
      <4>1. PICK t \in T : t.RetS = a
        BY <3>4 DEF Inv9D
      <4>2. DEFINE u == [State |-> t.State,
                         RetW  |-> Bot,
                         RetS  |-> t.RetS]
      <4>3. u \in T'
        BY <3>4, <4>1
      <4>4. QED
        BY <4>1, <4>3
      
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv9D
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv9D
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv9D
    <3>8. CASE L8
      <4> SUFFICES ASSUME pc["S"] = 8,
                          B = Bot
                   PROVE  \E t \in T' : t.RetS = a
        BY <3>8 DEF Inv9D
      <4>1. PICK t \in T : t.State = a
        BY <3>8 DEF Inv8D
      <4>2. CASE t.RetW = Ack
        <5>1. DEFINE u == [State |-> t.State,
                           RetW  |-> Ack,
                           RetS  |-> t.State]
        <5>2. u \in T'
          BY <3>8, <4>1, <4>2
        <5>3. QED
          BY <4>1, <5>2
      <4>3. CASE t.RetW = Bot /\ pc["W"] = 1
        <5>1. DEFINE u == [State |-> t.State,
                           RetW  |-> Bot,
                           RetS  |-> t.State]
        <5>2. u \in T'
          BY <3>8, <4>1, <4>3
        <5>3. QED
          BY <4>1, <5>2
      <4>4. CASE t.RetW = Bot /\ pc["W"] /= 1
        <5>1. DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.State]
        <5>2. u \in T'
          BY <3>8, <4>1, <4>4
        <5>3. QED
          BY <4>1, <5>2      
      <4>5. QED
        BY <4>2, <4>3, <4>4 DEF TypeOK
      
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv9D
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv9D
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv9D
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>33. Inv9E'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv9A, Inv9E
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv9E
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv9E
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv9E
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv9E
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv9E
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv9E
    <3>8. CASE L8
      <4>1. (\A t \in T : pc["W"] /= 1 => t.RetW = Ack)'
        PROOF BY <3>8 DEF Inv9E
      <4>2. (\A t \in T : t.State = A)'
        <5> SUFFICES ASSUME NEW u \in T'
                     PROVE  u.State = A
          BY <3>8
        <5>1. CASE \E t \in T : /\ t.RetW = Bot
                                /\ pc["W"] /= 1
                                /\ u.State = v
                                /\ u.RetW = Ack
                                /\ u.RetS = t.State
          <6>1. v = A
            BY <5>1 DEF TypeOK, Inv2A, Inv3A, Inv4A
          <6>2. QED
            BY <5>1, <6>1
        <5>2. CASE \E t \in T : /\ t.RetW = Bot
                                /\ pc["W"] = 1
                                /\ u.State = t.State
                                /\ u.RetW = Bot
                                /\ u.RetS = t.State
          <6>1. \A t \in T : t.State = A
            BY <5>2 DEF Inv1B
          <6>2. QED
            BY <5>2, <6>1
        <5>3. CASE \E t \in T : /\ t.RetW = Ack
                                /\ u.State = t.State
                                /\ u.RetW = Ack
                                /\ u.RetS = t.State
          <6>1. \A t \in T : t.RetW = Ack => t.State = A
            BY DEF Inv0B
          <6>2. QED
            BY <5>3, <6>1                                
        <5>4. QED
          BY <3>8, <5>1, <5>2, <5>3
\*        PROOF BY <3>8 DEF Inv8A, Inv8B, Inv1A, Inv1B, Inv2A, Inv2C, Inv3A, Inv4A
      <4>3. QED
        BY <4>1, <4>2 DEF Inv9E
      
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv9E
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv9E
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv9E
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>34. Inv10A'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv10A
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv10A
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv10A
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv10A
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv10A
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv10A
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv10A
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv10A
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv10A, Inv9A
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv10A
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv10A
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>35. Inv10B'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv10B
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv10B
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv10B
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv10B
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv10B
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv10B
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv10B
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv10B
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv10B, Inv9B
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv10B
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv10B
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>36. Inv10C'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc["S"] = 10,
                            b /= Bot
                     PROVE  \E t \in T' : t.RetS = b
          BY <4>1 DEF Inv10C
        <5>1. PICK t \in T : t.RetS = b
          BY <4>1 DEF Inv10C
        <5>2. DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>3. u \in T'
          BY <4>1
        <5>4. QED
          BY <4>1, <5>1, <5>3
          
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv10C
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv10C
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv10C, Inv10E
    <3>4. CASE L4
      PROOF BY <3>4, Isa DEF TypeOK, Inv10C
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv10C
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv10C
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv10C
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv10C
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv10C, Inv9C
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv10C
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv10C
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>37. Inv10D'
    <3>1. CASE L1
      <4>1. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (\/ X = FALSE
                     \/ pc["S"] = 6
                     \/ (/\ pc["S"] = 7 
                         /\ B = Bot)
                     \/ B = v
                     \/ (/\ pc["S"] = 8 
                         /\ B = Bot
                         /\ a = v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T}
                 /\ UNCHANGED <<X, B, v, a, b>>
        <5> SUFFICES ASSUME pc["S"] = 10,
                            b = Bot
                     PROVE  \E t \in T' : t.RetS = a
          BY <4>1 DEF Inv10D
        <5>1. PICK t \in T : t.RetS = a
          BY <4>1 DEF Inv10D
        <5>2. DEFINE u == [State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS]
        <5>3. u \in T'
          BY <4>1
        <5>4. QED
          BY <4>1, <5>1, <5>3
      <4>2. CASE /\ pc["W"] = 1    
                 /\ pc' = [pc EXCEPT !["W"] = 2]
                 /\ A' = v
                 /\ (/\ X = TRUE
                     /\ pc["S"] /= 6
                     /\ (\/ pc["S"] /= 7 
                         \/ B /= Bot)
                     /\ B /= v
                     /\ (\/ pc["S"] /= 8 
                         \/ B /= Bot 
                         \/ a /= v))
                 /\ T' = {[State |-> v,
                           RetW  |-> Ack,
                           RetS  |-> t.RetS] : t \in T} \union T
                 /\ UNCHANGED <<X, B, v, a, b>>
        PROOF BY <4>2, <3>1 DEF TypeOK, Inv10D
      <4>3. QED
        BY <3>1, <4>1, <4>2 DEF L1
      
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv10D
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv10D, Inv10E
    <3>4. CASE L4
      PROOF BY <3>4, Isa DEF TypeOK, Inv10D
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv10D
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv10D
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv10D
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv10D
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv10D, Inv9D
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv10D
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv10D
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>38. Inv10E'
    <3>1. CASE L1
      PROOF BY <3>1 DEF TypeOK, Inv10A, Inv10E
    <3>2. CASE L2
      PROOF BY <3>2 DEF TypeOK, Inv10E
    <3>3. CASE L3
      PROOF BY <3>3 DEF TypeOK, Inv10E
    <3>4. CASE L4
      PROOF BY <3>4 DEF TypeOK, Inv10E
    <3>5. CASE L5
      PROOF BY <3>5 DEF TypeOK, Inv10E
    <3>6. CASE L6
      PROOF BY <3>6 DEF TypeOK, Inv10E
    <3>7. CASE L7
      PROOF BY <3>7 DEF TypeOK, Inv10E
    <3>8. CASE L8
      PROOF BY <3>8 DEF TypeOK, Inv10E
    <3>9. CASE L9
      PROOF BY <3>9 DEF TypeOK, Inv9E, Inv10E
    <3>10. CASE L10
      PROOF BY <3>10 DEF TypeOK, Inv10E
    <3>11. CASE UNCHANGED vars
      PROOF BY <3>11 DEF TypeOK, Inv10E
    <3>12. QED
      BY <3>1, <3>10, <3>11, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
    
  <2>39. QED
    BY <2>1, <2>2, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>17, <2>18, <2>19, <2>20, <2>21, <2>22, <2>23, <2>24, <2>25, <2>26, <2>27, <2>28, <2>29, <2>3, <2>30, <2>31, <2>32, <2>33, <2>34, <2>35, <2>36, <2>37, <2>38, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF IInv
   
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
  


=============================================================================
\* Modification History
\* Last modified Fri May 14 16:54:04 EDT 2021 by uguryavuz
\* Created Thu May 13 11:08:51 EDT 2021 by uguryavuz
