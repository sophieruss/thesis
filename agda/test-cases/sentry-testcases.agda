module agda.test-cases.sentry-testcases where

open import agda.commands
open import agda.sentry
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Agda.Builtin.List

-- 'Enable' test pc+1
test-prog : Program 4
test-prog = program ( Enable ∷ Enable ∷ Enable ∷ Enable ∷ [] )

r32 r32-evil : Vec ℕ 32
r32 = replicate 32 0
r32-evil = updateAt r32 (# 0) (λ x → 1)

state0 = [ 0 , r32 ]
state1 = [ 1 , r32 ]
state2 = [ 2 , r32 ]
state3 = [ 3 , r32 ]

t-Enable : Trace
t-Enable = ⟨ Enable , 0 ∷ 0 ∷ 0 ∷ [] ⟩

test-step-Enable : t-Enable , test-prog , state2 —→ state3
test-step-Enable = step-Enable t-Enable test-prog state2 (s≤s (s≤s (s≤s z≤n))) refl

test-multi-step-Enable : t-Enable , test-prog , state1 —→* state3 

test-multi-step-Enable = step—→ test-prog state1 state2 state3 t-Enable t-Enable 2—→*3 1—→2 
 where
  1—→2 : t-Enable , test-prog , state1 —→ state2
  1—→2 = step-Enable t-Enable test-prog state1 (s≤s (s≤s z≤n)) refl

  2—→*3 : t-Enable , test-prog , state2 —→* state3
  2—→*3  = step—→ test-prog state2 state3 state3 t-Enable emptyTrace 3—→*3 2—→3
    where
    2—→3 : t-Enable , test-prog , state2 —→ state3
    2—→3 = step-Enable t-Enable test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl

    3—→*3 : emptyTrace , test-prog , state3 —→* state3
    3—→*3 = done emptyTrace test-prog state3

-- 'NoOp' test
test-prog-NoOp : Program 4
test-prog-NoOp = program ( NoOp ∷ NoOp ∷ NoOp ∷ NoOp ∷ [] )

state000 = [ 0 , r32 ]

t-NoOp : Trace
t-NoOp = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

test-step-noOp : t-NoOp , test-prog-NoOp , state000 —→ state000
test-step-noOp = step-NoOp t-NoOp test-prog-NoOp state000 (s≤s z≤n) refl


-- 'Disable' test
test-prog-Disable : Program 4
test-prog-Disable = program ( Disable ∷ Disable ∷ Disable ∷ Disable ∷ [] )

state001 = [ 0 , r32 ]
state002 = [ 2 , r32 ]


t-Disable : Trace
t-Disable = ⟨ Disable , 0 ∷ 0 ∷ 0 ∷ [] ⟩

test-step-Disable : t-Disable , test-prog-Disable , state001 —→ state002
test-step-Disable = step-Disable t-Disable test-prog-Disable state001 (s≤s z≤n) refl


-- 'ADD' test
test-prog-add : Program 4
test-prog-add = program ( Add (# 2) (# 1) (# 0) ∷ Add (# 3) (# 2) (# 1) ∷ Add (# 4) (# 3) (# 2) ∷ Add (# 5) (# 4) (# 3)  ∷  [] )

r32-add-a r32-add-b r32-add-c r32-add-d : Vec ℕ 32
r32-add-a = 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-b = 1 ∷ 1 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-c = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-d = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

statea = [ 0 , r32-add-a ]
stateb = [ 1 , r32-add-b ]
statec = [ 2 , r32-add-c ]
stated = [ 3 , r32-add-d ]

ta = ⟨ Add (# 2) (# 1) (# 0) , 1 ∷ 1 ∷ 2 ∷ [] ⟩
tb = ⟨ Add (# 3) (# 2) (# 1) , 2 ∷ 1 ∷ 3 ∷ [] ⟩
tc = ⟨ Add (# 4) (# 3) (# 2) , 3 ∷ 2 ∷ 5 ∷ [] ⟩
td = ⟨ Add (# 5) (# 4) (# 3) , 5 ∷ 3 ∷ 8 ∷ [] ⟩

test-step-add-ab : ta , test-prog-add , statea —→ stateb
test-step-add-ab = step-Add ta test-prog-add statea (s≤s z≤n) refl

test-step-add-bc : tb , test-prog-add , stateb —→ statec
test-step-add-bc = step-Add tb test-prog-add stateb (s≤s (s≤s z≤n)) refl

test-step-add-cd : tc , test-prog-add , statec —→ stated 
test-step-add-cd = step-Add tc test-prog-add statec (s≤s (s≤s (s≤s z≤n))) refl

test-step-add-d→*d : emptyTrace , test-prog-add , stated —→* stated
test-step-add-d→*d = done emptyTrace test-prog-add stated 

test-step-add-c→*d : tc , test-prog-add , statec —→* stated
test-step-add-c→*d = step—→ test-prog-add statec stated stated tc emptyTrace test-step-add-d→*d test-step-add-cd 

test-step-add-b→*d : tb , test-prog-add , stateb —→* stated
test-step-add-b→*d = step—→ test-prog-add stateb statec stated tb tc test-step-add-c→*d test-step-add-bc

-- 'SUB' test
test-prog-sub : Program 1
test-prog-sub = program ( Sub (# 0) (# 1) (# 2) ∷ [] )

r32-sub-start r32-sub-end : Vec ℕ 32
r32-sub-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-sub-end = 3 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

stateI = [ 0 , r32-sub-start ]
stateII = [ 1 , r32-sub-end  ]

t-sub = ⟨ Sub (# 0) (# 1) (# 2) , 10 ∷ 7 ∷ 3 ∷ [] ⟩

test-step-sub : _ , test-prog-sub , stateI —→ stateII
test-step-sub =  step-Sub t-sub test-prog-sub stateI (s≤s z≤n) refl


-- 'Addi' test
test-prog-addi : Program 1
test-prog-addi = program ( Addi (# 0) (# 1) 500 ∷ [] )


r32-addi-start r32-addi-end : Vec ℕ 32
r32-addi-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-addi-end = 510 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-one = [ 0 , r32-addi-start ]
state-two = [ 1 , r32-addi-end ]

addi-trace = ⟨ Addi (# 0) (# 1) 500 , 10 ∷ 510 ∷ 0 ∷ [] ⟩

test-step-addi : addi-trace , test-prog-addi , state-one —→ state-two 
test-step-addi =  step-Addi addi-trace  test-prog-addi state-one (s≤s z≤n) refl


-- 'Jump' test
test-prog-jmp : Program 4
test-prog-jmp = program ( Jump 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-jmp : Vec ℕ 32
r32-jmp = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-uno = [ 0 , r32-jmp ]
state-dos = [ 3 , r32-jmp ]

jmp-trace = ⟨ Jump 3 , 3 ∷ 0 ∷ 0 ∷ [] ⟩

test-step-jmp : jmp-trace , test-prog-jmp , state-uno —→ state-dos 
test-step-jmp = step-Jump jmp-trace test-prog-jmp state-uno  (s≤s z≤n) ((s≤s (s≤s (s≤s (s≤s z≤n))))) refl

-- 'Bgtz' test
test-prog-bgtz-g test-prog-bgtz-l : Program 4
test-prog-bgtz-g = program ( Bgtz (# 1) 3 ∷ Enable ∷ Enable ∷ Add (# 0) (# 1) (# 2) ∷ [] )
test-prog-bgtz-l = program ( Bgtz (# 0) 3 ∷ Enable ∷ Enable ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-bgtz-g : Vec ℕ 32
r32-bgtz-g = 0 ∷ 1 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-i = [ 0 , r32-bgtz-g ]
state-ii-l = [ 1 , r32-bgtz-g ]
state-ii-g = [ 3 , r32-bgtz-g ]

bgtz-g-trace = ⟨ Bgtz (# 1) 3 , 1 ∷ 3 ∷ 0 ∷ [] ⟩
bgtz-l-trace = ⟨ Bgtz (# 0) 3 , 0 ∷ 1 ∷ 0 ∷ [] ⟩

-- greater
test-step-bgtz-g : bgtz-g-trace , test-prog-bgtz-g , state-i —→ state-ii-g
test-step-bgtz-g = step-Bgtz-g bgtz-g-trace (test-prog-bgtz-g) state-i (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl

-- less
test-step-bgtz-l :  bgtz-l-trace , test-prog-bgtz-l , state-i —→ state-ii-l
test-step-bgtz-l = step-Bgtz-l bgtz-l-trace test-prog-bgtz-l state-i (s≤s z≤n)  (s≤s (s≤s (s≤s (s≤s z≤n)))) refl refl



     