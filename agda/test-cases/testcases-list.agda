
module agda.test-cases.testcases-list where

open import agda.commands-list
open import agda.steps-list
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Agda.Builtin.List


-- 'NoOp' test
test-prog : Program 4
test-prog = program ( NoOp ∷ NoOp ∷ NoOp ∷ NoOp ∷ [] )

r32 r32-evil : Vec ℕ 32
r32 = replicate 32 0
r32-evil = updateAt r32 (# 0) (λ x → 1)

state0 = [ 0 , r32 , [] ] 
state1 = [ 1 , r32 , [] ] 
state2 = [ 2 , r32 , [] ]
state3 = [ 3 , r32 , [] ]

test-step-noOp : test-prog , state2 —→ state3  
test-step-noOp = step-NoOp test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl
-- -- test-step = step-NoOp test-prog state2 (s<s (s<s z<s))

test-multi-step-noOp : test-prog , state1 —→* state3
test-multi-step-noOp = step—→ test-prog state1 state2 state3 2—→*3 1—→2
  where
  1—→2 : test-prog , state1 —→ state2
  1—→2 = step-NoOp test-prog state1 ((s≤s (s≤s z≤n))) refl

  2—→*3 : test-prog , state2 —→* state3
  2—→*3  = step—→ test-prog state2 state3 state3 (done test-prog state3) 2—→3
    where
    2—→3 : test-prog , state2 —→ state3
    2—→3 = step-NoOp test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl


-- 'ADD' test
test-prog-add : Program 4
test-prog-add = program ( Add (# 2) (# 1) (# 0) ∷ Add (# 3) (# 2) (# 1) ∷ Add (# 4) (# 3) (# 2) ∷ Add (# 5) (# 4) (# 3)  ∷  [] )

r32-add-a r32-add-b r32-add-c r32-add-d : Vec ℕ 32
r32-add-a = 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-b = 1 ∷ 1 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-c = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-d = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

statea = [ 0 , r32-add-a , [] ]
stateb = [ 1 , r32-add-b , [] ]
statec = [ 2 , r32-add-c , [] ]
stated = [ 3 , r32-add-d , [] ]

test-step-add : test-prog-add , statea —→ stateb 
test-step-add = step-Add test-prog-add statea (s≤s z≤n) refl

test-multi-step-add : test-prog-add , statea —→* stated
test-multi-step-add = step—→ test-prog-add statea stateb stated  b—→*d a—→b
  where
  a—→b : test-prog-add , statea —→ stateb
  a—→b = step-Add test-prog-add statea (s≤s z≤n) refl

  b—→*d : test-prog-add , stateb —→* stated
  b—→*d  = step—→ test-prog-add stateb statec stated ((step—→ test-prog-add statec stated stated (done test-prog-add stated) c—→d)) b—→c
    where
    
    b—→c : test-prog-add , stateb —→ statec
    b—→c = step-Add test-prog-add stateb(s≤s (s≤s z≤n)) refl

    c—→d : test-prog-add , statec —→ stated
    c—→d =  step-Add test-prog-add statec (s≤s (s≤s (s≤s z≤n))) refl 
   

-- 'SUB' test
test-prog-sub : Program 1
test-prog-sub = program ( Sub (# 0) (# 1) (# 2) ∷ [] )

r32-sub-start r32-sub-end : Vec ℕ 32
r32-sub-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-sub-end = 3 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

stateI = [ 0 , r32-sub-start , [] ]
stateII = [ 1 , r32-sub-end  , [] ]

test-step-sub : test-prog-sub , stateI —→ stateII
test-step-sub =  step-Sub test-prog-sub stateI (s≤s z≤n) refl


-- 'Addi' test
test-prog-addi : Program 1
test-prog-addi = program ( Addi (# 0) (# 1) 500 ∷ [] )


r32-addi-start r32-addi-end : Vec ℕ 32
r32-addi-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-addi-end = 510 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-one = [ 0 , r32-addi-start , [] ]
state-two = [ 1 , r32-addi-end , [] ]

test-step-addi : test-prog-addi , state-one —→ state-two
test-step-addi =  step-Addi test-prog-addi state-one (s≤s z≤n) refl



-- 'Jump' test
test-prog-jmp : Program 4
test-prog-jmp = program ( Jump 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-jmp : Vec ℕ 32
r32-jmp = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-uno = [ 0 , r32-jmp , [] ]
state-dos = [ 3 , r32-jmp , [] ]

test-step-jmp : test-prog-jmp , state-uno —→ state-dos
test-step-jmp = step-Jump test-prog-jmp state-uno  (s≤s z≤n) ((s≤s (s≤s (s≤s (s≤s z≤n))))) refl

-- 'Bgtz' test
test-prog-bgtz-g test-prog-bgtz-l : Program 4
test-prog-bgtz-g = program ( Bgtz (# 1) 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )
test-prog-bgtz-l = program ( Bgtz (# 0) 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-bgtz-g : Vec ℕ 32
r32-bgtz-g = 0 ∷ 1 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-i = [ 0 , r32-bgtz-g , [] ]
state-ii-l = [ 1 , r32-bgtz-g , [] ]
state-ii-g = [ 3 , r32-bgtz-g , [] ]

-- greater
test-step-bgtz-g : test-prog-bgtz-g , state-i —→ state-ii-g
test-step-bgtz-g = step-Bgtz-g (test-prog-bgtz-g) state-i (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl

-- less
test-step-bgtz-l : test-prog-bgtz-l , state-i —→ state-ii-l
test-step-bgtz-l = step-Bgtz-l test-prog-bgtz-l state-i (s≤s z≤n)  (s≤s (s≤s (s≤s (s≤s z≤n)))) refl refl



