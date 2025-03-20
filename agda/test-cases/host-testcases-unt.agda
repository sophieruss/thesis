
module agda.test-cases.host-testcases-unt where

open import agda.commands hiding (State)
open import agda.host-unt
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Agda.Builtin.List
open import Data.Bool using (Bool; true; false)


-- 'Enable' test
test-prog : Program 4
test-prog = program ( Enable ∷ Enable ∷ Enable ∷ Enable ∷ [] )

r32 r32-evil : Vec ℕ 32
r32 = replicate 32 0
r32-evil = updateAt r32 (# 0) (λ x → 1)

state0 = [[ 0 , r32 , true , r32 ]]
state1 = [[ 1 , r32 , true , r32 ]]
state2 = [[ 2 , r32 , true , r32 ]]
state3 = [[ 3 , r32 , true , r32 ]]

t-enable : Trace
t-enable = ⟨ Enable , 0 ∷ 0 ∷ 0 ∷ [] ⟩

test-step-enable : test-prog , state2 —→ state3 , t-enable
test-step-enable = step-Enable test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl
-- test-step = step-Enable test-prog state2 (s<s (s<s z<s))

test-multi-step-Enable : test-prog , state1 —→* state3 , emptyTrace
test-multi-step-Enable = step—→ test-prog state1 state2 state3 t-enable emptyTrace 2—→*3 1—→2
  where
  1—→2 : test-prog , state1 —→ state2 , t-enable
  1—→2 = step-Enable test-prog state1 (s≤s (s≤s z≤n)) refl

  2—→*3 : test-prog , state2 —→* state3 , emptyTrace
  2—→*3  = step—→ test-prog state2 state3 state3 t-enable emptyTrace 3—→*3 2—→3
    where
    2—→3 : test-prog , state2 —→ state3 , t-enable
    2—→3 = step-Enable test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl

    3—→*3 : test-prog , state3 —→* state3 , emptyTrace
    3—→*3 = done test-prog state3

-- 'Disable' test
test-prog-d : Program 4
test-prog-d = program ( Disable ∷ Disable ∷ Disable ∷ Disable ∷ [] )
t-disable : Trace
t-disable = ⟨ Disable , 0 ∷ 0 ∷ 0 ∷ [] ⟩

test-step-disable : test-prog-d , state2 —→ state3 , t-disable
test-step-disable = step-Disable test-prog-d state2 ((s≤s (s≤s (s≤s z≤n)))) refl

-- 'NoOp' test
test-prog-NoOp : Program 4
test-prog-NoOp = program ( NoOp ∷ NoOp ∷ NoOp ∷ NoOp ∷ [] )
t-NoOp : Trace
t-NoOp = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

test-step-NoOp : test-prog-NoOp , state0 —→ state0 , t-NoOp
test-step-NoOp = step-NoOp test-prog-NoOp state0 (s≤s z≤n) refl


-- 'ADD' test
test-prog-add : Program 4
test-prog-add = program ( Add (# 2) (# 1) (# 0) ∷ Add (# 3) (# 2) (# 1) ∷ Add (# 4) (# 3) (# 2) ∷ Add (# 5) (# 4) (# 3)  ∷  [] )

r32-add-a r32-add-b r32-add-c r32-add-d : Vec ℕ 32
r32-add-a = 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-b = 1 ∷ 1 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-c = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-d = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

statea = [[ 0 , r32-add-a , true , r32 ]]
statea_ = [[ 0 , r32-add-a , false , r32 ]]
stateb = [[ 1 , r32-add-b , true , r32 ]]
stateb_ = [[ 1 , r32-add-b , false , r32 ]]
statec = [[ 2 , r32-add-c , true , r32 ]]
stated = [[ 3 , r32-add-d , true , r32 ]]

ta = ⟨ Add (# 2) (# 1) (# 0) , 1 ∷ 1 ∷ 2 ∷ [] ⟩
tb = ⟨ Add (# 3) (# 2) (# 1) , 2 ∷ 1 ∷ 3 ∷ [] ⟩
tc = ⟨ Add (# 4) (# 3) (# 2) , 3 ∷ 2 ∷ 5 ∷ [] ⟩
td = ⟨ Add (# 5) (# 4) (# 3) , 5 ∷ 3 ∷ 8 ∷ [] ⟩

test-step-add-ab-unt : test-prog-add , statea_ —→ stateb_ , t-NoOp
test-step-add-ab-unt = step-Add test-prog-add statea_ (s≤s z≤n) refl

test-step-add-ab : test-prog-add , statea —→ stateb , ta
test-step-add-ab = step-Add test-prog-add statea (s≤s z≤n) refl

test-step-add-bc : test-prog-add , stateb —→ statec , tb
test-step-add-bc = step-Add test-prog-add stateb (s≤s (s≤s z≤n)) refl

test-step-add-cd : test-prog-add , statec —→ stated , tc
test-step-add-cd = step-Add test-prog-add statec (s≤s (s≤s (s≤s z≤n))) refl

test-step-add-d→*d :  test-prog-add , stated —→* stated , ⟨ Empty , 0 ∷ 0 ∷ 0 ∷ [] ⟩
test-step-add-d→*d = done test-prog-add stated 

test-step-add-c→*d : test-prog-add , statec —→* stated , emptyTrace
test-step-add-c→*d = step—→ test-prog-add statec stated stated tc emptyTrace test-step-add-d→*d test-step-add-cd 

test-step-add-b→*d : test-prog-add , stateb —→* stated , emptyTrace
test-step-add-b→*d = step—→ test-prog-add stateb statec stated tb emptyTrace test-step-add-c→*d test-step-add-bc

-- 'SUB' test
test-prog-sub : Program 1
test-prog-sub = program ( Sub (# 0) (# 1) (# 2) ∷ [] )

r32-sub-start r32-sub-end : Vec ℕ 32
r32-sub-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-sub-end = 3 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

stateI = [[ 0 , r32-sub-start , true , r32 ]]
stateII = [[ 1 , r32-sub-end  , true , r32 ]]

t-sub = ⟨ Sub (# 0) (# 1) (# 2) , 10 ∷ 7 ∷ 3 ∷ [] ⟩

test-step-sub : test-prog-sub , stateI —→ stateII , t-sub
test-step-sub =  step-Sub test-prog-sub stateI (s≤s z≤n) refl


-- 'Addi' test
test-prog-addi : Program 1
test-prog-addi = program ( Addi (# 0) (# 1) 500 ∷ [] )


r32-addi-start r32-addi-end : Vec ℕ 32
r32-addi-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-addi-end = 510 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-one = [[ 0 , r32-addi-start , true , r32 ]]
state-two = [[ 1 , r32-addi-end , true , r32 ]]

test-step-addi : test-prog-addi , state-one —→ state-two , ⟨ Addi (# 0) (# 1) 500 , 10 ∷ 510 ∷ 0 ∷ [] ⟩
test-step-addi =  step-Addi test-prog-addi state-one (s≤s z≤n) refl


-- 'Jump' test
test-prog-jmp : Program 4
test-prog-jmp = program ( Jump 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-jmp : Vec ℕ 32
r32-jmp = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-uno = [[ 0 , r32-jmp , true , r32 ]]
state-dos = [[ 3 , r32-jmp , true , r32 ]]

test-step-jmp : test-prog-jmp , state-uno —→ state-dos , ⟨ Jump 3 , 3 ∷ 0 ∷ 0 ∷ [] ⟩
test-step-jmp = step-Jump test-prog-jmp state-uno  (s≤s z≤n) ((s≤s (s≤s (s≤s (s≤s z≤n))))) refl

-- 'Bgtz' test
test-prog-bgtz-g test-prog-bgtz-l : Program 4
test-prog-bgtz-g = program ( Bgtz (# 1) 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )
test-prog-bgtz-l = program ( Bgtz (# 0) 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-bgtz-g : Vec ℕ 32
r32-bgtz-g = 0 ∷ 1 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-i = [[ 0 , r32-bgtz-g , true , r32 ]]
state-ii-l = [[ 1 , r32-bgtz-g , true , r32 ]]
state-ii-g = [[ 3 , r32-bgtz-g , true , r32 ]]

-- greater
test-step-bgtz-g : test-prog-bgtz-g , state-i —→ state-ii-g , ⟨ Bgtz (# 1) 3 , 1 ∷ 3 ∷ 0 ∷ [] ⟩
test-step-bgtz-g = step-Bgtz-g (test-prog-bgtz-g) state-i (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl

-- less
test-step-bgtz-l : test-prog-bgtz-l , state-i —→ state-ii-l , ⟨ Bgtz (# 0) 3 , 0 ∷ 1 ∷ 0 ∷ [] ⟩
test-step-bgtz-l = step-Bgtz-l test-prog-bgtz-l state-i (s≤s z≤n)  (s≤s (s≤s (s≤s (s≤s z≤n)))) refl refl



      