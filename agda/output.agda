
module agda.output where
open import agda.sentry
open import agda.commands
open import agda.host
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

state0 = [ 0 , r32 ]
state1 = [ 1 , r32 ]
state2 = [ 2 , r32 ]
state3 = [ 3 , r32 ]

t-NoOp : Trace
t-NoOp = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

sentry_test-step-noOp : t-NoOp , test-prog , state2 —→ state3
sentry_test-step-noOp = step-NoOp t-NoOp test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl
-- test-step = step-NoOp test-prog state2 (s<s (s<s z<s))

sentry_test-multi-step-noOp : t-NoOp , test-prog , state1 —→* state3
sentry_test-multi-step-noOp = step—→ test-prog state1 state2 state3 t-NoOp t-NoOp sentry_2—→*3 sentry_1—→2
  where
  sentry_1—→2 : t-NoOp , test-prog , state1 —→ state2
  sentry_1—→2 = step-NoOp t-NoOp test-prog state1 (s≤s (s≤s z≤n)) refl

  sentry_2—→*3 : t-NoOp , test-prog , state2 —→* state3
  sentry_2—→*3 = step—→ test-prog state2 state3 state3 t-NoOp emptyTrace sentry_3—→*3 sentry_2—→3
    where
    sentry_2—→3 : t-NoOp , test-prog , state2 —→ state3
    sentry_2—→3 = step-NoOp t-NoOp test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl

    sentry_3—→*3 : emptyTrace , test-prog , state3 —→* state3
    sentry_3—→*3 = done emptyTrace test-prog state3

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

sentry_test-step-add-ab : ta , test-prog-add , statea —→ stateb
sentry_test-step-add-ab = step-Add ta test-prog-add statea (s≤s z≤n) refl

sentry_test-step-add-bc : tb , test-prog-add , stateb —→ statec
sentry_test-step-add-bc = step-Add tb test-prog-add stateb (s≤s (s≤s z≤n)) refl

sentry_test-step-add-cd : tc , test-prog-add , statec —→ stated
sentry_test-step-add-cd = step-Add tc test-prog-add statec (s≤s (s≤s (s≤s z≤n))) refl

sentry_test-step-add-d→*d : ⟨ Empty , 0 ∷ 0 ∷ 0 ∷ [] ⟩ , test-prog-add , stated —→* stated
sentry_test-step-add-d→*d = done ⟨ Empty , 0 ∷ 0 ∷ 0 ∷ [] ⟩ test-prog-add stated

sentry_test-step-add-c→*d : tc , test-prog-add , statec —→* stated
sentry_test-step-add-c→*d = step—→ test-prog-add statec stated stated tc emptyTrace sentry_test-step-add-d→*d sentry_test-step-add-cd

sentry_test-step-add-b→*d : tb , test-prog-add , stateb —→* stated
sentry_test-step-add-b→*d = step—→ test-prog-add stateb statec stated tb tc sentry_test-step-add-c→*d sentry_test-step-add-bc

-- 'SUB' test
test-prog-sub : Program 1
test-prog-sub = program ( Sub (# 0) (# 1) (# 2) ∷ [] )

r32-sub-start r32-sub-end : Vec ℕ 32
r32-sub-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-sub-end = 3 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

stateI = [ 0 , r32-sub-start ]
stateII = [ 1 , r32-sub-end  ]

t-sub = ⟨ Sub (# 0) (# 1) (# 2) , 10 ∷ 7 ∷ 3 ∷ [] ⟩

sentry_test-step-sub : t-sub , test-prog-sub , stateI —→ stateII
sentry_test-step-sub = step-Sub t-sub test-prog-sub stateI (s≤s z≤n) refl


-- 'Addi' test
test-prog-addi : Program 1
test-prog-addi = program ( Addi (# 0) (# 1) 500 ∷ [] )


r32-addi-start r32-addi-end : Vec ℕ 32
r32-addi-start = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-addi-end = 510 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-one = [ 0 , r32-addi-start ]
state-two = [ 1 , r32-addi-end ]

sentry_test-step-addi : ⟨ Addi (# 0) (# 1) 500 , 10 ∷ 510 ∷ 0 ∷ [] ⟩ , test-prog-addi , state-one —→ state-two
sentry_test-step-addi = step-Addi ⟨ Addi (# 0) (# 1) 500 , 10 ∷ 510 ∷ 0 ∷ [] ⟩ test-prog-addi state-one (s≤s z≤n) refl


-- 'Jump' test
test-prog-jmp : Program 4
test-prog-jmp = program ( Jump 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-jmp : Vec ℕ 32
r32-jmp = 1 ∷ 10 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-uno = [ 0 , r32-jmp ]
state-dos = [ 3 , r32-jmp ]

sentry_test-step-jmp : ⟨ Jump 3 , 3 ∷ 0 ∷ 0 ∷ [] ⟩ , test-prog-jmp , state-uno —→ state-dos
sentry_test-step-jmp = step-Jump ⟨ Jump 3 , 3 ∷ 0 ∷ 0 ∷ [] ⟩ test-prog-jmp state-uno (s≤s z≤n) ((s≤s (s≤s (s≤s (s≤s z≤n))))) refl

-- 'Bgtz' test
test-prog-bgtz-g test-prog-bgtz-l : Program 4
test-prog-bgtz-g = program ( Bgtz (# 1) 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )
test-prog-bgtz-l = program ( Bgtz (# 0) 3 ∷ NoOp ∷ NoOp ∷ Add (# 0) (# 1) (# 2) ∷ [] )

r32-bgtz-g : Vec ℕ 32
r32-bgtz-g = 0 ∷ 1 ∷ 7 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state-i = [ 0 , r32-bgtz-g ]
state-ii-l = [ 1 , r32-bgtz-g ]
state-ii-g = [ 3 , r32-bgtz-g ]

-- greater
sentry_test-step-bgtz-g : ⟨ Bgtz (# 1) 3 , 1 ∷ 3 ∷ 0 ∷ [] ⟩ , test-prog-bgtz-g , state-i —→ state-ii-g
sentry_test-step-bgtz-g = step-Bgtz-g ⟨ Bgtz (# 1) 3 , 1 ∷ 3 ∷ 0 ∷ [] ⟩ (test-prog-bgtz-g) state-i (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl

-- less
sentry_test-step-bgtz-l : ⟨ Bgtz (# 0) 3 , 0 ∷ 1 ∷ 0 ∷ [] ⟩ , test-prog-bgtz-l , state-i —→ state-ii-l
sentry_test-step-bgtz-l = step-Bgtz-l ⟨ Bgtz (# 0) 3 , 0 ∷ 1 ∷ 0 ∷ [] ⟩ test-prog-bgtz-l state-i (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) refl refl



     
