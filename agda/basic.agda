module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Agda.Primitive
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)


data Instruction : Set where
  NoOp  : Instruction
  Add   : Fin 32 → Fin 32 → Fin 32 → Instruction

record Program (n : ℕ) : Set where
  constructor program
  field 
    instructions : Vec Instruction n

record State : Set where
  constructor [_,_]
  field
    pc : ℕ
    registers : Vec ℕ 32
   
   
addHelper : Vec ℕ 32 →  Fin 32 → Fin 32 → Fin 32 → Vec ℕ 32
addHelper vec dest r1 r2 = 
  let newelem = (lookup vec ( r1 )) + (lookup vec ( r2))
  in updateAt vec ( dest ) (λ x → newelem)

infix 4 _,_—→_
data _,_—→_ : ∀ {n} → Program n → State → State → Set where
  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
        (prf : s .State.pc < n) → 
        ((lookup (p .Program.instructions) (fromℕ< prf)) ≡ NoOp) →
        p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ]
  
  -- step-Add : ∀ {n pc regs} {inst : Vec Instruction n} {dest r1 r2 : Fin 32}
      -- → ((program inst) , ([ pc , regs ]) —→ ([ (suc pc) , addHelper regs dest r1 r2 ]))
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
      (prf : s .State.pc < n ) → 
      ((lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Add dest r1 r2)) →
      p , s —→ [ (suc (s .State.pc)) , addHelper (s .State.registers) dest r1 r2 ]


-- infix  3 _∎
infix 4 _,_—→*_
data _,_—→*_ : ∀ {n} → Program n → State → State → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : State) 
      → p , s —→* s
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State)
      → p , s₁ —→* s₂ 
      → p , s —→ s₁ 
      → p , s —→* s₂


test-prog : Program 4
test-prog = program ( NoOp ∷ NoOp ∷ NoOp ∷ NoOp ∷ [] )

r32 = replicate 32 0
r32-evil = updateAt r32 (# 0) (λ x → 1)

state0 = [ 0 , r32 ]
state1 = [ 1 , r32 ]
state2 = [ 2 , r32 ]
state3 = [ 3 , r32 ]


test-step-noOp : test-prog , state2 —→ state3  
test-step-noOp = step-NoOp test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl
-- test-step = step-NoOp test-prog state2 (s<s (s<s z<s))

test-multi-step : test-prog , state1 —→* state3
test-multi-step = step—→ test-prog state1 state2 state3 2—→*3 1—→2
  where
  1—→2 : test-prog , state1 —→ state2
  1—→2 = step-NoOp test-prog state1 ((s≤s (s≤s z≤n))) refl

  2—→*3 : test-prog , state2 —→* state3
  2—→*3  = step—→ test-prog state2 state3 state3 (done test-prog state3) 2—→3
    where
    2—→3 : test-prog , state2 —→ state3
    2—→3 = step-NoOp test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl


-- 'ADD' test

test-prog-add : Program 1
test-prog-add = program ( Add (# 0) (# 1) (# 2) ∷ [] )

r32-add-start = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-add-end = 5 ∷ 2 ∷ 3 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

statea = [ 0 , r32-add-start ]
stateb = [ 1 , r32-add-end ]


test-step-add : test-prog-add , statea —→ stateb 
test-step-add = step-Add test-prog-add statea (s≤s z≤n) refl
