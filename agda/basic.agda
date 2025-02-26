module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Agda.Primitive
open import Data.Fin using (Fin; zero; suc; #_)



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
    -- instruction pointer (now), register vector 32, noop regs shuold be same
    -- step relation for add - all other regs are unchanged except destinati0on


addHelper : Vec ℕ 32 →  Fin 32 → Fin 32 → Fin 32 → Vec ℕ 32
addHelper vec dest r1 r2 = 
  let newelem = (lookup vec ( r1 )) + (lookup vec ( r2))
  in updateAt vec ( dest ) (λ x → newelem)

infix 4 _,_—→_
data _,_—→_ : ∀ {n} → Program n → State → State → Set where
  -- ensure instruction is NoOp, increment pc
  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
        (s .State.pc < n ) → 
        ((lookup (p .Program.instructions) (# (s .State.pc))) ≡ NoOp) →
        p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ]
  
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
        (s .State.pc < n ) → 
        ((lookup (p .Program.instructions) (# (s .State.pc))) ≡ (Add dest r1 r2)) →
        p , s —→ [ (suc (s .State.pc)) , addHelper (s .State.registers) (dest) (r1) (r2) ]

        
        


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
r32-evil = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

state0 = [ 0 , r32 ]
state1 = [ 1 , r32 ]
state2 = [ 2 , r32 ]
state3 = [ 3 , r32 ]

test-step : test-prog , state2 —→ state3  
test-step = step-NoOp test-prog state2 ((s≤s (s≤s (s≤s z≤n)))) refl
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




