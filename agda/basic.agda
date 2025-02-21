module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
-- proofs for constructors, inductive
import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Vec using (Vec; _∷_; [])
open import Agda.Primitive
open import Data.Sum



data Instruction : Set where
  NoOp  : Instruction
  Add   : ℕ → ℕ → Instruction

record Program (n : ℕ) : Set where
  constructor program
  field 
    instructions : Vec Instruction n

record State : Set where
  constructor [_]
  field
    pc : ℕ
    -- instruction pointer (now), register vector 32, noop regs shuold be same
    -- step relation for add - all other regs are unchanged except destinati0on

infix 4 _,_—→_
data _,_—→_ : ∀ {n} → Program n → State → State → Set where
  step-pc : ∀ {n} → (p : Program n) → (s : State) → 
         (s .State.pc < n ) → 
         p , s —→ [ suc (s .State.pc) ]
        --  no op and add


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

test-step : test-prog , [ 2 ] —→ [ 3 ] 
test-step = step-pc test-prog [ 2 ] ((s≤s (s≤s (s≤s z≤n))))
-- test-step = step-pc [ 5 ] [ 2 ] (s<s (s<s z<s))


test-multi-step : test-prog , [ 1 ] —→* [ 3 ]
test-multi-step = step—→ test-prog [ 1 ] [ 2 ] [ 3 ] 2—→*3 1—→2
  where
  1—→2 : test-prog , [ 1 ] —→ [ 2 ] 
  1—→2 = step-pc test-prog [ 1 ] ((s≤s (s≤s z≤n)))

  2—→*3 : test-prog , [ 2 ] —→* [ 3 ]
  2—→*3  = step—→ test-prog [ 2 ] [ 3 ] [ 3 ] (done test-prog [ 3 ]) 2—→3
    where
    2—→3 : test-prog , [ 2 ] —→ [ 3 ] 
    2—→3 = step-pc test-prog [ 2 ] ((s≤s (s≤s (s≤s z≤n)))) 


