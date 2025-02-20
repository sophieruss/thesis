module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
-- proofs for constructors, inductive
import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Data.List using (List; _∷_; _++_; length)

data Instruction : Set where
  NoOp  : Instruction
  Add   : ℕ → ℕ → Instruction

record Program : Set where
  constructor program
  field 
    instructions : List Instruction

record State : Set where
  constructor [_]
  field
    pc : ℕ
    -- instruction pointer (now), register vector 32, noop regs shuold be same
    -- step relation for add - all other regs are unchanged except destinati0on

infix 4 _,_—→_
data _,_—→_ : Program → State → State → Set where
  step-pc : (p : Program) → (s : State) → 
         (s .State.pc < (length (Program.instructions p)) ∸ 1 ) → 
         p , s —→ [ suc (s .State.pc) ]
        --  no op and add


-- infix  3 _∎
infix 4 _,_—→*_
data _,_—→*_ : Program → State → State → Set where
    _∎ : ∀ (p : Program) → (s : State) 
      → p , s —→* s
    step—→ : ∀ (p : Program) (s s₁ s₂ : State)
      → p , s₁ —→* s₂ 
      → p , s —→ s₁ 
      → p , s —→* s₂

-- TODO: how to make this pattern 
pattern _,_—→⟨_⟩_ p s s₁ p,s—→s₁ p,s₁—→*s₂ = step—→ p s s₁ p,s₁—→*s₂ p,s—→s₁
-- pattern _—→⟨_⟩_ t t—→t₁ t₁—→*t₂ = step—→ t t₁—→*t₂ t—→t₁


exampleProgram : Program
exampleProgram = program  ( Add 4 3 ∷ NoOp ∷ NoOp ∷ NoOp ∷ [])

_ : ( exampleProgram , [ 2 ] —→ [ 3 ] ) 
_ = step-pc exampleProgram [ 2 ] ((s≤s (s≤s (s≤s z≤n))))
-- _ = step-pc [ 5 ] [ 2 ] (s<s (s<s z<s))
