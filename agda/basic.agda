module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
-- proofs for constructors, inductive
import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
-- open import Agda.Builtin.List
-- open import Data.List using (List; _∷_; _++_; length)
open import Data.Vec using (Vec; _∷_; [])
open import Agda.Primitive


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
         p , s —→ 
         [ suc (s .State.pc) ]
        --  no op and add


-- infix  3 _∎
infix 4 _,_—→*_
data _,_—→*_ : ∀ {n} → Program n → State → State → Set where
    _∎ : ∀ {n} → ∀ (p : Program n) → (s : State) 
      → p , s —→* s
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State)
      → p , s₁ —→* s₂ 
      → p , s —→ s₁ 
      → p , s —→* s₂

-- TODO: how to make this pattern 
pattern _,_—→⟨_⟩_ p s s₁ p,s—→s₁ p,s₁—→*s₂ = step—→ p s s₁ p,s₁—→*s₂ p,s—→s₁
-- pattern _—→⟨_⟩_ t t—→t₁ t₁—→*t₂ = step—→ t t₁—→*t₂ t—→t₁


exampleProgram : Program 4
exampleProgram = program ( Add 4 3 ∷ NoOp ∷ NoOp ∷ NoOp ∷ [] )

_ : ( exampleProgram , [ 2 ] —→ [ 3 ] ) 
_ = step-pc exampleProgram [ 2 ] ((s≤s (s≤s (s≤s z≤n))))
-- _ = step-pc [ 5 ] [ 2 ] (s<s (s<s z<s))
