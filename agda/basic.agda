module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; zero; suc; s<s; z<s; z≤n; s≤s )
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
    -- make this into vector of instructions


exampleProgram : Program
-- exampleProgram = _ { instructions = [ ] }
exampleProgram = program  (NoOp ∷ NoOp ∷ NoOp ∷ NoOp ∷ NoOp ∷ [])

record State : Set where
  constructor [_]
  field
    pc : ℕ

infix 4 _,_—→_
data _,_—→_ : Program → State → State → Set where
  step-pc : (p : Program) → (s : State) → 
         (s .State.pc < (length (Program.instructions p)) ) → 
         p , s —→ [ suc (s .State.pc) ]




_ : ( exampleProgram , [ 2 ] —→ [ 3 ] ) 
_ = step-pc exampleProgram [ 2 ] ((s≤s (s≤s (s≤s z≤n))))
-- _ = step-pc [ 5 ] [ 2 ] (s≤s (s≤s (s≤s z≤n)))
-- _ = step-pc [ 5 ] [ 2 ] (s<s (s<s z<s))



  -- ^^y or c ^^.
  -- transitive closure - copy and paste step relation, give name take multi steps to here
  -- goes from 0 to 3, takes lots of steps, 0 to 1, 1 to 2 ...

  -- only takes step if < |prog| < 2, so doesnt step off end

  -- vector of instructions

  -- instructions bessides no-op




-- data _—→*_ : Term → Term → Set where
--     _∎ : ∀ (t : Term) → t —→* t
--     step—→ : ∀ (t : Term) {t₁ t₂ : Term}
--         → t₁ —→* t₂
--         → t  —→  t₁
--         → t  —→* t₂

-- pattern _—→⟨_⟩_ t t—→t₁ t₁—→*t₂ = step—→ t t₁—→*t₂ t—→t₁
