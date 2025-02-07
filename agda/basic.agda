module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; zero; suc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record Program : Set where
  constructor  [_]
  field 
    size : ℕ

record State : Set where
  constructor [_]
  field
    pc : ℕ

infix 4 _,_—→_
data _,_—→_ : Program → State → State → Set where
  step_pc : (p : Program) → (s : State) → 
         (s .State.pc < p .Program.size) →
         (s' : State) → (s' .State.pc ≡ s .State.pc + 1) → 
         p , s —→ s'


prog : Program
prog = [ 5 ]

st : State
-- st = [ 0 ]
st = [ 10 ]

st' : State
st' = [ 1 ]

-- _ : ( prog , st —→ st' ) ≡ ([ 5 ] , [ 0 ] —→ [ 1 ] )
_ : ( prog , st —→ st' ) ≡ ([ 5 ] , [ 10 ] —→ [ 1 ] )
_ = refl

 