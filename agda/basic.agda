module basic where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; zero; suc; s<s; z<s; z≤n; s≤s )
-- proofs for constructors, inducdive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

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
  step-pc : (p : Program) → (s : State) → 
         (s .State.pc < p .Program.size) → 
         p , s —→ [ suc (s .State.pc) ]


prog : Program
prog = [ 5 ]

st : State
st = [ 0 ]
-- st = [ 10 ]

st' : State
st' = [ 1 ]


_ : ( prog , st —→ st' ) 
-- ≡ ([ 5 ] , [ 0 ] —→ [ 1 ] )
-- _ = step [ 5 ] pc [ 0 ] (_≤_.s≤s _≤_.z≤n)
_ = step-pc prog st z<s -- (s≤s z≤n)

_ : ( [ 5 ] , [ 2 ] —→ [ 3 ] ) 
_ = step-pc [ 5 ] [ 2 ] (s≤s (s≤s (s≤s z≤n)))
-- _ = step-pc [ 5 ] [ 2 ] (s<s (s<s z<s))



-- ^^y or c ^^.
    -- transitive closure - copy and paste step relation, give name take multi steps to here
    -- goes from 0 to 3, takes lots of steps, o to 1, 1 to 2 ...

    -- only takes step if < |prog| < 2, so doesnt step off end

    -- vector of instructions

    -- instructions bessides no-op