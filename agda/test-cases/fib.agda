module agda.test-cases.fib where

open import agda.commands
open import agda.host
open import agda.sentry
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Agda.Builtin.List
open import Data.Bool using (Bool; true; false; if_then_else_)



-- a test case for host and sentry being in sentry-testcases

-- fibonacci

p : Program 4
p = program ( Add (# 2) (# 1) (# 0) ∷ Add (# 3) (# 2) (# 1) ∷ Add (# 4) (# 3) (# 2) ∷ Add (# 5) (# 4) (# 3)  ∷  [] )

r32-0 r32-1 r32-2 r32-3 : Vec ℕ 32
r32-0 = 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-1 = 1 ∷ 1 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-2 = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r32-3 = 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

-- state   pc  registers 
state0 = [ 0 , r32-0 ]
state1 = [ 1 , r32-1 ]
state2 = [ 2 , r32-2 ]
state3 = [ 3 , r32-3 ]

state0_ = [[ 0 , r32-0 , true ]]
state1_ = [[ 1 , r32-1 , true ]]
state2_ = [[ 2 , r32-2 , true ]]
state3_ = [[ 3 , r32-3 , true ]]

-- trace   instruction      r1val  r2val  sum
t0 = ⟨ Add (# 2) (# 1) (# 0) , 1 ∷ 1 ∷ 2 ∷ [] ⟩
t1 = ⟨ Add (# 3) (# 2) (# 1) , 2 ∷ 1 ∷ 3 ∷ [] ⟩
t2 = ⟨ Add (# 4) (# 3) (# 2) , 3 ∷ 2 ∷ 5 ∷ [] ⟩
t3 = ⟨ Add (# 5) (# 4) (# 3) , 5 ∷ 3 ∷ 8 ∷ [] ⟩


-- host / sentry steps
H_0→1 : p , state0_ —→ state1_ , t0
H_0→1  = step-Add p state0_(s≤s z≤n) refl

S_0→1 : t0 , p , state0 —→ state1
S_0→1  = step-Add t0 p state0 (s≤s z≤n) refl

H_1→2 : p , state1_ —→ state2_ , t1
H_1→2 = step-Add p state1_ (s≤s (s≤s z≤n)) refl

S_1→2 : t1 , p , state1 —→ state2
S_1→2 = step-Add t1 p state1 (s≤s (s≤s z≤n)) refl

H_2→3 : p , state2_ —→ state3_ , t2
H_2→3 = step-Add p state2_ (s≤s (s≤s (s≤s z≤n))) refl

S_2→3 : t2 , p , state2 —→ state3
S_2→3 = step-Add t2 p state2 (s≤s (s≤s (s≤s z≤n))) refl

H_3→*3 : p , state3_ —→* state3_ , emptyTrace
H_3→*3 = done p state3_

S_3→*3 : emptyTrace , p , state3 —→* state3
S_3→*3 = done emptyTrace p state3



