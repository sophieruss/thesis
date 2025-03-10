module agda.sim-out-sentry where
open import agda.sentry
open import agda.commands
open import agda.host
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Agda.Builtin.List
prog : Program 4
prog = program (Add (# 2) (# 1) (# 0) ∷ Add (# 3) (# 2) (# 1) ∷ Add (# 4) (# 3) (# 2) ∷ Add (# 5) (# 4) (# 3) ∷ [])
r-0 r-1 r-2 r-3  : Vec ℕ 32
r-0 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-1 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-2 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-3 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
state-0 = [ 0 , r-0 ]
state-1 = [ 1 , r-1 ]
state-2 = [ 2 , r-2 ]
state-3 = [ 3 , r-3 ]
τ-0 τ-1 τ-2 τ-3  : Trace
τ-0 = ⟨ Add (# 2) (# 1) (# 0) , 0 ∷ 0 ∷ 0 ∷ [] ⟩
τ-1 = ⟨ Add (# 3) (# 2) (# 1) , 0 ∷ 0 ∷ 0 ∷ [] ⟩
τ-2 = ⟨ Add (# 4) (# 3) (# 2) , 0 ∷ 0 ∷ 0 ∷ [] ⟩
τ-3 = ⟨ Add (# 5) (# 4) (# 3) , 0 ∷ 0 ∷ 0 ∷ [] ⟩
0→1 : prog , state-0 —→ state-1 , τ-0
0→1 = step-Add prog state-0 (s≤s z≤n) refl
sentry_0→1 : τ-0 , prog , state-0 —→ state-1
sentry_0→1 = step-Add τ-0 prog state-0 (s≤s z≤n) refl

1→2 : prog , state-1 —→ state-2 , τ-1
1→2 = step-Add prog state-1 (s≤s (s≤s z≤n)) refl
sentry_1→2 : τ-1 , prog , state-1 —→ state-2
sentry_1→2 = step-Add τ-1 prog state-1 (s≤s (s≤s z≤n)) refl

2→3 : prog , state-2 —→ state-3 , τ-2
2→3 = step-Add prog state-2 (s≤s (s≤s (s≤s z≤n))) refl
sentry_2→3 : τ-2 , prog , state-2 —→ state-3
sentry_2→3 = step-Add τ-2 prog state-2 (s≤s (s≤s (s≤s z≤n))) refl

