module Agda.programs.outputs.simulator-Sentry where
open import agda.sentry
open import agda.commands
open import agda.host
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Agda.Builtin.List
prog : Program 16
prog = program (NoOp ∷ Addi (# 1) (# 0) 1 ∷ Addi (# 2) (# 1) 0 ∷ Add (# 3) (# 1) (# 2) ∷ Add (# 4) (# 2) (# 3) ∷ Add (# 5) (# 3) (# 4) ∷ Add (# 6) (# 4) (# 5) ∷ Add (# 7) (# 5) (# 6) ∷ Add (# 8) (# 6) (# 7) ∷ Add (# 9) (# 7) (# 8) ∷ Add (# 10) (# 8) (# 9) ∷ Add (# 11) (# 9) (# 10) ∷ Add (# 12) (# 10) (# 11) ∷ Add (# 13) (# 11) (# 12) ∷ Add (# 14) (# 12) (# 13) ∷ NoOp ∷ [])
r-0 r-1 r-2 r-3 r-4 r-5 r-6 r-7 r-8 r-9 r-10 r-11 r-12 r-13 r-14 r-15  : Vec ℕ 32
r-0 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-1 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-2 = 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-3 = 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-4 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-5 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-6 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-7 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-8 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-9 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-10 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-11 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-12 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ 89 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-13 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ 89 ∷ 144 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-14 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ 89 ∷ 144 ∷ 233 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-15 = 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ 89 ∷ 144 ∷ 233 ∷ 377 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
state-0 = [ 0 , r-0 ]
state-1 = [ 1 , r-1 ]
state-2 = [ 2 , r-2 ]
state-3 = [ 3 , r-3 ]
state-4 = [ 4 , r-4 ]
state-5 = [ 5 , r-5 ]
state-6 = [ 6 , r-6 ]
state-7 = [ 7 , r-7 ]
state-8 = [ 8 , r-8 ]
state-9 = [ 9 , r-9 ]
state-10 = [ 10 , r-10 ]
state-11 = [ 11 , r-11 ]
state-12 = [ 12 , r-12 ]
state-13 = [ 13 , r-13 ]
state-14 = [ 14 , r-14 ]
state-15 = [ 15 , r-15 ]
τ-0 τ-1 τ-2 τ-3 τ-4 τ-5 τ-6 τ-7 τ-8 τ-9 τ-10 τ-11 τ-12 τ-13 τ-14 τ-15  : Trace
τ-0 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
τ-1 = ⟨ Addi (# 1) (# 0) 1 , 0 ∷ 1 ∷ 0 ∷ [] ⟩
τ-2 = ⟨ Addi (# 2) (# 1) 0 , 1 ∷ 1 ∷ 0 ∷ [] ⟩
τ-3 = ⟨ Add (# 3) (# 1) (# 2) , 1 ∷ 1 ∷ 2 ∷ [] ⟩
τ-4 = ⟨ Add (# 4) (# 2) (# 3) , 1 ∷ 2 ∷ 3 ∷ [] ⟩
τ-5 = ⟨ Add (# 5) (# 3) (# 4) , 2 ∷ 3 ∷ 5 ∷ [] ⟩
τ-6 = ⟨ Add (# 6) (# 4) (# 5) , 3 ∷ 5 ∷ 8 ∷ [] ⟩
τ-7 = ⟨ Add (# 7) (# 5) (# 6) , 5 ∷ 8 ∷ 13 ∷ [] ⟩
τ-8 = ⟨ Add (# 8) (# 6) (# 7) , 8 ∷ 13 ∷ 21 ∷ [] ⟩
τ-9 = ⟨ Add (# 9) (# 7) (# 8) , 13 ∷ 21 ∷ 34 ∷ [] ⟩
τ-10 = ⟨ Add (# 10) (# 8) (# 9) , 21 ∷ 34 ∷ 55 ∷ [] ⟩
τ-11 = ⟨ Add (# 11) (# 9) (# 10) , 34 ∷ 55 ∷ 89 ∷ [] ⟩
τ-12 = ⟨ Add (# 12) (# 10) (# 11) , 55 ∷ 89 ∷ 144 ∷ [] ⟩
τ-13 = ⟨ Add (# 13) (# 11) (# 12) , 89 ∷ 144 ∷ 233 ∷ [] ⟩
τ-14 = ⟨ Add (# 14) (# 12) (# 13) , 144 ∷ 233 ∷ 377 ∷ [] ⟩
τ-15 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
sentry_0→1 : τ-0 , prog , state-0 —→ state-1
sentry_0→1 = step-NoOp τ-0 prog state-0 (s≤s z≤n) refl

sentry_1→2 : τ-1 , prog , state-1 —→ state-2
sentry_1→2 = step-Addi τ-1 prog state-1 (s≤s (s≤s z≤n)) refl

sentry_2→3 : τ-2 , prog , state-2 —→ state-3
sentry_2→3 = step-Addi τ-2 prog state-2 (s≤s (s≤s (s≤s z≤n))) refl

sentry_3→4 : τ-3 , prog , state-3 —→ state-4
sentry_3→4 = step-Add τ-3 prog state-3 (s≤s (s≤s (s≤s (s≤s z≤n)))) refl

sentry_4→5 : τ-4 , prog , state-4 —→ state-5
sentry_4→5 = step-Add τ-4 prog state-4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) refl

sentry_5→6 : τ-5 , prog , state-5 —→ state-6
sentry_5→6 = step-Add τ-5 prog state-5 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) refl

sentry_6→7 : τ-6 , prog , state-6 —→ state-7
sentry_6→7 = step-Add τ-6 prog state-6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) refl

sentry_7→8 : τ-7 , prog , state-7 —→ state-8
sentry_7→8 = step-Add τ-7 prog state-7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) refl

sentry_8→9 : τ-8 , prog , state-8 —→ state-9
sentry_8→9 = step-Add τ-8 prog state-8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) refl

sentry_9→10 : τ-9 , prog , state-9 —→ state-10
sentry_9→10 = step-Add τ-9 prog state-9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))) refl

sentry_10→11 : τ-10 , prog , state-10 —→ state-11
sentry_10→11 = step-Add τ-10 prog state-10 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))) refl

sentry_11→12 : τ-11 , prog , state-11 —→ state-12
sentry_11→12 = step-Add τ-11 prog state-11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))) refl

sentry_12→13 : τ-12 , prog , state-12 —→ state-13
sentry_12→13 = step-Add τ-12 prog state-12 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))) refl

sentry_13→14 : τ-13 , prog , state-13 —→ state-14
sentry_13→14 = step-Add τ-13 prog state-13 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))) refl

sentry_14→15 : τ-14 , prog , state-14 —→ state-15
sentry_14→15 = step-Add τ-14 prog state-14 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))) refl

