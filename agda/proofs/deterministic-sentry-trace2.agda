module agda.proofs.deterministic-sentry-trace2 where

open import agda.commands
open import agda.sentry-new
open import Data.Nat using (ℕ; compare; _≤_; _≥_;  _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ; proj₁; proj₂)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; _≥?_)
open import Function.Base using (flip)

≤-≡-trans : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤-≡-trans x refl = x

-- Can I maybe prove traces must be the same, everthing else is; 
det-trace : ∀ {n} {p : Program n} {s s₁ s₂ : State} {t₁ t₂ : Trace}
    → t₁ , p , s —→ s₁
    → t₂ , p , s —→ s₁
    → (t₁ ≡ t₂)

det-trace (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with trans prf-trace (sym prf-trace₁)
... | refl = refl
det-trace (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Jump _ _ [ pc , registers ] prf-cur₁ prf-canStep prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-g _ _ [ pc , registers ] prf-cur₁ prf-canStep prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁

det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ NoOp , args ⟩} (step-Add ⟨ Add x x₁ x₂ , args₁ ⟩ _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {! t₁ !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Add x x₁ x₂ , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Sub x x₁ x₂ , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Addi x x₁ x₂ , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Jump x , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Bgtz x x₁ , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Enable , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Disable , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Call-Unt x , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Call-Unt-Sentry , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Return-Unt , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Return , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Alert , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Load-UR x , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Load-UR-Sentry x x₁ , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}
det-trace {n} {p} {s₁} {s} {s₂} {t₁} {⟨ Empty , args ⟩} (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!   !}




det-trace (step-Sub t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!  !}
det-trace (step-Addi t _ _ prf-cur prf-cmd prf-trace prf-canStep) _ = {!  !}
det-trace (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) _ = {!  !}
det-trace (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) _ = {!  !}
det-trace (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) _ = {!  !}
det-trace (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) _ = {!  !}
det-trace (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) _ = {!  !}

 
det-trace (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Jump _ _ [ pc , registers ] prf-cur₁ prf-canStep prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-g _ _ [ pc , registers ] prf-cur₁ prf-canStep prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with trans prf-trace (sym prf-trace₁)
... | refl = refl
det-trace (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁



det-trace (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Jump _ _ [ pc , registers ] prf-cur₁ prf-canStep prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-g _ _ [ pc , registers ] prf-cur₁ prf-canStep prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det-trace (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with trans prf-trace (sym prf-trace₁)
... | refl = refl 