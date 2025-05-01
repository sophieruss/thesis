module agda.proofs.deterministic-sentry where

open import agda.commands
open import agda.sentry
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

det : ∀ {n} {p : Program n} {s s₁ s₂ : State} {t : Trace}
    → t , p , s —→ s₁
    → t , p , s —→ s₂
    → (s₁ ≡ s₂) 

det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) = refl
det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Jump _ _ _ prf-cur₁ prf-canStep prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero prf-cmd₁ prf-trace₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep prf-cmd₁ prf-canReturn prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Load-UR _ _ _ prf-cur₁ prf-cmd₁ prf-canStep prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ _ prf-cur prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) (step-Add t₁ _ _ prf-cur₁ prf-cmd₁ prf-trace₁ prf-canStep₁) = refl
det (step-Sub t _ _ prf-cur prf-cmd prf-trace prf-canStep) (step-Sub t₁ _ _ prf-cur₁ prf-cmd₁ prf-trace₁ prf-canStep₁) = refl
det (step-Addi t _ _ prf-cur prf-cmd prf-trace prf-canStep) (step-Addi t₁ _ _ prf-cur₁ prf-cmd₁ prf-trace₁ prf-canStep₁) = refl

det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-Jump _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl
det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero prf-cmd₁ prf-trace₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep₁ prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-canReturn prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-Load-UR _ _ _ prf-cur₁ prf-cmd₁ prf-canStep₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ _ prf-cur prf-canStep prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-Jump _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero₁ prf-cmd₁ prf-trace₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl
det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep₁ prf-gzero prf-cmd₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl with () ←  ≤-≡-trans prf-gzero prf-zero 
det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-canReturn prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-Load-UR _ _ _ prf-cur₁ prf-cmd₁ prf-canStep₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ _ prf-cur prf-zero prf-cmd prf-trace prf-canStep) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-Jump _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero prf-cmd₁ prf-trace₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl with () ←  ≤-≡-trans prf-gzero prf-zero 
det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep₁ prf-gzero₁ prf-cmd₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl
det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-canReturn prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-Load-UR _ _ _ prf-cur₁ prf-cmd₁ prf-canStep₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ _ prf-cur prf-canStep prf-gzero prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-Jump _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero prf-cmd₁ prf-trace₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep₁ prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-canReturn₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl
det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-Load-UR _ _ _ prf-cur₁ prf-cmd₁ prf-canStep₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt-Sentry _ _ _ prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-Jump _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero prf-cmd₁ prf-trace₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep₁ prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep₁ prf-cmd₁ prf-canReturn prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR {n} {temp} t _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-Load-UR {n} {temp1} t _ _ prf-cur₁ prf-cmd₁ prf-canStep₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl with trans (sym prf-trace) prf-trace₁
... | refl = refl

det (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Jump _ _ _ prf-cur₁ prf-canStep prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero prf-cmd₁ prf-trace₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep prf-cmd₁ prf-canReturn prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Load-UR _ _ _ prf-cur₁ prf-cmd₁ prf-canStep prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl
det (step-Return _ _ _ prf-cur prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-NoOp _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Jump _ _ _ prf-cur₁ prf-canStep prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-l _ _ _ prf-cur₁ prf-zero prf-cmd₁ prf-trace₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-g _ _ _ prf-cur₁ prf-canStep prf-gzero prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Call-Unt-Sentry _ _ _ prf-cur₁ prf-canStep prf-cmd₁ prf-canReturn prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Load-UR _ _ _ prf-cur₁ prf-cmd₁ prf-canStep prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Return _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ _ prf-cur prf-cmd prf-trace) (step-Alert _ _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl