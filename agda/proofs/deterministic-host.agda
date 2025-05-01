module agda.proofs.deterministic-host where

open import agda.commands renaming (State to command-state)
open import agda.host
open import Data.Nat using (ℕ; compare; _≤_; _≥_;  _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ; proj₁; proj₂)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; _≥?_)
open import Function.Base using (flip)


det : ∀ {n} {p : Program n} {s s₁ s₂ : State} {t₁ t₂ : Trace}
    → p , s —→ s₁ , t₁
    → p , s —→ s₂ , t₂
    → (s₁ ≡ s₂) × (t₁ ≡ t₂)


≤-≡-trans : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤-≡-trans x refl = x

det {n} {p} {s} {s₁} {s₂} {t₁} {t₂} (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace₁) with trans (sym prf-cmd) prf-cmd₁
... | refl with trans prf-trace (sym prf-trace₁)
... | refl = refl , refl
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Jump _ _ prf-cur₁ prf-canStep prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Ret-Unt _ _ prf-cur₁ prf-canStep prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-NoOp _ _ prf-cur prf-cmd prf-trace) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det {n} {p} {s} {s₁} {s₂} {t₁} {t₂} (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Add _ _ prf-cur prf-cmd prf-canStep)(step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁)with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Sub _ _ prf-cur prf-cmd prf-canStep) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Addi _ _ prf-cur prf-cmd prf-canStep) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Jump _ _ prf-cur prf-canStep prf-cmd) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero₁ prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl with () ←  ≤-≡-trans prf-gzero prf-zero 
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl with () ←  ≤-≡-trans prf-gzero prf-zero 
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero₁ prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc₁ prf-mode₁ prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode₁ prf-cmd₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Ret-Unt _ _ prf-cur prf-canStep prf-mode prf-cmd) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Return _ _ prf-cur prf-cmd) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Jump _ _ prf-cur₁ prf-canStep prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Ret-Unt _ _ prf-cur₁ prf-canStep prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Return _ _ prf-cur₁ prf-cmd₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Return _ _ prf-cur prf-cmd) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Return _ _ prf-cur prf-cmd) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Alert _ _ prf-cur prf-cmd) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Jump _ _ prf-cur₁ prf-canStep prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Ret-Unt _ _ prf-cur₁ prf-canStep prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Alert _ _ prf-cur₁ prf-cmd₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Alert _ _ prf-cur prf-cmd) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Alert _ _ prf-cur prf-cmd) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl
det (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁


det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-NoOp _ _ prf-cur₁ prf-cmd₁ prf-trace) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Add _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Sub _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Addi _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Jump _ _ prf-cur₁ prf-canStep₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Bgtz-l _ _ prf-cur₁ prf-zero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Bgtz-g _ _ prf-cur₁ prf-gzero prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Call-Unt _ _ prf-cur₁ prf-jmp-pc prf-mode₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ prf-mode₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Return _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Alert _ _ prf-cur₁ prf-cmd₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Load-UR _ _ prf-cur₁ prf-cmd₁ prf-canStep₁) with () ← trans (sym prf-cmd) prf-cmd₁
det (step-Put-UR _ _ prf-cur prf-cmd prf-mode prf-canStep) (step-Put-UR _ _ prf-cur₁ prf-cmd₁ prf-mode₁ prf-canStep₁) with trans (sym prf-cmd) prf-cmd₁
... | refl = refl , refl