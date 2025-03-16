module agda.host-sentry where

open import agda.commands
open import agda.steps
open import Data.Nat using (ℕ; compare; _≤_; _≥_;  _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Vec using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no; does; Dec)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Product using (∃-syntax; _×_)


open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; _≥?_)
open import Function.Base using (flip)

-- vecEq : ∀ {A : Set} {n : ℕ} → Vec A n → Vec A n → Bool
-- vecEq [] [] = true
-- vecEq (x ∷ xs) (y ∷ ys) with x ≡ y
-- ... | zz = vecEq xs ys



det : ∀ {n} {p : Program n} {sₕ sₕ' : HostState} {sₛ s­ₛ' : SentryState}
    → p , s —→ s₁
    → p , s —→ s₂
    → s₁ ≡ s₂



reg = 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

-- Example State 1
s₁ : HostState
s₁ = ⟨ [ 5 , reg ] , true ⟩

-- Example State 2 (Same as s₁)
s₂ : SentryState
s₂ = ⟨ [ 5 , reg ] ⟩

-- Example State 3 (Different pc)
s₃ : HostState
s₃ = ⟨ [ 6 , reg ] , true ⟩

-- Testing the states
test1 : (s₁ .HostState.state) ≡ (s₂ .SentryState.state)
test1 = refl

t2 : (s₁ .HostState.state) ≡ (s₃ .HostState.state)
t2 = refl
-- test2 : statesEq s₁ s₃ ≡ false
-- test2 = ?







-- det : ∀ {n} {p : Program n} {host host' sentry sentry' : State}
--     → p , s —→ s₁
--     → p , s —→ s₂
    
--     → s₁ ≡ s₂  

