module deterministic where

open import steps
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)



det : ∀ {n} {p : Program n} {s s₁ s₂ : State}
    → p , s —→ s₁
    → p , s —→ s₂
    → s₁ ≡ s₂


det (step-NoOp _ _ prf cmd-prf) (step-NoOp _ _ prf₁ cmd-prf₁) = refl
det (step-NoOp _ _ prf cmd-prf) (step-Add _ _ prf₁ cmd-prf₁) with () ← trans (sym cmd-prf) cmd-prf₁

det (step-NoOp _ _ prf cmd-prf) (step-Sub _ _ prf₁ cmd-prf₁) = {!   !}
det (step-NoOp _ _ prf cmd-prf) (step-Addi _ _ prf₁ cmd-prf₁) = {!   !}
det (step-NoOp _ _ prf cmd-prf) (step-Jump _ _ prf₁ prf2 cmd-prf₁) = {!   !}
det (step-NoOp _ _ prf cmd-prf) (step-Bgtz-l _ _ prf₁ prf2 prf3 cmd-prf₁) = refl
det (step-NoOp _ _ prf cmd-prf) (step-Bgtz-g _ _ prf₁ prf2 prf3 cmd-prf₁) = {!   !}


det (step-Add _ _ prf cmd-prf ) (step-Add _ _ prf₁ cmd-prf₁) with trans (sym cmd-prf) cmd-prf₁
... | refl = refl
det (step-Add _ _ prf cmd-prf ) s—→s₂ = {!   !}

det (step-Sub _ _ prf cmd-prf ) (step-Sub _ _ prf₁ cmd-prf₁) = {!   !}
det (step-Sub _ _ prf cmd-prf ) s—→s₂ = {!   !}

det (step-Addi _ _ prf cmd-prf ) (step-Addi _ _ prf₁ cmd-prf₁) = {!   !}
det (step-Addi _ _ prf cmd-prf ) s—→s₂ = {!   !}

det (step-Jump _ _ prf prf2 cmd-prf ) (step-Jump _ _ prf₁ prf3 cmd-prf₁) = {!   !}
det (step-Jump _ _ prf prf2 cmd-prf ) s—→s₂ = {!   !}

det (step-Bgtz-l _ _ prf prf2 prf3 cmd-prf ) (step-Bgtz-l _ _ prf₁ prf4 prf5 cmd-prf₁) = refl
det (step-Bgtz-l _ _ prf prf2 prf3 cmd-prf ) s—→s₂ = {!   !}

det (step-Bgtz-g _ _ prf prf2 prf3 cmd-prf ) (step-Bgtz-g _ _ prf₁ prf4 prf5 cmd-prf₁) = {!   !}
det (step-Bgtz-g _ _ prf prf2 prf3 cmd-prf ) s—→s₂ = {!   !}

-- det s—→s₁ s—→s₂ = {!   !}


-- issues
-- how to eliminate the rest of the step-options. given p , s ≡ p , the step must be the same because cmd-prf ≡ cmd-prf₁ 
-- how to prove that helper functions are deterministic
-- det (step-NoOp _ _ prf cmd-prf) (step-Add _ _ prf₁ cmd-prf₁) = ⊥-elim (contradiction step-NoOp λ cmd-prf₂ → [ {!   !} ])


-- not . I think clements was incorrect.
-- det : ∀ {n} {p : Program n} {s s₁ s₂ : State}
--     → p , s₁ —→ s
--     → p , s₂ —→ s
--     → s₁ ≡ s₂