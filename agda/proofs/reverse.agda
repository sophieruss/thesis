module agda.proofs.reverse where

-- try reversing host and sentry 

open import agda.commands
open import agda.host renaming (State to Hstate)
open import agda.sentry
open import Data.Nat using (ℕ; compare; _≤_; _≥_;  _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; _≥?_)
open import Function.Base using (flip)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ)
open import Data.Bool using (Bool; true; false; if_then_else_)

z = ℕ.zero
zz = replicate 32 0

equiv : Hstate → State → Set
equiv sₕ sₛ = (sₕ .Hstate.pc ≡ sₛ .State.pc) × (sₕ .Hstate.registers ≡ sₛ .State.registers)

prf : ∀ {n} {p : Program n} {t : Trace} {sₕ : Hstate} {sₛ sₛ' : State}
    → (sₕ .Hstate.mode ≡ true)
    → (equiv sₕ sₛ)
    → t , p , sₛ —→ sₛ'
    → ∃[ sₕ' ] (p , sₕ —→ sₕ' , t) × (equiv sₕ' sₛ')

-- How to determine UR, ST, ret-pc? 
-- how to fill in proof
prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-NoOp _ p [ pc , reg ] prf₁ cmd-prf) = [[ pc , reg , true ,   Hstate.UR h    , Hstate.SR h , Hstate.ret-pc h  ]] , (step-NoOp {!   !} {!   !} {!   !} {!   !} , refl , refl)
prf refl (refl , refl) _ = {!   !}


-- prf refl (refl , refl) (step-Add t _ _ prf₁ cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Sub t _ _ prf₁ cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Addi t _ _ prf₁ cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Jump _ _ _ prf₁ prf2 cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Bgtz-l _ _ _ prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Bgtz-g _ _ _ prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Call-Unt-Sentry _ _ _ prf₁ cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Return _ _ _ prf₁ cmd-prf) = {!   !}
-- prf refl (refl , refl) (step-Alert _ _ _ prf₁ cmd-prf) = {!   !} 