module agda.proofs.call-untrusted where

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

-- unt-prf : ∀ {n} {p : Program n} {t : Trace} {sₕ sₕ' : Hstate} {sₛ : State}
--     → (sₕ .Hstate.mode ≡ true)
--     → (sₕ .Hstate.pc  ≡ sₛ .State.pc)
--     → (sₕ .Hstate.registers  ≡ sₛ .State.registers)
--     → p , sₕ —→* sₕ' , t
--     → ∃[ sₛ' ] (t , p , sₛ —→ sₛ') × (sₕ' .Hstate.pc  ≡ sₛ' .State.pc) × (sₕ' .Hstate.registers ≡ sₛ' .State.registers)

equiv : Hstate → State → Set
equiv sₕ sₛ = (sₕ .Hstate.pc ≡ sₛ .State.pc) × (sₕ .Hstate.registers ≡ sₛ .State.registers)

-- data equiv (Host Sentry : Set) : Host → Sentry → Set where
--     equiv :  ∀ {pc : ℕ} {reg : Fin 32} →
--            (Host .pc pc .register register) ≡ (StateB .pc pc .register register)
--            → StateEq StateA StateB (StateA pc register) (StateB pc register) 


unt-prf : ∀ {n} {p : Program n} {t : Trace} {sₕ sₕ' : Hstate} {sₛ : State}
    → (sₕ .Hstate.mode ≡ true)
    → (equiv sₕ sₛ)
    → p , sₕ —→* sₕ' , t
    → ∃[ sₛ' ] (t , p , sₛ —→ sₛ') × (equiv sₕ' sₛ')



unt-prf refl (fst , snd) (done _ .([[ _ , _ , true , _ , _ , _ ]])) = {!   !}
unt-prf refl (fst , snd) (step—→ _ .([[ _ , _ , true , _ , _ , _ ]]) s₁ _ t₁ _ c x) = {!   !}


-- unt-prf refl a (done _ ([[ pc , reg , true , _ , _ , _ ]])) = [ pc , reg ] , {!   !} , {!   !}
-- unt-prf refl a (step—→ _ .([[ _ .State.pc , _ .State.registers , true , _ , _ , _ ]]) s₁ _ t₁ _ a x) = {!   !}

-- unt-prf refl refl refl (step-Call-Unt {n} {jmp-pc} p ([[ pc , reg , mode , UR , SR , ret-pc ]]) prf₁ prf2 prf3 cmd-prf) = [ suc (pc) , reg ] , {!   !} , ({!   !} , {!   !})

-- unt-prf refl refl refl _ = {!   !}



-- /////////////////////////////////////

 
  