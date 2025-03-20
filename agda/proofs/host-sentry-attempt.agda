module agda.proofs.host-sentry where

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


-- ask how to write this proof.


prf : ∀ {n} {p : Program n} {t : Trace} {sₕ sₕ' : Hstate} {sₛ : State}
    → (sₕ .Hstate.pc  ≡ sₛ .State.pc)
    → (sₕ .Hstate.registers  ≡ sₛ .State.registers)
    → p , sₕ —→* sₕ' , t
    → ∃[ sₛ' ] (t , p , sₛ —→ sₛ') × (sₕ' .Hstate.pc  ≡ sₛ' .State.pc) × (sₕ' .Hstate.registers  ≡ sₛ' .State.registers)
    
    -- there exists a step such that the host ends up in state where the pc and registers are equivalent

       
prf refl refl (done p [[ pc , registers , mode ]]) = [ pc , registers ] , {!   !} , refl , refl
prf refl refl (step—→ p [[ pc , registers , mode ]] sₕ _ t _ x (step-NoOp .p ([[ .pc , .registers , .mode ]]) prf₁ cmd-prf)) = [ pc , registers ] , step-NoOp _ _ _ prf₁ cmd-prf , {!   !} , {!   !}

prf _ _ _ = {!   !}

-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Add .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Sub .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Addi .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Jump .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Bgtz-l .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 prf3 cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Bgtz-g .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 prf3 cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Enable .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₕ _ t _ x (step-Disable .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !} , {!   !}

-- prf refl refl (step—→ p [[ pc , registers , mode ]] sₛ' _ t _ x (step-NoOp .p ([[ .pc , .registers , .mode ]]) prf₁ cmd-prf)) = [ pc , registers ] , {!   !} , {!   !} , {!   !}


-- prf _ _ _ = {!   !}



-- prf eq1 eq2 (step—→ p [[ pc , registers , mode ]] sₛ' _ t _ x (step-Add .p .([[ pc , registers , mode ]]) prf₁ cmd-prf)) = {!   !} , {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₛ' _ t _ x (step-Sub .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₛ' _ t _ x (step-Addi .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₛ' _ t _ x (step-Jump .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₛ' _ t _ x (step-Bgtz-l .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 prf3 cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₛ' _ t _ x (step-Bgtz-g .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 prf3 cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₛ' _ t _ x (step-Enable .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !}
-- prf refl refl (step—→ p .([[ _ .State.pc , _ .State.registers , _ ]]) sₛ' _ t _ x (step-Disable .p .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf)) = {!   !} , {!   !} , {!   !}







                                                             --      host-state          step        trace             prog      host-state     prf cmd-prf    pc-eqiv      ref-equiv
-- prf refl refl (step-NoOp p [[ pc , registers , mode ]] prf₁ cmd-prf) = [ pc , registers ] , step-NoOp ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ p [ pc , registers ] prf₁ cmd-prf , refl , refl
-- sentry takes no-op step  and ends up in a state where pc and reg are equiv
-- bring in p, sₛ 

-- prf refl refl (step-Add p ([[ pc , registers , mode ]]) prf₁ cmd-prf) = [ pc , registers ] , {!  !} , {!   !} , {!   !}

-- prf refl refl (step-Add p ([[ pc , registers , true ]]) prf₁ cmd-prf) = [ pc , registers ] , {!  !} , {!   !} , {!   !}
-- prf refl refl (step-Add p ([[ pc , registers , false ]]) prf₁ cmd-prf) = [ pc , registers ] , {! !} , {!   !} , {!   !}

-- prf refl refl (step-Add p .([[ _ .State.pc , _ .State.registers , false ]]) prf₁ cmd-prf) = [ .State.pc , .State.registers ] , ?  , {!   !} , {!   !}



-- prf _ _ _ = {!   !}

-- prf refl refl (step-Sub _ .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf) = {!   !}
-- prf refl refl (step-Addi _ .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf) = {!   !}
-- prf refl refl (step-Jump _ .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 cmd-prf) = {!   !}
-- prf refl refl (step-Bgtz-l _ .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf refl refl (step-Bgtz-g _ .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf refl refl (step-Enable _ .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf) = {!   !}
-- prf refl refl (step-Disable _ .([[ _ .State.pc , _ .State.registers , _ ]]) prf₁ cmd-prf) = {!   !}


-- prf refl refl (step-Add t _ _ prf₁ cmd-prf) = {!   !} , {!   !}
-- -- prf refl refl (step-Add t _ _ prf₁ cmd-prf) with step-Add 



-- prf refl refl (step-Sub t _ _ prf₁ cmd-prf) = {!   !}
-- prf refl refl (step-Addi t _ _ prf₁ cmd-prf) = {!   !}
-- prf refl refl (step-Jump _ _ _ prf₁ prf2 cmd-prf) = {!   !}
-- prf refl refl (step-Bgtz-l _ _ _ prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf refl refl (step-Bgtz-g _ _ _ prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf refl refl (step-Enable _ _ _ prf₁ cmd-prf) = {!   !}
-- prf refl refl (step-Disable _ _ _ prf₁ cmd-prf) = {!   !}
-- prf refl refl (step-NoOp _ _ _ prf₁ cmd-prf) = {!   !} , {!   !} 
    