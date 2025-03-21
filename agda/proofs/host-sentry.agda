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

z = ℕ.zero
y =  (# 0)

prf : ∀ {n} {p : Program n} {t : Trace} {sₕ sₕ' : Hstate} {sₛ : State}
    → (sₕ .Hstate.mode ≡ true)
    → (sₕ .Hstate.pc  ≡ sₛ .State.pc)
    → (sₕ .Hstate.registers  ≡ sₛ .State.registers)
    → p , sₕ —→ sₕ' , t
    → ∃[ sₛ' ] (t , p , sₛ —→ sₛ') × (sₕ' .Hstate.pc  ≡ sₛ' .State.pc) × (sₕ' .Hstate.registers  ≡ sₛ' .State.registers)
    
    -- there exists a step such that the host ends up in state where the pc and registers are equivalent


-- (mode)(pc) (reg)        (p , sₕ —→ sₕ' , t )                               (sₛ')        
prf refl refl refl (step-NoOp p [[ pc , registers , _ ]] prf₁ cmd-prf) = [ pc , registers ] , (step-NoOp ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ p [ pc , registers ] prf₁ cmd-prf) , (refl , refl)
prf refl refl refl (step-Add {n} {dest} {r1} {r2} p [[ pc , registers , _ ]] prf₁ cmd-prf ) = [ suc (pc) , _ ] , step-Add ⟨ (Add dest r1 r2 ) , z ∷ ( z ∷ ( z ∷ [])) ⟩ p [ pc , registers ] prf₁ cmd-prf , (refl , refl)
prf refl refl refl (step-Sub {n} {dest} {r1} {r2} p [[ pc , registers , _ ]] prf₁ cmd-prf ) = [ suc (pc) , _ ] ,  step-Sub ⟨ (Sub dest r1 r2 ) , z ∷ ( z ∷ ( z ∷ [])) ⟩ p [ pc , registers ] prf₁ cmd-prf , (refl , refl)
prf refl refl refl (step-Addi {n} {dest} {r1} {tmp} p [[ pc , registers , _ ]] prf₁ cmd-prf ) = [ suc (pc) , _ ] , step-Addi ⟨ (Addi dest r1 tmp ) , z ∷ ( z ∷ ( z ∷ [])) ⟩ p [ pc , registers ] prf₁ cmd-prf , (refl , refl)
prf refl refl refl (step-Jump {n} {jmp-pc} p [[ pc , registers , _ ]] prf₁ prf2 cmd-prf ) = [ jmp-pc , registers ] , step-Jump ⟨ (Jump jmp-pc) , _ ⟩ _ _ prf₁ prf2 cmd-prf , refl , refl

-- prf refl refl refl (step-Bgtz-l p [[ pc , registers , _ ]] prf₁ prf2 prf3 cmd-prf) = [ suc (pc) , registers ] , step-Bgtz-l ⟨ (Bgtz {!   !} {!   !}) , {!   !} ⟩ p [ pc , registers ] prf₁ {!   !} {!  !} {!   !} , ({!   !} , refl)
-- prf refl refl refl (step-Bgtz-g _ _ prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf refl refl refl (step-Enable _ _ prf₁ cmd-prf) = {!   !}
-- prf refl refl refl (step-Disable _ _ prf₁ cmd-prf) = {!   !}
prf refl refl refl _ = {!   !}
   