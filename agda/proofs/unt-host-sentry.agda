module agda.proofs.unt-host-sentry where

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

-- trusted  
prf : ∀ {n} {p : Program n} {t : Trace} {sₕ sₕ' : Hstate} {sₛ : State}
    → (sₕ .Hstate.mode ≡ false)
    → (sₕ .Hstate.pc  ≡ sₛ .State.pc)
    → (sₕ .Hstate.registers  ≡ sₛ .State.registers)
    → p , sₕ —→ sₕ' , t
    → ∃[ sₛ' ] (t , p , sₛ —→ sₛ') × (sₕ' .Hstate.pc  ≡ sₛ' .State.pc) × (sₕ' .Hstate.registers ≡ sₛ' .State.registers)
    -- there exists one step such that the host ends up in state where the pc and registers are equivalent

-- What assumptions am I making about the trace?
-- How can I check it? I think I am assuming I trust trace. Thus don't check?

-- (mode)(pc) (reg)          (p ,  sₕ —→ sₕ' , t )                                           (sₛ')                t                            p       sₛ                       pc     reg
prf refl refl refl (step-NoOp p ([[ pc , reg , mode , UR , SR , ret_pc ]]) prf₁ cmd-prf) = [ pc , reg ] , (step-NoOp ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ p [ pc , reg ] prf₁ cmd-prf) , (refl , refl)
prf refl refl refl (step-Add {n} {dest} {r1} {r2} p ([[ pc , reg , false , _ , _ , _ ]]) prf₁ cmd-prf) = [ suc (pc) , _ ] , step-NoOp ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ p [ pc , reg ] prf₁ cmd-prf , ? , ?
-- prf refl refl refl (step-Sub {n} {dest} {r1} {r2} p ([[ pc , reg , true , _ , _ , _ ]]) prf₁ cmd-prf) = [ suc (pc) , _ ] ,  step-Sub ⟨ (Sub dest r1 r2 ) , lookup reg r1 ∷ (lookup reg r2 ∷ ( (lookup reg r1 ∸ lookup reg r2) ∷ [])) ⟩ p [ pc , reg ] prf₁ cmd-prf , refl , refl
-- prf refl refl refl (step-Addi {n} {dest} {r1} {tmp} p ([[ pc , reg , true , _ , _ , _ ]]) prf₁ cmd-prf) = [ suc (pc) , _ ] , step-Addi ⟨ (Addi dest r1 tmp ) , lookup reg r1 ∷ (lookup reg r1 + tmp ∷ ( 0 ∷ []))   ⟩ p [ pc , reg ] prf₁ cmd-prf , refl , refl
-- prf refl refl refl (step-Jump {n} {jmp-pc} p ([[ pc , reg ,  _ , _ , _ , _ ]]) prf₁ prf2 cmd-prf) = [ jmp-pc , reg ] , step-Jump ⟨ (Jump jmp-pc) , _ ⟩ _ _ prf₁ prf2 cmd-prf , refl , refl
-- prf refl refl refl (step-Bgtz-l {n} {bgtz-pc} {src} p ([[ pc , reg , true , _ , _ , _ ]]) prf₁ prf2 prf3 cmd-prf) = [ suc (pc) , reg ] , step-Bgtz-l ⟨ (Bgtz src bgtz-pc) , lookup reg src ∷ suc pc ∷ 0 ∷ []  ⟩ p [ pc , reg ] prf₁ prf2 prf3 cmd-prf , ( refl , refl)
-- prf refl refl refl (step-Bgtz-g {n} {bgtz-pc} {src} p ([[ pc , reg , true , _ , _ , _ ]]) prf₁ prf2 prf3 cmd-prf) = [ bgtz-pc , reg ] , step-Bgtz-g ⟨ (Bgtz src bgtz-pc) , lookup reg src ∷ bgtz-pc ∷ 0 ∷ []  ⟩ p [ pc , reg ] prf₁ prf2 prf3 cmd-prf , ( refl , refl)

-- prf refl refl refl (step-Return p ([[ pc , reg , true , _ , _ , _ ]]) prf₁ cmd-prf) = [ pc , reg ] , (step-Return ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩ p [ pc , reg ] prf₁ cmd-prf) , (refl , refl)
-- prf refl refl refl (step-Alert p ([[ pc , reg , true , _ , _ , _ ]]) prf₁ cmd-prf) = [ pc , reg ] , (step-Alert ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩ p [ pc , reg ] prf₁ cmd-prf) , (refl , refl)
 
-- -- i'm confused. these states obviously aren't equivalent, after 1 step. these are just the expected equivalent steps. 
-- -- prf refl refl refl (step-Call-Unt {n} {jmp-pc} p ([[ pc , reg , mode , UR , SR , ret-pc ]]) prf₁ prf2 prf3 cmd-prf) = [ suc (pc) , reg ] , {!   !} , ({!   !} , {!   !})
-- prf refl refl refl (step-Ret-Unt p ([[ pc , reg , true , UR , SR , ret-pc ]]) prf₁ prf2 prf3 cmd-prf) = {!   !} , {!   !} --absurd; prf3

prf refl refl refl _ = {!   !}



-- /////////////////////////////////////

 
 