module agda.proofs.reverse*reverse where

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

equiv : Hstate → State → Set
equiv sₕ sₛ = (sₕ .Hstate.pc ≡ sₛ .State.pc) × (sₕ .Hstate.registers ≡ sₛ .State.registers)

-- trusted  
prf : ∀ {n} {p : Program n} {t : Trace} {h h' : Hstate} {s : State}
    → (h .Hstate.mode ≡ true)
    → (equiv h s)
    → p , h —→* h' , t
    → ∃[ s' ] (t , p , s —→ s') × (equiv h' s')

-- my base case
prf {n} {p} {t} {h} {.h} {s} refl (refl , refl) (done .p .h .t) = 
        s , step-Done t p s , (refl , refl)


-- NoOp case
prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl) 
    (step—→ .p .h .h' _ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ (done .p .h' ._) (step-NoOp .p .h prf-cur prf-cmd)) =
    [ Hstate.pc h , Hstate.registers h ] , 
    step-NoOp _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl , 
    (refl , refl)



prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl) (step—→ .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) .([[ _ , _ , true , _ , _ , _ ]]) _ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ (done .p .([[ _ , _ , true , _ , _ , _ ]]) .(⟨ NoOp , zero ∷ zero ∷ zero ∷ [] ⟩)) (step-Ret-Unt .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-canStep prf-mode)) = ?
-- [ Hstate.pc h , Hstate.registers h ] , step-NoOp _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl , (refl , refl)


-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ (done .p .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) .t) (step-NoOp _ .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {![ suc (Hstate.pc h) , Hstate.registers h' ]   !} , ({!   !} , {!   !})


-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ (step—→ .p .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) s₁ .h' t₂ .t c x) (step-NoOp _ .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Add _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Sub _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Addi _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Jump _ _ prf-cur prf-canStep prf-cmd)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Ret-Unt _ _ prf-canStep prf-mode)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Return _ .([[ pc , registers , mode , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Alert _ .([[ pc , registers , mode , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Load-UR _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- prf refl (refl , refl) (step—→ _ _ s₁ _ t₁ _ (step—→ _ .s₁ s₂ _ t₂ _ c x₁) x) = ? 
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) a 
    -- (step—→ .p .h .h' _ t _ 
    -- (done .p .h' ._) 
    -- (step-Add .p .h prf-cur prf-cmd prf-canStep)) 
    -- =
    -- [ suc (Hstate.pc h) , updateAt (Hstate.registers h) dest (λ _ → sum) ] ,
    -- step-Add _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl prf-canStep ,
    -- (refl , refl)

