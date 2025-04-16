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
    → p , h —→* h' , ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩
    -- it ends in return? 
    → ∃[ s' ] (t , p , s —→ s') × (equiv h' s')


-- my base case
prf {n} {p} {t} {h} {.h} {s} refl (refl , refl) (done .p .h .t) = 
        s , step-Done t p s , (refl , refl)

prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl) 
    (step—→ .p .h .h' _ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ (done .p .h' ._) (step-NoOp .p .h prf-cur prf-cmd prf-trace)) =
    [ Hstate.pc h , Hstate.registers h ] , 
    step-NoOp _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl , 
    (refl , refl)


(done .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) .(⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩)) = [ {!   !} , {!   !} ] , ({!   !} , {!   !})
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) s₁ .h' t₁ .(⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩) c x) = {!   !} 


-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (done .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) .t) = s , step-Done t p s , (refl , refl)

-- NoOp
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (
--     step—→ p 
--     h h' ([[ pc , reg , true , _ , _ , _ ]]) 
--     _ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
--     (done p ([[ pc , reg , true , _ , _ , _ ]]) t) 
--     (step-NoOp p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) 
--     = 
--     [ pc , reg ] , (step-NoOp t p s prf-cur prf-cmd refl , refl , refl)


-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (
--     step—→ p 
--     h h' ([[ pc , reg , true , _ , _ , _ ]]) 
--     t₁ ⟨ instr , args ⟩
--     (done p ([[ pc , reg , true , _ , _ , _ ]]) t) 
--     (step-NoOp p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) 
--     = 
--     {!   !}

-- prf {n} {p} {⟨ Add _ _ _ , _ ⟩} {h} {h'} {s} refl (refl , refl) (step—→ p h h _ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ ⟨ Add _ _ _ , _ ⟩ _ (step-NoOp _ _ _ _ prf-trace)) 
--     with prf-trace
-- ... | refl = [ {!   !} , {!   !} ] , {!   !} , {!   !}
    
-- prf {n} {p} {⟨ Add _ _ _ , _ ⟩} {h} {h'} {s} refl (refl , refl) (step—→ p h h _ _ ⟨ Add _ _ _ , _ ⟩ _ (step-NoOp _ _ _ _ ())) 
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ NoOp , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Add x x₁ x₂ , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Sub x x₁ x₂ , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Addi x x₁ x₂ , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Jump x , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Bgtz x x₁ , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Enable , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Disable , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Call-Unt x , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Call-Unt-Sentry , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Return-Unt x , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Return , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Alert , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Load-UR x , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Load-UR-Sentry x x₁ , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ p h h' [[ pc , reg , true , _ , _ , _ ]] t₁ ⟨ Empty , args ⟩ (done p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t) (step-NoOp p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) = {!   !}

-- prf {n} {p} {⟨ _ , _ ⟩} {h} {h'} {s} refl (refl , refl) (
--     step—→ p 
--     h h' ([[ pc , reg , true , _ , _ , _ ]]) 
--     t₁ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 
--     (done p ([[ pc , reg , true , _ , _ , _ ]]) ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩) 
--     (step-NoOp p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace)) 
--     = 
--     [ pc , reg ] , (step-NoOp ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ p s prf-cur prf-cmd refl , refl , refl)


-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
--     (step—→ .p 
--     h h' .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → lookup (s .State.registers) _ + lookup (s .State.registers) _) , true , _ , _ , _ ]]) 
--     t₁ .t 
--     (done .p .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → lookup (s .State.registers) _ + lookup (s .State.registers) _) , true , _ , _ , _ ]]) .t) 
--     (step-Add .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep)) 
--     = 
--     {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → lookup (s .State.registers) _ ∸ lookup (s .State.registers) _) , true , _ , _ , _ ]]) t₁ .t (done .p .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → lookup (s .State.registers) _ ∸ lookup (s .State.registers) _) , true , _ , _ , _ ]]) .t) (step-Sub .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → lookup (s .State.registers) _ + _) , true , _ , _ , _ ]]) t₁ .t (done .p .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → lookup (s .State.registers) _ + _) , true , _ , _ , _ ]]) .t) (step-Addi .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ _ , s .State.registers , true , _ , _ , _ ]]) t₁ .t (done .p .([[ _ , s .State.registers , true , _ , _ , _ ]]) .t) (step-Jump .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-canStep prf-cmd)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ suc (s .State.pc) , s .State.registers , true , _ , _ , _ ]]) t₁ .t (done .p .([[ suc (s .State.pc) , s .State.registers , true , _ , _ , _ ]]) .t) (step-Bgtz-l .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-zero prf-cmd prf-canStep)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ _ , s .State.registers , true , _ , _ , _ ]]) t₁ .t (done .p .([[ _ , s .State.registers , true , _ , _ , _ ]]) .t) (step-Bgtz-g .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-gzero prf-cmd prf-canStep)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ _ , s .State.registers , false , _ , s .State.registers , suc (s .State.pc) ]]) t₁ .t (done .p .([[ _ , s .State.registers , false , _ , s .State.registers , suc (s .State.pc) ]]) .t) (step-Call-Unt .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t₁ .t (done .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) .t) (step-Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t₁ .t (done .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) .t) (step-Alert .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd)) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p h h' .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → _) , true , _ , _ , _ ]]) t₁ .t (done .p .([[ suc (s .State.pc) , updateAt (s .State.registers) _ (λ x → _) , true , _ , _ , _ ]]) .t) (step-Load-UR .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep)) = {!   !}


-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) s₁ .h' t₁ .t (step—→ .p .s₁ s₂ .h' t₂ .t (done .p .h' .t) x₁) x) = {!   !}
-- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) s₁ .h' t₁ .t (step—→ .p .s₁ s₂ .h' t₂ .t (step—→ .p .s₂ s₃ .h' t₃ .t tt x₂) x₁) x) = {!   !}








-- -- NoOp case
-- prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl) 
--     (step—→ .p .h .h' _ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ (done .p .h' ._) (step-NoOp .p .h prf-cur prf-cmd)) =
--     [ Hstate.pc h , Hstate.registers h ] , 
--     step-NoOp _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl , 
--     (refl , refl)

-- -- Add case
-- prf {n} {p} {⟨ Add dest r1 r2 , r1v ∷ r2v ∷ sum ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Add .p .h prf-cur prf-cmd prf-canStep)) =
--     {!   !}
    -- let r1-val = lookup (Hstate.registers h) r1
    --     r2-val = lookup (Hstate.registers h) r2
    -- in [ suc (Hstate.pc h) , updateAt (Hstate.registers h) dest (λ _ → r1-val + r2-val) ] ,
    -- step-Add ⟨ Add dest r1 r2 , r1-val ∷ r2-val ∷ (r1-val + r2-val) ∷ [] ⟩ 
    --          p [ Hstate.pc h , Hstate.registers h ] 
    --          prf-cur refl refl prf-canStep ,
    -- (refl , refl)

-- Sub case
-- prf {n} {p} {⟨ Sub dest r1 r2 , r1v ∷ r2v ∷ dif ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Sub .p .h prf-cur prf-cmd prf-canStep)) =
--     ?
    -- let r1-val = lookup (Hstate.registers h) r1
    --     r2-val = lookup (Hstate.registers h) r2
    -- in [ suc (Hstate.pc h) , updateAt (Hstate.registers h) dest (λ _ → r1-val ∸ r2-val) ] ,
    -- step-Sub ⟨ Sub dest r1 r2 , r1-val ∷ r2-val ∷ (r1-val ∸ r2-val) ∷ [] ⟩ 
    --          p [ Hstate.pc h , Hstate.registers h ] 
    --          prf-cur refl refl prf-canStep ,
    -- (refl , refl)

-- -- Addi case
-- prf {n} {p} {⟨ Addi dest r1 temp , r1v ∷ sum ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Addi .p .h prf-cur prf-cmd prf-canStep)) =
--     let r1-val = lookup (Hstate.registers h) r1
--     in [ suc (Hstate.pc h) , updateAt (Hstate.registers h) dest (λ _ → r1-val + temp) ] ,
--     step-Addi ⟨ Addi dest r1 temp , r1-val ∷ (r1-val + temp) ∷ 0 ∷ [] ⟩ 
--               p [ Hstate.pc h , Hstate.registers h ] 
--               prf-cur refl refl prf-canStep ,
--     (refl , refl)

-- -- Jump case
-- prf {n} {p} {⟨ Jump jmp-pc , jmp-pc ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Jump .p .h prf-cur prf-canStep prf-cmd)) =
--     [ jmp-pc , Hstate.registers h ] ,
--     step-Jump _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-canStep prf-cmd refl ,
--     (refl , refl)

-- -- Bgtz-l case
-- prf {n} {p} {⟨ Bgtz src bgtz-pc , _ ∷ next-pc ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Bgtz-l .p .h prf-cur prf-zero prf-cmd prf-canStep)) =
--     [ suc (Hstate.pc h) , Hstate.registers h ] ,
--     step-Bgtz-l _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-zero prf-cmd refl prf-canStep ,
--     (refl , refl)

-- -- Bgtz-g case
-- prf {n} {p} {⟨ Bgtz src bgtz-pc , _ ∷ bgtz-pc ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Bgtz-g .p .h prf-cur prf-gzero prf-cmd prf-canStep)) =
--     [ bgtz-pc , Hstate.registers h ] ,
--     step-Bgtz-g _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-canStep prf-gzero prf-cmd refl ,
--     (refl , refl)

-- -- Return case
-- prf {n} {p} {⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Return .p .h prf-cur prf-cmd)) =
--     h' ,
--     step-Return _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl ,
--     (refl , refl)

-- -- Alert case
-- prf {n} {p} {⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Alert .p .h prf-cur prf-cmd)) =
--     h' ,
--     step-Alert _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl ,
--     (refl , refl)

-- -- Call-Unt-Sentry case
-- prf {n} {p} {⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl)
--     (step—→ .p .h .h' _ t _ (done .p .h' ._) (step-Call-Unt .p .h prf-cur prf-jmp-pc refl prf-cmd prf-canStep)) =
--     [ suc (Hstate.pc h) , Hstate.registers h ] ,
--     step-Call-Unt-Sentry _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-jmp-pc prf-cmd prf-canStep refl ,
--     (refl , refl)





-- -- prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {h'} {s} refl (refl , refl) (step—→ .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) .([[ _ , _ , true , _ , _ , _ ]]) _ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ (done .p .([[ _ , _ , true , _ , _ , _ ]]) .(⟨ NoOp , zero ∷ zero ∷ zero ∷ [] ⟩)) (step-Ret-Unt .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) prf-canStep prf-mode)) = ?
-- -- [ Hstate.pc h , Hstate.registers h ] , step-NoOp _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl , (refl , refl)


-- -- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ (done .p .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) .t) (step-NoOp _ .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {![ suc (Hstate.pc h) , Hstate.registers h' ]   !} , ({!   !} , {!   !})


-- -- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ (step—→ .p .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) s₁ .h' t₂ .t c x) (step-NoOp _ .([[ s .State.pc , s .State.registers , true , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Add _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Sub _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Addi _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Jump _ _ prf-cur prf-canStep prf-cmd)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Ret-Unt _ _ prf-canStep prf-mode)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Return _ .([[ pc , registers , mode , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Alert _ .([[ pc , registers , mode , UR , SR , ret-pc ]]) prf-cur prf-cmd)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ [[ pc , registers , mode , UR , SR , ret-pc ]] _ t₁ _ c (step-Load-UR _ _ prf-cur prf-cmd prf-canStep)) = {!   !}
-- -- prf refl (refl , refl) (step—→ _ _ s₁ _ t₁ _ (step—→ _ .s₁ s₂ _ t₂ _ c x₁) x) = ? 
-- -- prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) a 
--     -- (step—→ .p .h .h' _ t _ 
--     -- (done .p .h' ._) 
--     -- (step-Add .p .h prf-cur prf-cmd prf-canStep)) 
--     -- =
--     -- [ suc (Hstate.pc h) , updateAt (Hstate.registers h) dest (λ _ → sum) ] ,
--     -- step-Add _ p [ Hstate.pc h , Hstate.registers h ] prf-cur prf-cmd refl prf-canStep ,
--     -- (refl , refl)

