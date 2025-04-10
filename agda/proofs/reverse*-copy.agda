module agda.proofs.reverse*-copy where

-- apr 6, 2024. try reversing host and sentry 

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

-- trusted  
prf : ∀ {n} {p : Program n} {t : Trace} {sₕ : Hstate} {sₛ sₛ' : State}
    → (sₕ .Hstate.mode ≡ true)
    → (equiv sₕ sₛ)
    → t , p , sₛ —→ sₛ'
    → ∃[ sₕ' ] (p ,  sₕ —→* sₕ' , t) × (equiv sₕ' sₛ')
    -- there exists one step such that the host ends up in state where the pc and registers are equivalent



-- prf {n} {p} {⟨ NoOp , args ⟩} {h} {s} {s'} refl (refl , refl) (step-NoOp .(⟨ NoOp , args ⟩) .p .s prf₁ cmd-prf) = {!   !}
-- prf {n} {p} {⟨ NoOp , args ⟩} {h} {s} {s'} refl (refl , refl) (step-Jump .(⟨ NoOp , args ⟩) .p .s prf₁ prf2 cmd-prf) = {!   !}
-- prf {n} {p} {⟨ NoOp , args ⟩} {h} {s} {s'} refl (refl , refl) (step-Bgtz-l .(⟨ NoOp , args ⟩) .p .s prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf {n} {p} {⟨ NoOp , args ⟩} {h} {s} {s'} refl (refl , refl) (step-Bgtz-g .(⟨ NoOp , args ⟩) .p .s prf₁ prf2 prf3 cmd-prf) = {!   !}
-- prf {n} {p} {⟨ NoOp , args ⟩} {h} {s} {s'} refl (refl , refl) (step-Call-Unt-Sentry .(⟨ NoOp , args ⟩) .p .s prf₁ cmd-prf) = {!   !}
-- prf {n} {p} {⟨ NoOp , args ⟩} {h} {s} {s'} refl (refl , refl) (step-Return .(⟨ NoOp , args ⟩) .p .s prf₁ cmd-prf) = {!   !}
-- prf {n} {p} {⟨ NoOp , args ⟩} {h} {s} {s'} refl (refl , refl) (step-Alert .(⟨ NoOp , args ⟩) .p .s prf₁ cmd-prf) = {!   !}
prf {n} {p} {⟨ Add x x₁ x₂ , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Sub x x₁ x₂ , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Addi x x₁ x₂ , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Jump x , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Bgtz x x₁ , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Enable , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Disable , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Call-Unt x , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Call-Unt-Sentry , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Return-Unt , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Return , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Alert , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}
prf {n} {p} {⟨ Empty , args ⟩} {h} {s} {s'} refl (refl , refl) c = {!   !}


prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-NoOp _ p [ pc , reg ] prf₁ cmd-prf)   
        = [[ pc , reg , true , _ , _ , _ ]] , 
        step—→ p h
        [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
        ⟨ NoOp , (0 ∷ 0 ∷ 0 ∷ []) ⟩ _ 
        (done p h ⟨ NoOp , zero ∷ zero ∷ zero ∷ [] ⟩) 
        (step-NoOp p h prf₁ cmd-prf) , 
        (refl , refl)


prf {t = ⟨ NoOp , suc x ∷ zero ∷ zero ∷ [] ⟩} {sₛ = [ _ , _ ]} refl (refl , refl)
    (step-NoOp .(⟨ NoOp , suc x ∷ zero ∷ zero ∷ [] ⟩) _ .([ _ , _ ])
       prf₁
       cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ suc x₁ ∷ zero ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-NoOp .(⟨ NoOp , x ∷ suc x₁ ∷ zero ∷ [] ⟩) _ .([ _ , _ ]) prf₁
cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ x₁ ∷ suc x₂ ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-NoOp .(⟨ NoOp , x ∷ x₁ ∷ suc x₂ ∷ [] ⟩) _ .([ _ , _ ]) prf₁
cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-Jump .(⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩) _ .([ _ , _ ]) prf₁ prf2
cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-Bgtz-l .(⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩) _ .([ _ , _ ]) prf₁
prf2
prf3
cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-Bgtz-g .(⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩) _ .([ _ , _ ]) prf₁
prf2
prf3
cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-Call-Unt-Sentry .(⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩) _ .([ _ , _ ])
prf₁
cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-Return .(⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩) _ .([ _ , _ ]) prf₁
cmd-prf) = ?
prf {t = ⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩} {sₛ = [ _ , _ ]} refl
(refl , refl)
(step-Alert .(⟨ NoOp , x ∷ x₁ ∷ x₂ ∷ [] ⟩) _ .([ _ , _ ]) prf₁
cmd-prf) = ?






-- prf {n} {p} {⟨ Add _ _ _ , _ ∷ _ ∷ _ ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-Add {n} {dest} {r1} {r2} _ p [ pc , reg ] prf₁ cmd-prf)                            
--         = [[ (suc (pc)) , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h
--         [[ suc pc , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _ 
--         ? _ 
--         (done p _ _) 
--         (step-Add p _ prf₁ cmd-prf) , 
--         (refl , refl)

-- prf {n} {p} {t} {h} {s} {s'} refl (refl , refl) (step-Sub _ p [ pc , reg ] prf₁ cmd-prf)                            
--         = [[ (suc (pc)) , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h
--         [[ suc pc , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
--         t t 
--         (done p _ _) 
--         (step-Sub p _ prf₁ cmd-prf) , 
--         (refl , refl)

-- prf {n} {p} {t} {h} {s} {s'} refl (refl , refl) (step-Addi _ p [ pc , reg ] prf₁ cmd-prf)                           
--         = [[ (suc (pc)) , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h
--         [[ suc pc , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _        
--         t t 
--         (done p _ _) 
--         (step-Addi p _ prf₁ cmd-prf) , 
--         (refl , refl)

-- prf {n} {p} {⟨ Jump _ , _ ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-Jump {n} {jmp-pc} _ p [ pc , reg ] prf₁ prf2 cmd-prf) 
--         = [[ jmp-pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h 
--         [[ jmp-pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
--         ⟨ Jump jmp-pc , jmp-pc ∷ 0 ∷ 0 ∷ [] ⟩ _ 
--         (done p _ _) 
--         (step-Jump p _ prf₁ prf2 cmd-prf) , 
--         (refl , refl)

-- prf {n} {p} {⟨ Bgtz _ _ , _ ∷ _ ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-Bgtz-l {n} {bgtz-pc} {src} _ p [ pc , reg ] prf₁ prf2 prf3 cmd-prf) 
--         = [[ (suc (pc)) , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h 
--         [[ (suc (pc)) , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _ 
--         ⟨ Bgtz src bgtz-pc , lookup (reg) src ∷ suc pc ∷ 0 ∷ [] ⟩ _ 
--         (done p _ _) 
--         {! step-Bgtz-g!} ,
--         (refl , refl)

-- prf {n} {p} {⟨ Bgtz _ _ , _ ∷ _ ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-Bgtz-g {n} {bgtz-pc} {src} _ p [ pc , reg ] prf₁ prf2 prf3 cmd-prf) 
--         = [[ bgtz-pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h 
--         _ _ 
--         ⟨ Bgtz src bgtz-pc , lookup (reg) src ∷ bgtz-pc ∷ 0 ∷ [] ⟩ _
--         (done p _ _) 
--         (step-Bgtz-g p _ prf₁ prf2 prf3 cmd-prf) ,
--         (refl , refl)

-- prf {n} {p} {⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-Return _ p [ pc , reg ] prf₁ cmd-prf)  
--         = [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h 
--         [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
--         ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ 
--         (done p _ _) 
--         (step-Return p h prf₁ cmd-prf) , 
--         (refl , refl)  

-- prf {n} {p} {⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-Alert _ p [ pc , reg ] prf₁ cmd-prf)  
--         = [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h 
--         [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
--         ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ 
--         (done p _ _) 
--         (step-Alert p h prf₁ cmd-prf) , 
--         (refl , refl) 



-- -- prf refl (refl , refl) (step-NoOp _ p [ pc , reg ] prf₁ cmd-prf) = {!   !}
-- -- prf refl (refl , refl) (step-Jump _ _ _ prf₁ prf2 cmd-prf) = {!   !}
-- -- prf refl (fst , snd) (step-Bgtz-l _ _ _ prf₁ prf2 prf3 cmd-prf) = {!   !}
-- -- prf refl (refl , refl) (step-Bgtz-g _ _ _ prf₁ prf2 prf3 cmd-prf) = {!   !}
-- -- prf refl (fst , snd) (step-Call-Unt-Sentry _ _ _ prf₁ cmd-prf) = {!   !}
-- -- prf refl (fst , snd) (step-Return _ _ _ prf₁ cmd-prf) = {!   !}
-- -- prf refl (fst , snd) (step-Alert _ _ _ prf₁ cmd-prf) = {!   !} 
-- -- prf {n} {p} {⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) (step-NoOp _ p [ pc , reg ] prf₁ cmd-prf)   
-- --         = [[ pc , reg , true , _ , _ , _ ]] , 
-- --         step—→ p h
-- --         [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
-- --         ⟨ NoOp , (0 ∷ 0 ∷ 0 ∷ []) ⟩ _ 
-- --         (done p h ⟨ NoOp , zero ∷ zero ∷ zero ∷ [] ⟩) 
-- --         (step-NoOp p h prf₁ cmd-prf) , 
-- --         (refl , refl)