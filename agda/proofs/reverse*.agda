module agda.proofs.reverse* where

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
--     → (sₕ .Hstate.UR ≡ UR)
    → t , p , sₛ —→ sₛ'
    → ∃[ sₕ' ] (p , sₕ —→* sₕ' , t) × (equiv sₕ' sₛ')
    -- there exists one step such that the host ends up in state where the pc and registers are equivalent

-- What assumptions am I making about the trace?
-- How can I check it? I think I am assuming I trust trace. Thus don't check?


prf {n}  {p} {⟨ NoOp , (0 ∷ 0 ∷ 0 ∷ []) ⟩} {h} {s} {s'} refl (refl , refl) refl 
        (step-NoOp _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-trace prf-canStep)   
        = 
        [[ pc , reg , true , _ , _ , _ ]] , 
        step—→ p h
        [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
        ⟨ NoOp , (0 ∷ 0 ∷ 0 ∷ []) ⟩ _ 
        (done p h ⟨ NoOp , zero ∷ zero ∷ zero ∷ [] ⟩) 
        (step-NoOp p h prf-cur prf-cmd prf-canStep) , 
        (refl , refl)

prf {n}  {p} {t} {h} {s} {s'} refl (refl , refl) refl 
        (step-Add _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-trace prf-canStep)                            
        = 
        [[ (suc (pc)) , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h
        [[ suc pc , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _ 
        t t 
        (done p _ _) 
        (step-Add p _ prf-cur prf-cmd prf-canStep) , 
        (refl , refl)

prf {n}  {p} {t} {h} {s} {s'} refl (refl , refl) refl 
        (step-Sub _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-trace prf-canStep)                            
        =
        [[ (suc (pc)) , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h
        [[ suc pc , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
        t t 
        (done p _ _) 
        (step-Sub p _ prf-cur prf-cmd prf-canStep) , 
        (refl , refl)

prf {n}  {p} {t} {h} {s} {s'} refl (refl , refl) refl 
        (step-Addi _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-trace prf-canStep)                           
        =
        [[ (suc (pc)) , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h
        [[ suc pc , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _        
        t t 
        (done p _ _) 
        (step-Addi p _ prf-cur prf-cmd prf-canStep) , 
        (refl , refl)

prf {n}  {p} {⟨ Jump _ , _ ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) refl 
        (step-Jump {n} {jmp-pc} _ p [ pc , reg , URₛ ] prf-cur prf-canStep prf-cmd prf-trace ) 
        = 
        [[ jmp-pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h 
        [[ jmp-pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
        ⟨ Jump jmp-pc , jmp-pc ∷ 0 ∷ 0 ∷ [] ⟩ _ 
        (done p _ _) 
        (step-Jump p _ prf-cur prf-canStep prf-cmd) , 
        (refl , refl)

prf {n}  {p} {⟨ Bgtz _ _ , _ ∷ _ ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) refl 
        (step-Bgtz-l {n} {bgtz-pc} {x₁} {x₂} {src} _ p [ pc , reg , URₛ ] prf-cur prf-zero prf-cmd prf-trace prf-canStep) 
        = 
        [[ (suc (pc)) , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h 
        [[ (suc (pc)) , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _ 
        ⟨ Bgtz src bgtz-pc , lookup (reg) src ∷ suc pc ∷ 0 ∷ [] ⟩ _ 
        (done p _ _) 
        (step-Bgtz-l p _ prf-cur prf-zero prf-cmd prf-canStep) ,         --[[ pc , reg , true , UR , SR , ret-pc ]] —→ [[ suc pc , reg , true , UR , SR , ret-pc ]]
        (refl , refl)

prf {n}  {p} {⟨ Bgtz _ _ , _ ∷ _ ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) refl 
        (step-Bgtz-g {n} {bgtz-pc} {x₁} {x₂} {src} _ p [ pc , reg , URₛ ] prf-cur prf-canStep prf-gzero prf-cmd prf-trace) 
        = 
        [[ bgtz-pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h 
        _ _ 
        ⟨ Bgtz src bgtz-pc , lookup (reg) src ∷ bgtz-pc ∷ 0 ∷ [] ⟩ _
        (done p _ _) 
        (step-Bgtz-g p _ prf-cur prf-gzero prf-cmd prf-canStep) ,         --[[ pc , reg , true , UR , SR , ret-pc ]] —→ [[ suc pc , reg , true , UR , SR , ret-pc ]]
        (refl , refl)

prf {n}  {p} {⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) refl 
        (step-Return _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-trace)  
        = 
        [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h 
        [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
        ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ 
        (done p _ _) 
        (step-Return p h prf-cur prf-cmd) , 
        (refl , refl)  

prf {n}  {p} {⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) refl 
        (step-Alert _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-trace)  
        = 
        [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h 
        [[ pc , reg , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _
        ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ 
        (done p _ _) 
        (step-Alert p h prf-cur prf-cmd) , 
        (refl , refl) 

-- just proves that theres a way to get from call-unt back to a state that is the exact same, but trusted mode  & pc+1
prf {n}  {p} {⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) refl 
        (step-Call-Unt-Sentry {n} {jmp-pc} _ p [ pc , reg , URₛ ] prf-cur prf-canStep prf-cmd prf-canReturn prf-trace) 
        = 
        [[ suc pc , reg , true , Hstate.UR h , reg , suc pc ]] ,  --issue because this says that the UR is unchanged
        step—→ p h 
        [[ jmp-pc , reg , false , Hstate.UR h , reg , suc pc ]]   -- starte right after call-unt -- TODO: test what happens if its true?
        [[ suc pc , reg , true , _ , _ , _ ]] -- ultimate end state
        ⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _
        (step—→ p [[ jmp-pc , reg , false , Hstate.UR h , reg , suc pc ]] -- state right after call-unt
         [[ suc pc , reg , true , _ , _ , _ ]]  -- state after i take 1 step
         [[ suc pc , reg , true , _ , _ , _ ]]  -- ultimate end state
         ⟨ Return-Unt (Hstate.UR h) , 0 ∷ 0 ∷ 0 ∷ [] ⟩ _ 
         (done _ _ _)
                (step-Ret-Unt _ _ prf-cur refl ))                                        -- proof that [[ jmp-pc , reg , false , UR , reg , suc pc ]] —→ [[ suc pc , reg , true , UR , reg , suc pc ]]
                (step-Call-Unt _ _ prf-cur prf-canStep refl prf-cmd prf-canReturn) ,        -- proof that 
        refl , refl

prf {n}  {p} {t} {h} {s} {s'} refl (refl , refl) refl 
        (step-Load-UR _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-canStep prf-trace)  
        = 
        [[ suc pc , State.registers s' , true , URₛ , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p h 
        [[ suc pc , State.registers s' , true , URₛ , Hstate.SR h , Hstate.ret-pc h ]] _
        t _ 
        (done p _ _) 
        ({!   !}) , 
        (refl , refl )  

-- prf a b c (step-Add t _ _ prf-cur prf-cmd prf-trace prf-canStep) = {!   !}
-- prf a b c (step-Ret-Unt _ _ _ prf-cur prf-cmd) = {!   !} , {!   !}
prf {n}  {p} {t} {h} {s} {s'} refl (refl , refl) refl 
        (step-Ret-Unt _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-trace)  
        = 
        [[ pc , State.registers s' , true , State.UR s' , Hstate.SR h , Hstate.ret-pc h ]] , 
        step—→ p [[ pc , reg , true , ? , _ , _ ]] 
        [[ pc , State.registers s' , true , State.UR s' , Hstate.SR h , Hstate.ret-pc h ]] _
        ⟨ Return-Unt URₛ , (0 ∷ 0 ∷ 0 ∷ []) ⟩ _ 
        (done p _ _) 
        ({! step-Ret-Unt  !}) , 
        (refl , refl )  


     
     
-- prf {n}  {p} {⟨ Load-UR _ , _ ∷ 0 ∷ 0 ∷ [] ⟩} {h} {s} {s'} refl (refl , refl) refl 
--         (step-Load-UR _ p [ pc , reg , URₛ ] prf-cur prf-cmd prf-canStep prf-trace)                           
--         =
--         [[ (suc (pc)) , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] , 
--         step—→ p h
--         [[ suc pc , State.registers s' , true , Hstate.UR h , Hstate.SR h , Hstate.ret-pc h ]] _        
--         ⟨ Load-UR _ , UR ∷ 0 ∷ 0 ∷ [] ⟩ _ 
--         (done p _ _) 
--         (step-Load-UR p h prf-cur prf-cmd prf-canStep) , 
--         (refl , refl)




