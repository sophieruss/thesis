module agda.proofs.host-to-sentry-new where

open import agda.commands
open import agda.host-new  renaming (State to Hstate)
open import agda.sentry-new
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

proj : Hstate → State
proj [[ pc , registers , mode , UR , SR , ret-pc ]] = [ pc , registers ]

prf : ∀ {n} {p : Program n} {t : Trace} { h h' : Hstate} {s : State}
    → (h .Hstate.mode ≡ true)
    → (equiv h s)
    → p , h —→ h' , t
    → ∃[ s' ] (t , p , s —→ s') × (equiv h' s')
    -- there exists one step such that the host ends up in state where the pc and registers are equivalent

prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-NoOp p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-trace) 
    = 
    [ pc , reg ] , 
    step-NoOp _ p s prf-cur prf-cmd prf-trace , 
    (refl , refl)

    
prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Add p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep) 
    = 
    [ suc pc , (Hstate.registers h') ] ,
    step-Add t p [ pc , reg ] prf-cur prf-cmd refl prf-canStep ,
    (refl , refl)

    
prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Sub p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep) 
    = 
    [ suc pc , (Hstate.registers h') ] ,
    step-Sub t p s prf-cur prf-cmd refl prf-canStep ,
    (refl , refl)


prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Addi p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep) 
    = 
    [ suc pc , (Hstate.registers h') ] ,
    step-Addi t p s prf-cur prf-cmd refl prf-canStep ,
    (refl , refl)
    
prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Jump {n} {jmp-pc} p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-canStep prf-cmd ) 
    = 
    [ jmp-pc , (Hstate.registers h') ] ,
    step-Jump {n} t p s prf-cur prf-canStep prf-cmd refl ,
    ( refl , refl )


prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Bgtz-l p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-zero prf-cmd prf-canStep) 
    = 
    [ suc pc , (Hstate.registers h') ] ,
    step-Bgtz-l t p [ pc , reg ] prf-cur prf-zero prf-cmd refl prf-canStep ,
    (refl , refl)

prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Bgtz-g {n} {bgtz-pc} p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-gzero prf-cmd prf-canStep) 
    = 
    [ bgtz-pc , (Hstate.registers h') ] ,
    step-Bgtz-g t p [ pc , reg ] prf-cur prf-canStep prf-gzero prf-cmd refl ,
    (refl , refl)
    
prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Call-Unt p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) 
    =
    [ suc pc , reg ] ,
    step-Call-Unt-Sentry t p s prf-cur prf-jmp-pc prf-cmd prf-canStep refl ,
    refl , refl

prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Return p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd) 
    = 
    [ pc , reg ] ,
    step-Return t p s prf-cur prf-cmd refl ,
    refl , refl

prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Alert p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd) 
    =
    [ pc , reg ] ,
    step-Alert t p s prf-cur prf-cmd refl ,
    refl , refl

prf {n} {p} {t} {h} {h'} {s} refl (refl , refl) 
    (step-Load-UR p ([[ pc , reg , true , _ , _ , _ ]]) prf-cur prf-cmd prf-canStep) 
    =
    [ suc pc , (Hstate.registers h') ] ,
    step-Load-UR t p s prf-cur prf-cmd prf-canStep refl ,
    refl , refl