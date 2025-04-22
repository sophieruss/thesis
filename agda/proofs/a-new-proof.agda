module agda.proofs.a-new-proof where

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

project : Hstate → State
project [[ pc , registers , mode , UR , SR , ret-pc ]] = [ pc , registers ]

prf : ∀ {n} {p : Program n} {t t' : Trace} {h h' : Hstate} {s s' : State}
    → (h .Hstate.mode ≡ true)
    → (equiv h s)
    → p , h —→* h' , t' ✓
    → ∃[ s' ] (t , p , s —→ s') × (equiv h' s')


prf {n} {p} {⟨ NoOp , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Add x x₁ x₂ , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Sub x x₁ x₂ , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Addi x x₁ x₂ , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Jump x , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Bgtz x x₁ , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Enable , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Disable , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Call-Unt x , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Call-Unt-Sentry , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Return-Unt x , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Return , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Alert , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Load-UR x , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Load-UR-Sentry x x₁ , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
prf {n} {p} {⟨ Empty , args ⟩} {t'} {h} {h'} {s} {s'} refl (refl , refl) (Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t' prf-cur prf-cmd prf-trace) = {!   !}
-- [ s .State.pc , s .State.registers ] , step-Return t p s prf-cur prf-cmd {!  prf-trace !} , refl , refl

-- prf {n} {p} {t} {t'} {h} {h'} {s} {s'} refl (refl , refl) ( Return .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) t₁ prf-cur prf-cmd prf-trace) = [ s .State.pc , s .State.registers ] , step-Return t p s prf-cur prf-cmd {!  prf-trace !} , refl , refl
prf {n} {p} {t} {t'} {h} {h'} {s} {s'} refl (refl , refl) (step .p .([[ s .State.pc , s .State.registers , true , _ , _ , _ ]]) s₁ .h' t₁ .t' d x) = {!   !}

-- prf {n} {p} {t} {t'} {h} {h'} {s} {s'} refl (refl , refl) (done .p .h .t') = s , done t p s , refl , refl 
-- prf {n} {p} {t} {t'} {h} {h'} {s} {s'} mode h≡s t≡ret (step—→ prog .h s₁ .h' t₁ .t' h—→* x) = {!   !}   