module agda.proofs.UR-equiv where

-- apr 6, 2024. try reversing host and sentry 

open import agda.commands
open import agda.host renaming (State to HState)
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

equiv : HState → State → Set
equiv sₕ sₛ = (sₕ .HState.pc ≡ sₛ .State.pc) × (sₕ .HState.registers ≡ sₛ .State.registers)

project : HState → State
project [[ pc , registers , mode , UR , SR , ret-pc ]] = [ pc , registers ]

load-ur-correspondence :
  ∀ {n} {dest : Fin 32} {p : Program n} {hs : HState} {t : Trace} →
  (prf-cur : hs .HState.pc < n) →
  (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Load-UR dest) →
  (prf-canStep : hs .HState.pc < n ∸ 1) →
  (t ≡ ⟨ Load-UR-Sentry dest (hs .HState.UR) , 0 ∷ 0 ∷ 0 ∷ [] ⟩) →
  -- The sentry's step produces a state consistent with the host's projected state
  ∃[ ss′ ] (t , p , project hs —→ ss′ × ss′ ≡ project ([[ (suc (hs .HState.pc)) , updateAt (hs .HState.registers) dest (λ _ → hs .HState.UR) , hs .HState.mode , hs .HState.UR , hs .HState.SR , hs .HState.ret-pc ]]))

load-ur-correspondence {n} {dest} {p} {hs = hs} {t} prf-cur prf-cmd prf-canStep refl = 
  let
    -- Host's updated state
    hs′ = [[ (suc (hs .HState.pc)) , updateAt (hs .HState.registers) dest (λ _ → hs .HState.UR) , hs .HState.mode , hs .HState.UR , hs .HState.SR , hs .HState.ret-pc ]]
    -- Sentry's updated state
    ss′ = [ (suc (hs .HState.pc)) , updateAt (hs .HState.registers) dest (λ _ → hs .HState.UR) ]
    -- Proof that the sentry takes the step
    sentry-step : t , p , project hs —→ ss′
    sentry-step = step-Load-UR _ _ _ prf-cur prf-cmd prf-canStep refl
  in
    ss′ , sentry-step , {!   !}