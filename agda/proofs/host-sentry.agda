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


-- ask how to write this proof.


prf : ∀ {n} {p : Program n} {t : Trace} {sₕ sₕ' : Hstate} {sₛ sₛ' : State}
    → (sₕ .Hstate.pc  ≡ sₛ .State.pc) × (sₕ .Hstate.registers  ≡ sₛ .State.registers)
    → t , p , sₛ —→ sₛ'
    → p , sₕ —→* sₕ' , t
    → (sₕ' .Hstate.pc  ≡ sₛ' .State.pc) × (sₕ' .Hstate.registers  ≡ sₛ' .State.registers)

    -- → ∃[ sₕ' ] {! (p , sₕ —→* sₕ')  !}       -- → (sₕ' .State.pc  ≡ sₛ' .State.pc) × (sₕ' .State.registers  ≡ sₛ' .State.registers)

    -- → ∃ sₛ ((p , sₛ —→ sₛ) × ((sₛ .State.pc ≡ sₕ .State.pc) × (sₛ .State.registers ≡ sₕ .State.registers)))

    -- there exists a step such that the host ends up in state where the pc and registers are equivalent
-- how to write?? ∃ sₛ' ((p , sₛ —→ sₛ') × (sₕ' .State.pc  ≡ sₛ' .State.pc) (sₕ' .State.registers  ≡ sₛ' .State.registers) )


prf = λ samestates₁ sentrystep hoststeps → {!  !} , {!   !}
