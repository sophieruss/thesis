open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
-- Assume we have the following facts:
zz : ℕ
prf3 : 0 ≡ zz
prf5 : 1 ≤ zz

-- The goal is to show ⊥ (a contradiction)
contradiction1 : ⊥
contradiction1 = {!!}  -- We need to prove that these two facts are contradictory

-- First, from prf3, we know zz = 0
zeroLookup : zz ≡ zero
zeroLookup = prf3

-- From prf5, we know zz ≥ 1
oneLessThanLookup : 1 ≤ zz
oneLessThanLookup = prf5

-- You need to show that this leads to a contradiction. In Agda, you can prove ⊥ by showing that these two facts can't hold simultaneously.
