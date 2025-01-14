module thesis where

    
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Int


data Var : Set where
  x : Var



data L : Set where
  U : L
  T : L



record programmer-⇓ (R M Γ Q_g Q_p e : Set) : Set where
  field 
    Pass : R    