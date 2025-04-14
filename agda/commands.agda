module agda.commands where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec.Base using (Vec; _∷_; [])


data Instruction : Set where
  NoOp  : Instruction
  Add   : Fin 32 → Fin 32 → Fin 32 → Instruction
  Sub   : Fin 32 → Fin 32 → Fin 32 → Instruction
  Addi  : Fin 32 → Fin 32 → ℕ → Instruction
  Jump  : ℕ → Instruction
  Bgtz  : Fin 32 → ℕ → Instruction
  Enable : Instruction
  Disable : Instruction
  Call-Unt : ℕ → Instruction 
  Call-Unt-Sentry : Instruction 
  Return-Unt : ℕ → Instruction
  Return : Instruction
  Alert : Instruction
  Load-UR : Fin 32 → Instruction

  Empty : Instruction

record Program (n : ℕ) : Set where
  constructor program
  field 
    instructions : Vec Instruction n

record State : Set where
  constructor [_,_,_]
  field
    pc : ℕ
    registers : Vec ℕ 32
    UR : ℕ
  
record Trace : Set where
  constructor ⟨_,_⟩
  field
    instr : Instruction
    args :  Vec ℕ 3

emptyTrace : Trace
emptyTrace = ⟨ Empty , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 