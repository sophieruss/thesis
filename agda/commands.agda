module commands where

open import Data.Nat using (ℕ)
open import Data.Vec.Base using (Vec)
open import Data.Fin using (Fin)

data Instruction : Set where
  NoOp  : Instruction
  Add   : Fin 32 → Fin 32 → Fin 32 → Instruction
  Sub   : Fin 32 → Fin 32 → Fin 32 → Instruction
  Addi  : Fin 32 → Fin 32 → ℕ → Instruction
  Jump  : ℕ → Instruction
  Bgtz  : Fin 32 → ℕ → Instruction 
  Empty : Instruction

record Program (n : ℕ) : Set where
  constructor program
  field 
    instructions : Vec Instruction n

record State : Set where
  constructor [_,_]
  field
    pc : ℕ
    registers : Vec ℕ 32
   
record Trace : Set where
  constructor ⟨_,_⟩
  field
    instr : Instruction
    args :  Vec ℕ 3