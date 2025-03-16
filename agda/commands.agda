module agda.commands where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec.Base using (Vec; _∷_; [])
open import Data.Bool using (Bool)


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

record HostState : Set where
  constructor ⟨_,_⟩
  field
    state : State
    trusted : Bool

record SentryState : Set where
  constructor ⟨_⟩
  field
    state : State
   
record Trace : Set where
  constructor ⟨_,_⟩
  field
    instr : Instruction
    args :  Vec ℕ 3

emptyTrace : Trace
emptyTrace = ⟨ Empty , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 