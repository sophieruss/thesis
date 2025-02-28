module steps where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Agda.Primitive
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)


data Instruction : Set where
  NoOp  : Instruction
  Add   : Fin 32 → Fin 32 → Fin 32 → Instruction

record Program (n : ℕ) : Set where
  constructor program
  field 
    instructions : Vec Instruction n

record State : Set where
  constructor [_,_]
  field
    pc : ℕ
    registers : Vec ℕ 32
   
   
addHelper : Vec ℕ 32 →  Fin 32 → Fin 32 → Fin 32 → Vec ℕ 32
addHelper vec dest r1 r2 = 
  let newelem = (lookup vec ( r1 )) + (lookup vec ( r2))
  in updateAt vec ( dest ) (λ x → newelem)

  -- if i made a proof, itd be a call to their proof of updateAt.properties and that theirs works 

infix 4 _,_—→_
data _,_—→_ : ∀ {n} → Program n → State → State → Set where
  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
        (prf : s .State.pc < n) → 
        ((lookup (p .Program.instructions) (fromℕ< prf)) ≡ NoOp) →
        p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ]
  
  -- step-Add : ∀ {n pc regs} {inst : Vec Instruction n} {dest r1 r2 : Fin 32}
      -- → ((program inst) , ([ pc , regs ]) —→ ([ (suc pc) , addHelper regs dest r1 r2 ]))
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
      (prf : s .State.pc < n ) → 
      ((lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Add dest r1 r2)) →
      p , s —→ [ (suc (s .State.pc)) , addHelper (s .State.registers) dest r1 r2 ]


infix 4 _,_—→*_
data _,_—→*_ : ∀ {n} → Program n → State → State → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : State) 
      → p , s —→* s
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State)
      → p , s₁ —→* s₂ 
      → p , s —→ s₁ 
      → p , s —→* s₂

