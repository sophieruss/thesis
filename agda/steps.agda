module steps where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Data.List.Base using (List)

data Instruction : Set where
  NoOp  : Instruction
  Add   : Fin 32 → Fin 32 → Fin 32 → Instruction
  Sub   : Fin 32 → Fin 32 → Fin 32 → Instruction
  Addi  : Fin 32 → Fin 32 → ℕ → Instruction
  Jump  : ℕ → Instruction
  Bgtz  : Fin 32 → ℕ → Instruction 

record Program (n : ℕ) : Set where
  constructor program
  field 
    instructions : Vec Instruction n

record State : Set where
  constructor [_,_]
  field
    pc : ℕ
    registers : Vec ℕ 32
   

infix 4 _,_—→_
data _,_—→_ : ∀ {n} → Program n → State → State → Set where
  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
        (prf : s .State.pc < n) → 
        (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ NoOp) →
        p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ]

  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Add dest r1 r2)) →
    let sum = lookup (s .State.registers) r1 + lookup (s .State.registers) r1
    in let r = updateAt (s .State.registers) ( dest ) (λ x → sum)
    in p , s —→ [ (suc (s .State.pc)) , r ]
  

  step-Sub :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Sub dest r1 r2)) →
    let sum = lookup (s .State.registers) r1 ∸ lookup (s .State.registers) r2
    in let r = updateAt (s .State.registers) ( dest ) (λ x → sum)
    in p , s —→ [ (suc (s .State.pc)) , r ]


  step-Addi :  ∀ {n} → {dest r1 : Fin 32} → {temp : ℕ}  → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Addi dest r1 temp)) →
    let sum = lookup (s .State.registers) r1 + temp
    in let r = updateAt (s .State.registers) ( dest ) (λ x → sum)
    in p , s —→ [ (suc (s .State.pc)) , r ]

  step-Jump : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
        (prf : s .State.pc < n) → 
        (prf2 : jmp-pc < n) → 
        (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Jump jmp-pc)) →
        p , s —→ [ jmp-pc , (s .State.registers) ]
  
  step-Bgtz-l : ∀ {n bgtz-pc} → {src : Fin 32} →  (p : Program n) → (s : State) →                         
      (prf : s .State.pc < n) → 
      (prf2 : bgtz-pc < n) → 
      (prf3 : (lookup (s .State.registers) src) ≡ 0 ) → 
      (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →
      p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ]

  step-Bgtz-g : ∀ {n bgtz-pc} → {src : Fin 32} →  (p : Program n) → (s : State) →                         
      (prf : s .State.pc < n) → 
      (prf2 : bgtz-pc < n) → 
      (prf3 : (lookup (s .State.registers) src) > 0 ) → 
      (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →
      p , s —→ [ bgtz-pc , (s .State.registers) ]


infix 4 _,_—→*_
data _,_—→*_ : ∀ {n} → Program n → State → State → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : State) 
      → p , s —→* s
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State)
      → p , s₁ —→* s₂ 
      → p , s —→ s₁ 
      → p , s —→* s₂


