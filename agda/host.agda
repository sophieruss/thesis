module host where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<; toℕ)
open import Data.List.Base using (List)
-- open import Agda.Builtin.Bool
-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Sigma
-- open import Agda.Primitive

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
   
record Trace : Set where
  constructor ⟨_,_⟩
  field
    instr : Instruction
    args :  Vec ℕ 3

addiHelper : Vec ℕ 32 →  Fin 32 → Fin 32 → ℕ → Vec ℕ 32
addiHelper vec dest r1 temp = 
  let newelem = (lookup vec ( r1 )) + temp
  in updateAt vec ( dest ) (λ x → newelem)


infix 4 _,_—→_,_
data _,_—→_,_ : ∀ {n} → Program n → State → State → Trace → Set where
  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ NoOp) →
    p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ] , ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
  
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Add dest r1 r2)) →
      
    let    r1_val = lookup (s .State.registers) r1
    in let r2_val = lookup (s .State.registers) r2
    in let    sum = r1_val + r2_val
    in let      r = updateAt (s .State.registers) dest (λ x → sum)
    in let      t = ⟨ Add dest r1 r2 , r1_val ∷ r2_val ∷ sum ∷ [] ⟩
    
    in p , s —→ [ (suc (s .State.pc)) , r ] , t
    


  step-Sub :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Sub dest r1 r2)) →

    let    r1_val = lookup (s .State.registers) r1
    in let r2_val = lookup (s .State.registers) r2
    in let    dif = r1_val ∸ r2_val
    in let      r = updateAt (s .State.registers) dest (λ x → dif)
    in let      t = ⟨ Sub dest r1 r2 , r1_val ∷ r2_val ∷ dif ∷ [] ⟩
    
    in p , s —→ [ (suc (s .State.pc)) , r ] , t
      

  step-Addi :  ∀ {n} → {dest r1 : Fin 32} → {temp : ℕ}  → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Addi dest r1 temp)) →

    let    r1_val = lookup (s .State.registers) r1
    in let    sum = r1_val + temp
    in let      r = updateAt (s .State.registers) dest (λ x → sum)
    in let      t = ⟨ Addi dest r1 temp , r1_val ∷ sum ∷ 0 ∷ [] ⟩
    
    in p , s —→ [ (suc (s .State.pc)) , r ] , t

  step-Jump : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (prf2 : jmp-pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Jump jmp-pc)) →
    p , s —→ [ jmp-pc , (s .State.registers) ] ,
    ⟨ Jump jmp-pc , 
      jmp-pc ∷  0 ∷ 0 ∷ [] ⟩
  
  step-Bgtz-l : ∀ {n bgtz-pc} → {src : Fin 32} →  (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (prf2 : bgtz-pc < n) → 
    (prf3 : (lookup (s .State.registers) src) ≡ 0 ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →
    p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ] ,
    ⟨ Bgtz src bgtz-pc , 
      lookup (s .State.registers) src ∷  
      suc (s .State.pc) ∷ 
      0 ∷ [] ⟩

  step-Bgtz-g : ∀ {n bgtz-pc} → {src : Fin 32} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (prf2 : bgtz-pc < n) → 
    (prf3 : (lookup (s .State.registers) src) > 0 ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →
    p , s —→ [ bgtz-pc , (s .State.registers) ] , 
    ⟨ Bgtz src bgtz-pc , 
      lookup (s .State.registers) src ∷  
      bgtz-pc ∷ 
      0 ∷ [] ⟩

infix 4 _,_—→*_,_
data _,_—→*_,_ : ∀ {n} → Program n → State → State → Trace → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : State) (t : Trace) 
      → p , s —→* s , t
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State) (t : Trace)
      → p , s₁ —→* s₂ , t
      → p , s —→ s₁ , t
      → p , s —→* s₂ , t


