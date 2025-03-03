module steps where

open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
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
  Sw    : Fin 32 → Fin 32 → Instruction


record Program (n : ℕ) : Set where
  constructor program
  field 
    instructions : Vec Instruction n

record State : Set where
  constructor [_,_,_]
  field
    pc : ℕ
    registers : Vec ℕ 32
    memory : List ℕ
   
   
addHelper : Vec ℕ 32 →  Fin 32 → Fin 32 → Fin 32 → Vec ℕ 32
addHelper vec dest r1 r2 = 
  let newelem = (lookup vec ( r1 )) + (lookup vec ( r2))
  in updateAt vec ( dest ) (λ x → newelem)

subHelper : Vec ℕ 32 →  Fin 32 → Fin 32 → Fin 32 → Vec ℕ 32
subHelper vec dest r1 r2 = 
  let newelem = (lookup vec ( r1 )) ∸ (lookup vec ( r2))
  in updateAt vec ( dest ) (λ x → newelem)

addiHelper : Vec ℕ 32 →  Fin 32 → Fin 32 → ℕ → Vec ℕ 32
addiHelper vec dest r1 temp = 
  let newelem = (lookup vec ( r1 )) + temp
  in updateAt vec ( dest ) (λ x → newelem)

bgtzHelper : ℕ → ℕ → ℕ → ℕ
bgtzHelper src_val n pc with src_val
... | 0  = n
... | _ = suc pc 


infix 4 _,_—→_
data _,_—→_ : ∀ {n} → Program n → State → State → Set where
  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
        (prf : s .State.pc < n) → 
        ((lookup (p .Program.instructions) (fromℕ< prf)) ≡ NoOp) →
        p , s —→ [ (suc (s .State.pc)) , (s .State.registers) , (s .State.memory) ]
  
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
      (prf : s .State.pc < n ) → 
      ((lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Add dest r1 r2)) →
      p , s —→ [ (suc (s .State.pc)) , addHelper (s .State.registers) dest r1 r2 , (s .State.memory)]

  step-Sub :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    ((lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Sub dest r1 r2)) →
    p , s —→ [ (suc (s .State.pc)) , subHelper (s .State.registers) dest r1 r2 , (s .State.memory)]


  step-Addi :  ∀ {n} → {dest r1 : Fin 32} → {temp : ℕ}  → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    ((lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Addi dest r1 temp)) →
    p , s —→ [ (suc (s .State.pc)) , addiHelper (s .State.registers) dest r1 temp , (s .State.memory)]


  step-Jump : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
        (prf : s .State.pc < n) → 
        (prf2 : jmp-pc < n) → 
        ((lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Jump jmp-pc)) →
        p , s —→ [ jmp-pc , (s .State.registers) , (s .State.memory)]

  step-Bgtz : ∀ {n bgtz-pc} → {src : Fin 32} →  (p : Program n) → (s : State) →                         
        (prf : s .State.pc < n) → 
        (prf2 : bgtz-pc < n) → 
        ((lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →
        p , s —→ [ bgtzHelper (lookup (s .State.registers) src) bgtz-pc  (s .State.pc) , (s .State.registers) , (s .State.memory)]

  -- step-Bgtz-l : ∀ {n bgtz-pc} → {src : Fin 32}→  (p : Program n) → (s : State) →                         
  --     (prf : s .State.pc < n) → 
  --     (prf2 : bgtz-pc < n) → 
  --     (prf3 : (lookup (s .State.registers) src) > 0 ) → 
  --     ((lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →
  --     p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ]

infix 4 _,_—→*_
data _,_—→*_ : ∀ {n} → Program n → State → State → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : State) 
      → p , s —→* s
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State)
      → p , s₁ —→* s₂ 
      → p , s —→ s₁ 
      → p , s —→* s₂




-- open import Data.List.Base renaming (lookup to listlookup; updateAt to listupdateAt; length to listlength; _∷_ to _∻_; [] to ⟨⟩)

-- swHelper : Vec ℕ 32 → Fin 32 → Fin 32 → List ℕ → List ℕ
-- swHelper vec src dest memory  = 
--   {! updated memory list  !}
--   where
--     a = lookup vec src
--     b = lookup vec dest
--     prf = (a < listlength memory)
--     a` = listlookup memory (fromℕ< {! prf!})

-- step-Sw : ∀ {n} → {src dest : Fin 32} → (p : Program n) → (s : State) →
--         (prf : s .State.pc < n ) → 
--         ((lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Sw src dest)) →
--         p , s —→ [ ((suc (s .State.pc))) , (s .State.registers) , swHelper (s .State.registers) src dest (s .State.memory)]
