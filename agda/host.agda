module agda.host where

open import agda.commands hiding (State)
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<; toℕ)
open import Data.List.Base using (List)
open import Data.Bool using (Bool; true; false; if_then_else_)


record State : Set where
  constructor [[_,_,_,_,_,_]]
  field
    pc : ℕ
    registers : Vec ℕ 32
    mode : Bool             -- 1 trusted
    UR : ℕ                  -- untrusted register
    SR : Vec ℕ 32           -- saved registers (copy)
    ret-pc : ℕ              -- pc to return to

   

infix 4 _,_—→_,_
data _,_—→_,_ : ∀ {n} → Program n → State → State → Trace → Set where

  
  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ NoOp) →
    p , s —→ [[  (s .State.pc) , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
  
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Add dest r1 r2)) →
      
    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        sum = r1_val + r2_val
        r = updateAt (s .State.registers) dest (λ x → sum)
        t = if (s .State.mode ) 
            then ⟨ Add dest r1 r2 , r1_val ∷ r2_val ∷ sum ∷ [] ⟩ 
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
    
    in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t
    


  step-Sub :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Sub dest r1 r2)) →

    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        dif = r1_val ∸ r2_val
        r = updateAt (s .State.registers) dest (λ x → dif)
        t = if (s .State.mode ) 
            then ⟨ Sub dest r1 r2 , r1_val ∷ r2_val ∷ dif ∷ [] ⟩ 
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
    
    in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t
      

  step-Addi :  ∀ {n} → {dest r1 : Fin 32} → {temp : ℕ}  → (p : Program n) → (s : State) →
    (prf : s .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf)) ≡ (Addi dest r1 temp)) →

    let r1_val = lookup (s .State.registers) r1
        sum = r1_val + temp
        r = updateAt (s .State.registers) dest (λ x → sum)
        t = if (s .State.mode ) 
            then ⟨ Addi dest r1 temp , r1_val ∷ sum ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
            
    in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t

  step-Jump : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) →
    (prf2 : jmp-pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Jump jmp-pc)) →

    let newstate = [[ jmp-pc , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
        t = if (s .State.mode ) 
            then ⟨ Jump jmp-pc , jmp-pc ∷  0 ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
      
    in p , s —→ newstate , t
  
  step-Bgtz-l : ∀ {n bgtz-pc} → {src : Fin 32} →  (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (prf2 : bgtz-pc < n) → 
    (prf3 : (lookup (s .State.registers) src) ≡ 0 ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →

    let newstate = [[ (suc (s .State.pc)) , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
        t = if (s .State.mode ) 
            then ⟨ Bgtz src bgtz-pc , lookup (s .State.registers) src ∷  suc (s .State.pc) ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

    in p , s —→ newstate , t

  step-Bgtz-g : ∀ {n bgtz-pc} → {src : Fin 32} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (prf2 : bgtz-pc < n) → 
    (prf3 : (lookup (s .State.registers) src) > 0 ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →

    let newstate = [[ bgtz-pc , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
        t = if (s .State.mode ) 
            then ⟨ Bgtz src bgtz-pc , lookup (s .State.registers) src ∷ bgtz-pc ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

    in p , s —→ newstate , t

  -- step-Enable : ∀ {n} → (p : Program n) → (s : State) →                         
  --   (prf : s .State.pc < n) → 
  --   (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ Enable) →
  --   p , s —→ [[ (suc (s .State.pc)) , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , ⟨ Enable , 0 ∷ 0 ∷ 0 ∷ [] ⟩

  -- step-Disable : ∀ {n} → (p : Program n) → (s : State) →                         
  --   (prf : s .State.pc < n) → 
  --   (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ Disable) →
  --   p , s —→ [[ (suc (s .State.pc)) , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , ⟨ Disable , 0 ∷ 0 ∷ 0 ∷ [] ⟩
  
  step-Call-Unt : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (prf2 : jmp-pc < n) → 
    (prf3 : s .State.mode ≡ true ) → --single entry
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ Call-Unt jmp-pc) →

    let newstate = [[ jmp-pc , (s .State.registers) , false , s .State.UR , (s .State.registers) , (suc (s .State.pc)) ]]
        t = if (s .State.mode ) 
            then ⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩ -- potential issue
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
      
    in p , s —→ newstate , t

  step-Ret-Unt : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (prf2 : s .State.ret-pc < n) → 
    (prf3 : s .State.mode ≡ false ) → -- single entry
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ Return-Unt ) →

    let newstate = [[ s .State.ret-pc , (s .State.SR) , true , s .State.UR , (s .State.SR) , s .State.ret-pc ]]
        t = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
      
    in p , s —→ newstate , t


  step-Return : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ Return) →
    p , s —→ s , ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩

  step-Alert : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf : s .State.pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ Alert) →
    p , s —→ s , ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩


infix 4 _,_—→*_,_
data _,_—→*_,_ : ∀ {n} → Program n → State → State → Trace → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : State) → (t : Trace)
      → p , s —→* s , t -- Is there a way to ignore trace?
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State) (t₁ t₂ : Trace)
      → p , s₁ —→* s₂ , t₂
      → p , s —→ s₁ , t₁
      → p , s —→* s₂ , t₂

-- infix 4 _,_—→*_
-- data _,_—→*_ : ∀ {n} → Program n → State → State → Set where
--     done : ∀ {n} → ∀ (p : Program n) → (s : State) 
--       → p , s —→* s  -- Is there a way to ignore trace?
--     step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State) (t₁ : Trace)
--       → p , s₁ —→* s₂
--       → p , s —→ s₁ , t₁
--       → p , s —→* s₂

 