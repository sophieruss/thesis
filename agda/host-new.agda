module agda.host-new where

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

  
  step-NoOp : ∀ {n} {t : Trace} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ NoOp) →
    -- (prf-canStep : s .State.pc < n ∸ 1 ) → 
    (prf-trace : t ≡ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩) →

    p , s —→ [[  (s .State.pc) , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t
  
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf-cur)) ≡ (Add dest r1 r2)) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        sum = r1_val + r2_val
        r = updateAt (s .State.registers) dest (λ x → sum)
        t = if (s .State.mode ) 
            then ⟨ Add dest r1 r2 , r1_val ∷ r2_val ∷ sum ∷ [] ⟩ 
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
    
    in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t
    


  step-Sub :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf-cur)) ≡ (Sub dest r1 r2)) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        dif = r1_val ∸ r2_val
        r = updateAt (s .State.registers) dest (λ x → dif)
        t = if (s .State.mode ) 
            then ⟨ Sub dest r1 r2 , r1_val ∷ r2_val ∷ dif ∷ [] ⟩ 
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
    
    in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t
      

  step-Addi :  ∀ {n} → {dest r1 : Fin 32} → {temp : ℕ}  → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf-cur)) ≡ (Addi dest r1 temp)) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r1_val = lookup (s .State.registers) r1
        sum = r1_val + temp
        r = updateAt (s .State.registers) dest (λ x → sum)
        t = if (s .State.mode ) 
            then ⟨ Addi dest r1 temp , r1_val ∷ sum ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
            
    in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t

  step-Jump : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) →
    (prf-canStep : jmp-pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ (Jump jmp-pc)) →

    let newstate = [[ jmp-pc , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
        t = if (s .State.mode ) 
            then ⟨ Jump jmp-pc , jmp-pc ∷  0 ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
      
    in p , s —→ newstate , t

  -- step-Jump : ∀ {n jmp-pc t} → (p : Program n) → (s : State) →                         
  --   (prf-cur : s .State.pc < n) →
  --   (prf-canStep : jmp-pc < n) → 
  --   (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ (Jump jmp-pc)) →
  --   let
  --     jump-trace = ⟨ Jump jmp-pc , jmp-pc ∷ 0 ∷ 0 ∷ [] ⟩
  --     noop-trace = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
  --   in
  --   (prf-trace : (t ≡ jump-trace) ⊎ (t ≡ noop-trace)) → 
    
  --   let 
  --     newstate = [[ jmp-pc , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
  --     t = if (s .State.mode) then jump-trace else noop-trace
  --   in 
  --   p , s —→ newstate , t
  
  step-Bgtz-l : ∀ {n bgtz-pc} → {src : Fin 32} →  (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    -- (prf-bgtz-pc : bgtz-pc < n) → -- do i need this? should i accept programs where this is wrong, but never hit. 
    (prf-zero : (lookup (s .State.registers) src) ≡ 0 ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ (Bgtz src bgtz-pc)) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let newstate = [[ (suc (s .State.pc)) , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
        t = if (s .State.mode ) 
            then ⟨ Bgtz src bgtz-pc , lookup (s .State.registers) src ∷  suc (s .State.pc) ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

    in p , s —→ newstate , t

  step-Bgtz-g : ∀ {n bgtz-pc} → {src : Fin 32} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-gzero : (lookup (s .State.registers) src) > 0 ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ (Bgtz src bgtz-pc)) →
    (prf-canStep : bgtz-pc < n) → 

    let newstate = [[ bgtz-pc , (s .State.registers) , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
        t = if (s .State.mode ) 
            then ⟨ Bgtz src bgtz-pc , lookup (s .State.registers) src ∷ bgtz-pc ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

    in p , s —→ newstate , t

  step-Call-Unt : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) →                 
    (prf-jmp-pc : jmp-pc < n) → 
    (prf-mode : s .State.mode ≡ true ) → --single entry
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Call-Unt jmp-pc) →
    (prf-canStep : s .State.pc < n ∸ 1 ) →    -- is this true? This states that the program MUST return from untrusted. like sorta, but also confused. 
    -- TODO : newstate = [[ jmp-pc , (s .State.registers) , false , s .State.UR , (s .State.registers) , (suc (s .State.pc)) ]]

    let newstate = [[ (suc (s .State.pc)) , (s .State.registers) , false , s .State.UR , (s .State.registers) , (suc (s .State.pc)) ]]
        t = if (s .State.mode ) 
            then ⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩ -- potential issue
            -- then ⟨ Call-Unt jmp-pc , 0 ∷ 0 ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
      
    in p , s —→ newstate , t

  step-Ret-Unt : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) →      -- Don't need? Checks if steps off end, but stepping off end is the ret-pc part.
    -- Is there a pc = 0. Do I need to be doing pc < n+1
    (prf-canStep : s .State.ret-pc ≤ n) →    -- can this be ≤, or would = n mean stepping off?
    (prf-mode : s .State.mode ≡ false ) → -- single entry
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Return-Unt) → --if i can prove deterministic without this line, maybe i am fine.

    let newstate = [[ s .State.ret-pc , s .State.SR , true , s .State.UR , s .State.SR , s .State.ret-pc ]]
        t = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
      
    in p , s —→ newstate , t


  step-Return : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Return) →
    -- (prf-trace : t ≡ ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩) →

    -- p , s —→ s , t
    p , s —→ s , ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩

  step-Alert : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Alert) →
    p , s —→ s , ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩

  step-Load-UR : ∀ {n} {t : Trace} → {dest : Fin 32} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Load-UR dest) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r = updateAt (s .State.registers) dest (λ _ → s .State.UR)
        t = if (s .State.mode ) 
            then ⟨ Load-UR dest , (s .State.UR) ∷ 0 ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
         
        h = [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
            
    -- in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t
   in p , s —→ h , t

  -- enables user to put a value into UR
  step-Put-UR : ∀ {n} → {r1 : Fin 32} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Put-UR r1) →
    (prf-mode : s .State.mode ≡ false ) → 
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r1_val = lookup (s .State.registers) r1
        newstate = [[ (suc (s .State.pc)) , s .State.SR , false , r1_val , s .State.SR , s .State.ret-pc ]]
        t = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
   
    in p , s —→ newstate , t


infix 4 _,_—→*_,_
data _,_—→*_,_ : ∀ {n} → Program n → State → State → Trace → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : State) → (t : Trace)
      → p , s —→* s , t
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State) (t₁ t₂ : Trace)
      → p , s₁ —→* s₂ , t₂
      → p , s —→ s₁ , t₁
      → p , s —→* s₂ , t₂

infix 4 _,_—→*_,_✓
data _,_—→*_,_✓ : ∀ {n} → Program n → State → State → Trace → Set where

  Return : ∀ {n} → (p : Program n) → (s : State) → (t : Trace)                  
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Return) →
    (prf-trace : t ≡ ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩) →
    p , s —→* s , t ✓
    
  step : ∀ {n} → (p : Program n) (s s₁ s₂ : State) (t₁ t₂ : Trace)
    → p , s₁ —→* s₂ , t₂ ✓
    → p , s —→ s₁ , t₁
    → p , s —→* s₂ , t₂ ✓


  