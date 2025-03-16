module agda.host where

open import agda.commands
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<; toℕ)
open import Data.List.Base using (List)
open import Data.Bool using (Bool; true)


infix 4 _,_—→_,_
data _,_—→_,_ : ∀ {n} → Program n → HostState → HostState → Trace → Set where
  step-NoOp : ∀ {n} → (p : Program n) → (s : HostState) →                         
    (prf : s .HostState.state .State.pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ NoOp) →
    p , s —→ ⟨ [ (suc (s .HostState.state .State.pc)) , (s .HostState.state .State.registers) ] , s .HostState.trusted ⟩ , 
    ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
  
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : HostState) →
    (prf : s .HostState.state .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .HostState.state .State.pc} {n} prf)) ≡ (Add dest r1 r2)) →
      
    let r1_val = lookup (s .HostState.state .State.registers) r1
        r2_val = lookup (s .HostState.state .State.registers) r2
        sum = r1_val + r2_val
        r = updateAt (s .HostState.state .State.registers) dest (λ x → sum)
        t = ⟨ Add dest r1 r2 , r1_val ∷ r2_val ∷ sum ∷ [] ⟩
        newstate = [ (suc (s .HostState.state .State.pc)) , r ]
        trusted = s .HostState.trusted
    
    in p , s —→ ⟨ newstate , trusted ⟩ , t
    


  step-Sub :  ∀ {n} → {dest r1 r2 : Fin 32} → (p : Program n) → (s : HostState) →
    (prf : s .HostState.state .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .HostState.state .State.pc} {n} prf)) ≡ (Sub dest r1 r2)) →

    let r1_val = lookup (s .HostState.state .State.registers) r1
        r2_val = lookup (s .HostState.state .State.registers) r2
        dif = r1_val ∸ r2_val
        r = updateAt (s .HostState.state .State.registers) dest (λ x → dif)
        t = ⟨ Sub dest r1 r2 , r1_val ∷ r2_val ∷ dif ∷ [] ⟩
        newstate = [ (suc (s .HostState.state .State.pc)) , r ]
        trusted = s .HostState.trusted
    
    in p , s —→ ⟨ newstate , trusted ⟩ , t
      

  step-Addi :  ∀ {n} → {dest r1 : Fin 32} → {temp : ℕ}  → (p : Program n) → (s : HostState) →
    (prf : s .HostState.state .State.pc < n ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< {s .HostState.state .State.pc} {n} prf)) ≡ (Addi dest r1 temp)) →

    let r1_val = lookup (s .HostState.state .State.registers) r1
        sum = r1_val + temp
        r = updateAt (s .HostState.state .State.registers) dest (λ x → sum)
        t = ⟨ Addi dest r1 temp , r1_val ∷ sum ∷ 0 ∷ [] ⟩
        newstate = [ (suc (s .HostState.state .State.pc)) , r ]
        trusted = s .HostState.trusted
    
    in p , s —→ ⟨ newstate , trusted ⟩ , t
    

  step-Jump : ∀ {n jmp-pc} → (p : Program n) → (s : HostState) →                         
    (prf : s .HostState.state .State.pc < n) → 
    (prf2 : jmp-pc < n) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Jump jmp-pc)) →

    let newstate = [ jmp-pc , (s .HostState.state .State.registers) ]
        trusted = s .HostState.trusted
        t =  ⟨ Jump jmp-pc , jmp-pc ∷  0 ∷ 0 ∷ [] ⟩
    
    in p , s —→ ⟨ newstate , trusted ⟩ , t

   
  
  step-Bgtz-l : ∀ {n bgtz-pc} → {src : Fin 32} →  (p : Program n) → (s : HostState) →                         
    (prf : s .HostState.state .State.pc < n) → 
    (prf2 : bgtz-pc < n) → 
    (prf3 : (lookup (s .HostState.state .State.registers) src) ≡ 0 ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →
    
    let newstate = [ (suc (s .HostState.state .State.pc)) , (s .HostState.state .State.registers) ]
        trusted = s .HostState.trusted

    in p , s —→ ⟨ newstate , trusted ⟩ ,
    ⟨ Bgtz src bgtz-pc , 
      lookup (s .HostState.state .State.registers) src ∷  
      suc (s .HostState.state .State.pc) ∷ 
      0 ∷ [] ⟩

  step-Bgtz-g : ∀ {n bgtz-pc} → {src : Fin 32} → (p : Program n) → (s : HostState) →                         
    (prf : s .HostState.state .State.pc < n) → 
    (prf2 : bgtz-pc < n) → 
    (prf3 : (lookup (s .HostState.state .State.registers) src) > 0 ) → 
    (cmd-prf : (lookup (p .Program.instructions) (fromℕ< prf)) ≡ (Bgtz src bgtz-pc)) →

    let newstate = [ bgtz-pc , (s .HostState.state .State.registers) ]
        trusted = s .HostState.trusted
    in 
      p , s —→ ⟨ newstate , trusted ⟩ ,
      ⟨ Bgtz src bgtz-pc , 
        lookup (s .HostState.state .State.registers) src ∷  
        bgtz-pc ∷ 
        0 ∷ [] ⟩

infix 4 _,_—→*_,_
data _,_—→*_,_ : ∀ {n} → Program n → HostState → HostState → Trace → Set where
    done : ∀ {n} → ∀ (p : Program n) → (s : HostState) 
      → p , s —→* s , emptyTrace -- Is there a way to ignore trace?
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : HostState) (t₁ t₂ : Trace)
      → p , s₁ —→* s₂ , t₂
      → p , s —→ s₁ , t₁
      → p , s —→* s₂ , t₂



