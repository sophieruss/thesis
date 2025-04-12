module agda.sentry where

open import agda.commands
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<; toℕ)
open import Data.List.Base using (List)

infix 4 _,_,_—→_
data _,_,_—→_ : ∀ {n} → Trace → Program n → State → State → Set where

  step-NoOp : ∀ {n} → (t : Trace) → (p : Program n) → (s : State) →                     
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ NoOp) →
    (prf-trace : t ≡ ⟨ NoOp , (0 ∷ 0 ∷ 0 ∷ []) ⟩) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    t , p , s —→ [ (s .State.pc) , (s .State.registers) ]
   
  step-Add :  ∀ {n} → {dest r1 r2 : Fin 32} → (t : Trace) → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf-cur)) ≡ (Add dest r1 r2)) →
    (prf-trace : t .Trace.instr ≡ Add dest r1 r2) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        sum = r1_val + r2_val
        r = updateAt (s .State.registers) dest (λ x → sum)
        t = ⟨ Add dest r1 r2 , r1_val ∷ r2_val ∷ sum ∷ [] ⟩
    
    in t , p , s —→ [ (suc (s .State.pc)) , r ] 
    

  step-Sub :  ∀ {n} → {dest r1 r2 : Fin 32} → (t : Trace) → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf-cur)) ≡ (Sub dest r1 r2)) →
    (prf-trace : t .Trace.instr ≡ Sub dest r1 r2) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        dif = r1_val ∸ r2_val
        r = updateAt (s .State.registers) dest (λ x → dif)
        t = ⟨ Sub dest r1 r2 , r1_val ∷ r2_val ∷ dif ∷ [] ⟩
    
    in t , p , s —→ [ (suc (s .State.pc)) , r ]
      

  step-Addi :  ∀ {n} → {dest r1 : Fin 32} → {temp : ℕ} → (t : Trace) → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< {s .State.pc} {n} prf-cur)) ≡ (Addi dest r1 temp)) →
    (prf-trace : t .Trace.instr ≡ Addi dest r1 temp) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    let r1_val = lookup (s .State.registers) r1
        sum = r1_val + temp
        r = updateAt (s .State.registers) dest (λ x → sum)
        t = ⟨ Addi dest r1 temp , r1_val ∷ sum ∷ 0 ∷ [] ⟩
    
    in t , p , s —→ [ (suc (s .State.pc)) , r ]

  step-Jump : ∀ {n jmp-pc x₁ x₂} → (t : Trace) → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-canStep : jmp-pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ (Jump jmp-pc)) →
    (prf-trace : t ≡ ⟨ Jump x₁ , x₂ ∷ 0 ∷ 0 ∷ [] ⟩) →

    t , p , s —→ [ jmp-pc , (s .State.registers) ]
  
  step-Bgtz-l : ∀ {n bgtz-pc x₁ x₂} → {src : Fin 32} → (t : Trace) → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    -- (prf-bgtz-pc : bgtz-pc < n) → 
    (prf-zero : (lookup (s .State.registers) src) ≡ 0 ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ (Bgtz src bgtz-pc)) →
    (prf-trace : t ≡ ⟨ Bgtz src bgtz-pc , x₁ ∷ x₂ ∷ 0 ∷ [] ⟩) →
    (prf-canStep : s .State.pc < n ∸ 1 ) → 

    t , p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ]
    

  step-Bgtz-g : ∀ {n bgtz-pc x₁ x₂} → {src : Fin 32} → (t : Trace) → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-canStep : bgtz-pc < n) → 
    (prf-gzero : (lookup (s .State.registers) src) > 0 ) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ (Bgtz src bgtz-pc)) →
    (prf-trace : t ≡ ⟨ Bgtz src bgtz-pc , x₁ ∷ x₂ ∷ 0 ∷ [] ⟩) →

    t , p , s —→ [ bgtz-pc , (s .State.registers) ]


  step-Call-Unt-Sentry : ∀ {n jmp-pc} → (t : Trace) → (p : Program n) → (s : State) →                     
    (prf-cur : s .State.pc < n) → 
    (prf-canStep : jmp-pc < n) →                                                           -- Can i have this as a check?  The sentry shouldn't need it, but it makes the proof easier? But maybe that gets rid of the point of the proof and proof is trivial at that point
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Call-Unt jmp-pc) → -- Am I allowed to send jmp-pc? Why not I guess? beard says yes.
    (prf-canReturn : s .State.pc < n ∸ 1) → 
    -- (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Call-Unt-Sentry) → 

    (prf-trace : t ≡ ⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩) →

    t , p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ] 
    -- pc + 1
    -- TODO: I do not need to send/check where the jmp-pc goes. 
    -- Should I have two notions call-unt. 
    -- If I default to 0, will things break

  -- will never go here becuase this would be a NoOp, since starts as untrusted 
  -- step-Ret-Unt : ∀ {n} → (t : Trace) → (p : Program n) → (s : State) →                     
  --   (prf-cur : s .State.pc < n) → 
  --   (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Return-Unt) →
  --   t , p , s —→ [ (suc (s .State.pc)) , (s .State.registers) ] 
  --   -- pc + 1

  step-Return : ∀ {n} → (t : Trace) → (p : Program n) → (s : State) →                     
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Return) →
    (prf-trace : t ≡ ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩) →

    t , p , s —→ s

  step-Alert : ∀ {n} → (t : Trace) → (p : Program n) → (s : State) →                     
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : (lookup (p .Program.instructions) (fromℕ< prf-cur)) ≡ Alert) →
    (prf-trace : t ≡ ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩) →

    t , p , s —→ s  

    
infix 4 _,_,_—→*_
data _,_,_—→*_ : ∀ {n} → Trace → Program n → State → State → Set where
    done : ∀ {n} → ∀ (t : Trace) (p : Program n) → (s : State) 
      → t , p , s —→* s
    step—→ : ∀ {n} → ∀ (p : Program n) (s s₁ s₂ : State) (t t₁ : Trace)
      → t , p , s —→ s₁
      → t₁ , p , s₁ —→* s₂
      → t , p , s —→* s₂


 