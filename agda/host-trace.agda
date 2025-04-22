module agda.host-trace where

--old version of host. This works with postulate-prf

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


-- buildTrace : State → Instruction → Vec ℕ 3 → Trace
-- buildTrace s inst vals =
--   if s .State.mode then
--     ⟨ inst , vals ⟩
--   else
--     ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

buildTraceTrusted : State → Instruction → Trace
buildTraceTrusted s NoOp = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
buildTraceTrusted s (Add dest r1 r2) =
  let r1_val = lookup (s .State.registers) r1
      r2_val = lookup (s .State.registers) r2
  in ⟨ Add dest r1 r2 , r1_val ∷ r2_val ∷ (r1_val + r2_val) ∷ [] ⟩
buildTraceTrusted s (Sub dest r1 r2) =
  let r1_val = lookup (s .State.registers) r1
      r2_val = lookup (s .State.registers) r2
  in ⟨ Sub dest r1 r2 , r1_val ∷ r2_val ∷ (r1_val ∸ r2_val) ∷ [] ⟩
buildTraceTrusted s (Addi dest r1 temp) =
  let r1_val = lookup (s .State.registers) r1
  in ⟨ Addi dest r1 temp , r1_val ∷ (r1_val + temp) ∷ 0 ∷ [] ⟩
buildTraceTrusted s (Jump jmp-pc) = ⟨ Jump jmp-pc , jmp-pc ∷ 0 ∷ 0 ∷ [] ⟩
-- buildTraceTrusted s (Bgtz src bgtz-pc) =
--   let src_val = lookup (s .State.registers) src
--       next-pc = if src_val > 0 then bgtz-pc else suc (s .State.pc)
--   in ⟨ Bgtz src bgtz-pc , src_val ∷ next-pc ∷ 0 ∷ [] ⟩
buildTraceTrusted s (Call-Unt jmp-pc) = ⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩
buildTraceTrusted s Return-Unt = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
buildTraceTrusted s Return = ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩
buildTraceTrusted s Alert = ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩
buildTraceTrusted s (Load-UR dest) = ⟨ Load-UR-Sentry dest (s .State.UR) , 0 ∷ 0 ∷ 0 ∷ [] ⟩
buildTraceTrusted s _ = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

buildTrace : State → Instruction → Trace
buildTrace s inst with s .State.mode
... | false = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
... | true = buildTraceTrusted s inst




infix 4 _,_—→_,_
data _,_—→_,_ : ∀ {n} → Program n → State → State → Trace → Set where

  step-NoOp : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ NoOp) →
    p , s —→ [[ s .State.pc , s .State.registers , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , buildTrace s NoOp 
  
  step-Add : ∀ {n} {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Add dest r1 r2) →
    (prf-canStep : s .State.pc < n ∸ 1) → 
    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        sum = r1_val + r2_val
        r = updateAt (s .State.registers) dest (λ _ → sum)
    in p , s —→ [[ suc (s .State.pc) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , buildTrace s (Add dest r1 r2)
    
  step-Sub : ∀ {n} {dest r1 r2 : Fin 32} → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Sub dest r1 r2) →
    (prf-canStep : s .State.pc < n ∸ 1) → 
    let r1_val = lookup (s .State.registers) r1
        r2_val = lookup (s .State.registers) r2
        dif = r1_val ∸ r2_val
        r = updateAt (s .State.registers) dest (λ _ → dif)
    in p , s —→ [[ suc (s .State.pc) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , buildTrace s (Sub dest r1 r2) 
      
  step-Addi : ∀ {n} {dest r1 : Fin 32} {temp : ℕ} → (p : Program n) → (s : State) →
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Addi dest r1 temp) →
    (prf-canStep : s .State.pc < n ∸ 1) → 
    let r1_val = lookup (s .State.registers) r1
        sum = r1_val + temp
        r = updateAt (s .State.registers) dest (λ _ → sum)
    in p , s —→ [[ suc (s .State.pc) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , buildTrace s (Addi dest r1 temp) 

  step-Jump : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) →
    (prf-canStep : jmp-pc < n) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Jump jmp-pc) →
    p , s —→ [[ jmp-pc , s .State.registers , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , buildTrace s (Jump jmp-pc) 
  
  step-Bgtz-l : ∀ {n bgtz-pc} {src : Fin 32} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-zero : lookup (s .State.registers) src ≡ 0) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Bgtz src bgtz-pc) →
    (prf-canStep : s .State.pc < n ∸ 1) → 
    p , s —→ [[ suc (s .State.pc) , s .State.registers , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , buildTrace s (Bgtz src bgtz-pc)

  step-Bgtz-g : ∀ {n bgtz-pc} {src : Fin 32} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-gzero : lookup (s .State.registers) src > 0) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Bgtz src bgtz-pc) →
    (prf-canStep : bgtz-pc < n) → 
    p , s —→ [[ bgtz-pc , s .State.registers , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , buildTrace s (Bgtz src bgtz-pc)

  step-Call-Unt : ∀ {n jmp-pc} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) →                 
    (prf-jmp-pc : jmp-pc < n) → 
    (prf-mode : s .State.mode ≡ true) →
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Call-Unt jmp-pc) →
    (prf-canStep : s .State.pc < n ∸ 1) →
    p , s —→ [[ jmp-pc , s .State.registers , false , s .State.UR , s .State.registers , suc (s .State.pc) ]]
           , buildTrace s Call-Unt-Sentry 

  step-Ret-Unt : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) →
    (prf-canStep : s .State.ret-pc ≤ n) →
    (prf-mode : s .State.mode ≡ false) →
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Return-Unt) →
    p , s —→ [[ s .State.ret-pc , s .State.SR , true , s .State.UR , s .State.SR , s .State.ret-pc ]]
           , ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩

  step-Return : ∀ {n} → (p : Program n) → (s : State) →                         
    (prf-cur : s .State.pc < n) → 
    (prf-cmd : lookup (p .Program.instructions) (fromℕ< prf-cur) ≡ Return) →
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
            then ⟨ Load-UR-Sentry dest (s .State.UR) , 0 ∷ 0 ∷ 0 ∷ [] ⟩
            else ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩
         
        h = [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]]
            
    -- in p , s —→ [[ (suc (s .State.pc)) , r , s .State.mode , s .State.UR , s .State.SR , s .State.ret-pc ]] , t
   in p , s —→ h , t


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
    p , s —→* s , ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩ ✓
    
  step : ∀ {n} → (p : Program n) (s s₁ s₂ : State) (t₁ t₂ : Trace)
    → p , s₁ —→* s₂ , t₂ ✓
    → p , s —→ s₁ , t₁
    → p , s —→* s₂ , t₂ ✓

trace-deterministic : ∀ {n} (p : Program n) (s : State) (s₁ s₂ : State) (t₁ t₂ : Trace) →
                      p , s —→ s₁ , t₁ →
                      p , s —→ s₂ , t₂ →
                      t₁ ≡ t₂
≤-≡-trans : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤-≡-trans x refl = x

trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp {n} p s pc cmd) (step-NoOp {.n} .p .s pc1 cmd1) = refl
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Add {n} {dest} {r1} {r2} p s pc a cmd) (step-Add {.n} {dest_} {r1_} {r2_}  .p .s pc1 a1 cmd1) with trans (sym a) a1
... | refl = refl

trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Add .p .s prf-cur₁ prf-cmd₁ prf-canStep) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Sub .p .s prf-cur₁ prf-cmd₁ prf-canStep) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Addi .p .s prf-cur₁ prf-cmd₁ prf-canStep) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Jump .p .s prf-cur₁ prf-canStep prf-cmd₁) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Bgtz-l .p .s prf-cur₁ prf-zero prf-cmd₁ prf-canStep) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Bgtz-g .p .s prf-cur₁ prf-gzero prf-cmd₁ prf-canStep) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Call-Unt .p .s prf-cur₁ prf-jmp-pc prf-mode prf-cmd₁ prf-canStep) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Ret-Unt .p .s prf-cur₁ prf-canStep prf-mode prf-cmd₁) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Return .p .s prf-cur₁ prf-cmd₁) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Alert .p .s prf-cur₁ prf-cmd₁) = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-NoOp .p .s prf-cur prf-cmd) (step-Load-UR .p .s prf-cur₁ prf-cmd₁ prf-canStep) = {!   !}




trace-deterministic p s s₁ s₂ t₁ t₂ (step-Add .p .s prf-cur prf-cmd prf-canStep) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Sub .p .s prf-cur prf-cmd prf-canStep) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Addi .p .s prf-cur prf-cmd prf-canStep) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Jump .p .s prf-cur prf-canStep prf-cmd) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Bgtz-l .p .s prf-cur prf-zero prf-cmd prf-canStep) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Bgtz-g .p .s prf-cur prf-gzero prf-cmd prf-canStep) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Call-Unt .p .s prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Ret-Unt .p .s prf-cur prf-canStep prf-mode prf-cmd) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Return .p .s prf-cur prf-cmd) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Alert .p .s prf-cur prf-cmd) step2 = {!   !}
trace-deterministic p s s₁ s₂ t₁ t₂ (step-Load-UR .p .s prf-cur prf-cmd prf-canStep) step2 = {!   !}
