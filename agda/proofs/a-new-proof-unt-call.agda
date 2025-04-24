module agda.proofs.a-new-proof-unt-call where

open import agda.commands renaming (State to command-state)
open import agda.host-new
open import Data.Nat using (ℕ; _<_; _+_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; inspect)
open import Data.Vec.Base using (Vec; lookup; _∷_; [])
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)

-- state predicates
Trusted : State → Set
Trusted s = s .State.mode ≡ true

Untrusted : State → Set
Untrusted s = s .State.mode ≡ false

------------------------------------------------------------------------
-- helper lemmas         -- call-unt just change UR,  ->just change mode
------------------------------------------------------------------------
-- STATE MODE PRESERVED 
-- <goal: mode preserved for all instructions except call-unt, return-unt>

step-prf : ∀ {n} {p : Program n} {s s' t} → p , s —→ s' , t → s .State.pc < n
step-prf (step-NoOp _ _ prf-cur _ prf-trace) = prf-cur
step-prf (step-Add _ _ prf-cur _ _) = prf-cur
step-prf (step-Sub _ _ prf-cur _ _) = prf-cur
step-prf (step-Addi _ _ prf-cur _ _) = prf-cur
step-prf (step-Jump _ _ prf-cur _ _) = prf-cur
step-prf (step-Bgtz-l _ _ prf-cur _ _ _) = prf-cur
step-prf (step-Bgtz-g _ _ prf-cur _ _ _) = prf-cur
step-prf (step-Call-Unt _ _ prf-cur _ _ _ _) = prf-cur
step-prf (step-Ret-Unt _ _ prf-cur _ _ _) = prf-cur
step-prf (step-Return _ _ prf-cur _) = prf-cur
step-prf (step-Alert _ _ prf-cur _) = prf-cur
step-prf (step-Load-UR _ _ prf-cur _ _) = prf-cur
step-prf (step-Put-UR _ _ prf-cur _ _ _) = prf-cur


mode-preserved : ∀ {n} (p : Program n) (s s' : State) (t : Trace) →
                 (step : p , s —→ s' , t) →
                 (¬call : ∀ {jmp-pc} → lookup (p .Program.instructions) (fromℕ< (step-prf step)) ≢ Call-Unt jmp-pc) →
                 (¬ret : lookup (p .Program.instructions) (fromℕ< (step-prf step)) ≢ Return-Unt) →
                 s .State.mode ≡ s' .State.mode

mode-preserved p s s' t (step-NoOp _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Add _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Sub _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Addi _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Jump _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Bgtz-l _ _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Bgtz-g _ _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Call-Unt _ _ _ _ mode cmd _) ¬call ¬ret = ⊥-elim (¬call cmd)
mode-preserved p s s' t (step-Ret-Unt _ _ _ _ mode cmd) ¬call ¬ret =  ⊥-elim (¬ret cmd)
mode-preserved p s s' t (step-Return _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Alert _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Load-UR _ _ _ _ _) _ _ = refl
mode-preserved p s s' t (step-Put-UR _ _ _ _ mode _) _ _ = mode

-- sum lemma: While in untrusted mode, any step that's not Return-Unt preserves untrusted mode
unt-preserved : ∀ {n} {s s' : State} {t : Trace} (p : Program n) →
                 (s .State.mode ≡ false) →
                 (step : p , s —→ s' , t) →
                 (lookup (p .Program.instructions) (fromℕ< (step-prf step)) ≢ Return-Unt) →
                 (s' .State.mode ≡ false)

unt-preserved p s-false (step-NoOp .p _ prf-cur prf-cmd prf-trace) ¬ret = s-false
unt-preserved p s-false (step-Add .p _ prf-cur prf-cmd prf-canStep) ¬ret = s-false
unt-preserved p s-false (step-Sub .p _ prf-cur prf-cmd prf-canStep) ¬ret = s-false
unt-preserved p s-false (step-Addi .p _ prf-cur prf-cmd prf-canStep) ¬ret = s-false
unt-preserved p s-false (step-Jump .p _ prf-cur prf-canStep prf-cmd) ¬ret = s-false
unt-preserved p s-false (step-Bgtz-l .p _ prf-cur prf-zero prf-cmd prf-canStep) ¬ret = s-false
unt-preserved p s-false (step-Bgtz-g .p _ prf-cur prf-gzero prf-cmd prf-canStep) ¬ret = s-false
unt-preserved p s-false (step-Call-Unt .p _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) ¬ret = refl
unt-preserved p s-false (step-Ret-Unt .p _ prf-cur prf-canStep prf-mode prf-cmd) ¬ret = ⊥-elim (¬ret prf-cmd)
unt-preserved p s-false (step-Return .p _ prf-cur prf-cmd) ¬ret = s-false
unt-preserved p s-false (step-Alert .p _ prf-cur prf-cmd) ¬ret = s-false
unt-preserved p s-false (step-Load-UR .p _ prf-cur prf-cmd prf-canStep) ¬ret = s-false
unt-preserved p s-false (step-Put-UR .p _ prf-cur prf-cmd prf-mode prf-canStep) ¬ret = refl



------------------------------------------------------------------------
-- SWITCH TO UNTRUSTED
-- <goal: only call-unt can switch host mode to untrusted>

go-untrusted : ∀ {n} (p : Program n) (s s' : State) (t : Trace) →
                (step : p , s —→ s' , t) →
                (s .State.mode ≡ true) →
                (s' .State.mode ≡ false) →
                -- (Trusted s) →
                -- (Untrusted s') →
                ∃[ jmp-pc ] (lookup (p .Program.instructions) (fromℕ< (step-prf step)) ≡ Call-Unt jmp-pc)
      
go-untrusted p s s' t (step-Call-Unt {n} {jmp-pc} _ _ _ _ mode cmd _) mode-true mode-false = jmp-pc , cmd
go-untrusted p s s' t (step-Ret-Unt _ _ _ _ _ _) mode-true mode-false with () ← mode-false 
go-untrusted p s s' t (step-NoOp p s prf-cur prf-cmd prf-t) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Add _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Sub _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Addi _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Jump _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Bgtz-l _ _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Bgtz-g _ _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Return _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Alert _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Load-UR _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false)  
go-untrusted p s s' t (step-Put-UR _ _ _ _ mode _) mode-true mode-false with () ← (trans (sym mode-true) mode) 

------------------------------------------------------------------------
-- SWITCH TO TRUSTED
-- <goal: only return-unt can switch host mode to trusted>

go-trusted : ∀ {n} (p : Program n) (s s' : State) (t : Trace) →
                (step : p , s —→ s' , t) →
                (s .State.mode ≡ false) →
                (s' .State.mode ≡ true) →
                (lookup (p .Program.instructions) (fromℕ< (step-prf step)) ≡ Return-Unt )

go-trusted p s s' t (step-NoOp _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Add _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Sub _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Addi _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Jump _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Bgtz-l _ _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Bgtz-g _ _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Ret-Unt _ _ _ _ _ prf-cmd) mode-true mode-false = prf-cmd 
go-trusted p s s' t (step-Return _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Alert _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 
go-trusted p s s' t (step-Load-UR _ _ _ _ _) mode-true mode-false with () ← (trans (sym mode-true) mode-false) 

------------------------------------------------------------------------
------------------------------------------------------------------------

-- MAIN THM       
-- <goal: um not sure>

------------------- version I
-- if       program has a final return 
-- then if  there is a call-untrusted, 
-- then     there must be a return-untrusted

-- given the wording, is there an issue of multiple untrusted calls 
-- (e.g. would this prove an instance of ret-untrusted exists, 
--       but now issue of there needing to be same amt of call-untrusted and return-untrusted)
-- Issue is scope is entire program
-- Instead do I need to narrow scope te be a small part of program?

------------------- version II -------------------

-- if       if a program takes the following two successive steps
--              a) small-step going into untrusted mode (call-unt)
--              b) big-step in untrusted mode (induction?)
-- then if  the program ends in trusted mode
-- then     the program must take a small step going into trusted (return-unt) immediately after the big step

-- step-over-untrusted : ∀ {n jmp-pc} (p : Program n) (s s' s'' s''' : State) (t' t'' t''' : Trace) →
--                   (s .State.mode ≡ true) →
--                   (s''' .State.mode ≡ true) →
--                   (go-unt : p , s —→ s' , t') →
--                   (lookup (p .Program.instructions) (fromℕ< (step-prf go-unt)) ≡ Call-Unt jmp-pc) →                  
--                   (bigstep : p , s' —→* s'' , t'') →
--                   (after-bigstep : p , s'' —→ s''' , t''') →
--                   (lookup (p .Program.instructions) (fromℕ< (step-prf after-bigstep)) ≡ Return-Unt)

-- step-over-untrusted p s s' s'' s''' t' t'' t''' refl refl step-a instr-unt step-big step-b = {! !}




------------------- version III -------------------

-- if       a program takes small-step into untrusted mode (call-unt step)
-- thenfi   the program is in trusted mode at some point after
-- then

--  There exists some intermediate state s₂ where we return from untrusted modthe program must have taken a big step in untrusted mode, immediately followed by a small step back to trusted

-- v3 : ∀ {n jmp-pc} (p : Program n) (s s₁ s₃ : State) (t₁ t₃ : Trace) →
--                   (s .State.mode ≡ true) →
--                   (s₁ .State.mode ≡ false) →
--                 --   (s₂ .State.mode ≡ false) →
--                   (s₃ .State.mode ≡ true) →

--                   (step-call-unt : p , s —→ s₁ , t₁) →
--                   (lookup (p .Program.instructions) (fromℕ< (step-prf step-call-unt)) ≡ Call-Unt jmp-pc) →
                  

--                    ∃[ s₂ ] ∃[ t₂ ] 
--                     (step-b : p , s₁ —→* s₂ , t₂) ×
--                     (step-c : p , s₂ —→ s₃ , t₃) ×
--                     (lookup (p .Program.instructions) (fromℕ< (step-prf step-c)) ≡ Return-Unt) ×
--                     (∀ s' t' → (p , s₁ —→* s' , t') → (p , s' —→* s₂ , t₂) → s' .State.mode ≡ false)
                  
--                 --   (step-ret-unt : p , s₂ —→ s₃ , t₃) →
--                 --   (lookup (p .Program.instructions) (fromℕ< (step-prf step-ret-unt)) ≡ Return-Unt) →

--                 --   p , s₂ —→* s₃ , t₃
--                   -- how do I enforce that this big-step doesn't include another return-unt/call-unt/return-unt
--                   -- maybe its ok if it does. because induction. but i dont really do induction.
--                   -- should this somehow be a there exists

-- v3 {n} {jmp-pc} p s s₁ s₂ s₃ t₁ t₂ t₃ refl refl refl refl step1 type1 step2 type2 = {!   !}



------------------- version IV -------------------

-- if           a program takes small-step into untrusted mode (call-unt step)
-- thenif       a program is later in trusted mode
-- then         the program must have taken a return-unt step

-- Theorem: If we enter untrusted mode via Call-Unt and later reach trusted mode in one step,
--          then that step must be Return-Unt
v4 : ∀ {n} {s s₁ s₂ : State} {t₁ t₂ : Trace} (p : Program n)  →
          -- Initial step: enter untrusted mode via Call-Unt
          (call-step : p , s —→ s₁ , t₁) →
          (s .State.mode ≡ true) →
          (s₁ .State.mode ≡ false) →
          (∃[ jmp-pc ] lookup (p .Program.instructions) (fromℕ< (step-prf call-step)) ≡ Call-Unt jmp-pc) →
          
          -- Next step: reach trusted mode again
          (next-step : p , s₁ —→ s₂ , t₂) →
          (s₂ .State.mode ≡ true) →
          
          -- Then this next step must be Return-Unt
          lookup (p .Program.instructions) (fromℕ< (step-prf next-step)) ≡ Return-Unt

v4 {n} {s} {s₁} {s₂} {t₁} {t₂} p 
    (step-Call-Unt p [[ _ , _ , true , _ , _ , _ ]] prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) 
    s-true s₁-false (jmp-pc , call-instr) 
    (step-Ret-Unt .p .([[ suc _ , _ , false , _ , _ , suc _ ]]) prf-cur₁ prf-canStep₁ prf-mode₁ prf-cmd₁)
    s₂-true 
    = prf-cmd₁


------------------- version V -------------------

-- if           a program takes small-step into untrusted mode (call-unt step)
-- thenif       a program is later in trusted mode
-- then         the program must have taken a return-unt step

-- Based on v4 proof, we know that if it starts in steps into trusted, ends in trusted, it must have taken a return-unt step
-- now I want to build on this and say there exists a way for while its in untrusted, it can take an arbitraty step that is not return-unt, and remaing in untrusted which we know when i proved mode preserved


v5 : ∀ {n} {s s₁ s₂ : State} {t₁ t₂ : Trace} (p : Program n) →
     -- Initial step: enter untrusted mode via Call-Unt
     (call-step : p , s —→ s₁ , t₁) →
     (s .State.mode ≡ true) →
     (s₁ .State.mode ≡ false) →
     (∃[ jmp-pc ] lookup (p .Program.instructions) (fromℕ< (step-prf call-step)) ≡ Call-Unt jmp-pc) →
     
     -- Later step: reach trusted mode again
     (later-step : p , s₁ —→ s₂ , t₂) →
     (s₂ .State.mode ≡ true) →
     (lookup (p .Program.instructions) (fromℕ< (step-prf later-step)) ≡ Return-Unt) →
     -- all of above is v4 
     
     -- Then there exists some state s' where:
     -- 1. There's a sequence of steps from s₁ to s' where mode remains false
     -- 2. The final step from s' to s₂ is Return-Unt
    --  ∃[ sⱼ ] ∃[ tⱼ ] (p , s₁  *—→ sⱼ , tⱼ × 
    --                   (∀ {sₖ tₖ} → (p , s₁  *—→ sₖ , tₖ) → (p , sₖ —→ s₂ , t₂) → 
    --                   (sₖ .State.mode ≡ false)))
    (∀ {sₖ tₖ} → 
    (sₖ .State.mode ≡ false) →          -- all steps stay untrusted
    (big : p , s₁  *—→ sₖ , tₖ) →       -- steps in untrusted
    (p , sₖ —→ s₂ , t₂))
    -- (lookup (p .Program.instructions) (fromℕ< (step-prf step)) ≡ Return-Unt) →
    -- (sₖ .State.mode ≡ false))
  
-- v5 {n} {s} {s₁} {s₂} {t₁} {t₂} p 
--     (step-Call-Unt p [[ _ , _ , true , _ , _ , _ ]] prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) 
--         s-true s₁-false (jmp-pc , call-instr) 
--         (step-Ret-Unt .p .([[ suc _ , _ , false , _ , _ , suc _ ]]) prf-cur₁ prf-canStep₁ prf-mode₁ prf-cmd₁) 
--         s₂-true prf-cmd₂ {[[ _ , _ , false , _ , _ , _ ]]} {tₖ} sₖ-false big

v5 {n} {s} {s₁} {s₂} {t₁} {t₂} p 
    (step-Call-Unt p [[ _ , _ , true , _ , _ , _ ]] prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) 
    s-true s₁-false (jmp-pc , call-instr) 
    (step-Ret-Unt .p .([[ suc _ , _ , false , _ , _ , suc _ ]]) prf-cur₁ prf-canStep₁ prf-mode₁ prf-cmd₁) 
    s₂-true prf-cmd₂ {[[ _ , _ , false , _ , _ , _ ]]} {tₖ} sₖ-false 
    (done .p .([[ suc _ , _ , false , _ , _ , suc _ ]]) .tₖ) 
    = 
    step-Ret-Unt _ _ prf-cur₁ prf-canStep₁ refl prf-cmd₁
    
v5 {n} {s} {s₁} {s₂} {t₁} {t₂} p 
    (step-Call-Unt p [[ _ , _ , true , _ , _ , _ ]] prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) 
    s-true s₁-false (jmp-pc , call-instr) 
    (step-Ret-Unt .p .([[ suc _ , _ , false , _ , _ , suc _ ]]) prf-cur₁ prf-canStep₁ prf-mode₁ prf-cmd₁) 
    s₂-true prf-cmd₂ {[[ _ , _ , false , _ , _ , _ ]]} {tₖ} sₖ-false 
    (step—→ .p .([[ suc _ , _ , false , _ , _ , suc _ ]]) s₃ aa t₃ .tₖ x big) 
    = 
    {!   !}
  