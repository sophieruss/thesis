module agda.proofs.a-new-proof-unt-call where

open import agda.commands renaming (State to command-state)
open import agda.host-new
open import Data.Nat using (ℕ; _<_; _+_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; inspect)
open import Data.Vec.Base using (Vec; lookup; _∷_; [])
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
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
-- state mode-preserved for all instructions except call-unt, return-unt
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
------------------------------------------------------------------------
-- Switch to untrusted  -- only call-unt
go-untrusted : ∀ {n} (p : Program n) (s s' : State) (t : Trace) →
                (step : p , s —→ s' , t) →
                (s .State.mode ≡ true) →
                (s' .State.mode ≡ false) →
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

------------------------------------------------------------------------
-- Swtich to trusted -- only return-unt

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

-- main thm

prove that if the host takes multiple steps and ends in a true mode, then for every call-unt command, there must also have been a return-trusted
--  p , s —→* s′ , t′ ×
    p , s′ —→ [[ (s′ .State.ret-pc) , (s′ .State.SR) , true , (s′ .State.UR) , (s′ .State.SR) , (s′ .State.ret-pc) ]] , t × 
    (lookup (p .Program.instructions) (fromℕ< {s′ .State.pc} {n} (pc<n))) ≡ Return-Unt


EndsWithRet-Unt : ∀ {n} → Program n → State → Trace → Set
EndsWithRet-Unt {n} p s t = 
  ∃ λ s′ → 
  ∃ λ t′ → 
  ∃ λ (pc<n : s′ .State.pc < n) →
    p , s —→* s′ , t′ ×
    p , s′ —→ [[ (s′ .State.ret-pc) , (s′ .State.SR) , true , (s′ .State.UR) , (s′ .State.SR) , (s′ .State.ret-pc) ]] , t × 
    (lookup (p .Program.instructions) (fromℕ< {s′ .State.pc} {n} (pc<n))) ≡ Return-Unt



-- No instruction other than Ret-Unt can transition to trusted mode
-- mode-preserved : ∀ {n} {p : Program n} {s s′ : State} {t : Trace} →
--   Untrusted s →
--   p , s —→ s′ , t →
--   ∃ λ (pc<n : s .State.pc < n) →
-- --   except for return-unt there existsed a way to get to trused`
--   Untrusted s′


-- mode-preserved untrusted-s c = {!   !}
-- mode-preserved untrusted-s (step-NoOp _ _ prf-cur _ prf-trace) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Add _ _ prf-cur _ _) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Sub _ _ prf-cur _ _) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Addi _ _ prf-cur _ _) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Jump _ _ prf-cur _ _) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Bgtz-l _ _ prf-cur prf-zero _ _) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Bgtz-g _ _ prf-cur prf-gzero _ _) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Return _ _ prf-cur _ prf-trace) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Alert _ _ prf-cur _) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Load-UR _ _ prf-cur _ _) ¬ret-unt = untrusted-s
-- mode-preserved {n} {p} untrusted-s (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode _ _) ¬ret-unt = refl
-- mode-preserved {p = p} {s = s} untrusted-s (step-Ret-Unt _ _ _ pc≤ mode≡false _) ¬ret-unt = ⊥-elim (¬ret-unt (_ , _))


-- only-ret-unt-transitions-to-trusted : ∀ {n} (p : Program n) (s s′ : State) (t : Trace) →
--   Untrusted s →
--   p , s —→ s′ , t →
--   Trusted s′ →
--   ∃ λ _ → lookup (p .Program.instructions) (fromℕ< {s .State.pc} _) ≡ Return-Unt
-- only-ret-unt-transitions-to-trusted p s s′ t untrusted-s (step-Ret-Unt _ _ _ _ _ _) trusted-s′ = 
--   _ , _
-- only-ret-unt-transitions-to-trusted p s s′ t untrusted-s s→s′ trusted-s′ 
--   with lookup (p .Program.instructions) (fromℕ< {s .State.pc} _)
-- ... | Return-Unt = ?
-- ... | _ = ⊥-elim (contradiction trusted-s′ (mode-preserved untrusted-s s→s′ (λ where (r , ()))))

-- only-ret-unt-transitions-to-trusted : ∀ {n} (p : Program n) (s s′ : State) (t : Trace) →
--   Untrusted s →
--   p , s —→ s′ , t →
--   Trusted s′ →
--   ∃ λ r → lookup (p .Program.instructions) (fromℕ< {s .State.pc} _) ≡ Return-Unt

-- only-ret-unt-transitions-to-trusted p s s′ t untrusted-s s→s′ trusted-s′ 
--   with lookup (p .Program.instructions) (fromℕ< {s .State.pc} _) in eq
-- ... | Return-Unt = {!   !}
-- ... | other-instr = {!   !}
--   ⊥-elim (contradiction trusted-s′ (mode-preserved untrusted-s s→s′ (λ where ( ()))))

  