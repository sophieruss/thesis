module agda.proofs.a-new-proof-unt-call where

open import agda.commands renaming (State to command-state)
open import agda.host-new
open import Data.Nat using (ℕ; _<_; _+_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; inspect)
open import Data.Vec.Base using (Vec; lookup; _∷_; [])
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)

-- State predicates
Trusted : State → Set
Trusted s = s .State.mode ≡ true

Untrusted : State → Set
Untrusted s = s .State.mode ≡ false

EndsWithRet-Unt : ∀ {n} → Program n → State → Trace → Set
EndsWithRet-Unt {n} p s t = 
  ∃ λ s′ → 
  ∃ λ t′ → 
  ∃ λ (pc<n : s′ .State.pc < n) →
    p , s —→* s′ , t′ ×
    p , s′ —→ [[ (s′ .State.ret-pc) , (s′ .State.SR) , true , (s′ .State.UR) , (s′ .State.SR) , (s′ .State.ret-pc) ]] , t × 
    (lookup (p .Program.instructions) (fromℕ< {s′ .State.pc} {n} (pc<n))) ≡ Return-Unt

------------------------------------------------------------------------
-- Helper Lemmas
------------------------------------------------------------------------

-- No instruction other than Ret-Unt can transition to trusted mode
mode-preserved : ∀ {n} {p : Program n} {s s′ : State} {t : Trace} →
  Untrusted s →
  p , s —→ s′ , t →
  ∃ λ (pc<n : s .State.pc < n) →
--   except for return-unt there existsed a way to get to trused`
  Untrusted s′


mode-preserved untrusted-s c = {!   !}
-- mode-preserved untrusted-s (step-NoOp _ _ prf-cur prf-cmd prf-trace) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Add _ _ prf-cur prf-cmd prf-canStep) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Sub _ _ prf-cur prf-cmd prf-canStep) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Addi _ _ prf-cur prf-cmd prf-canStep) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Jump _ _ prf-cur prf-canStep prf-cmd) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Bgtz-l _ _ prf-cur prf-zero prf-cmd prf-canStep) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Bgtz-g _ _ prf-cur prf-gzero prf-cmd prf-canStep) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Return _ _ prf-cur prf-cmd prf-trace) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Alert _ _ prf-cur prf-cmd) ¬ret-unt = untrusted-s
-- mode-preserved untrusted-s (step-Load-UR _ _ prf-cur prf-cmd prf-canStep) ¬ret-unt = untrusted-s
-- mode-preserved {n} {p} untrusted-s (step-Call-Unt _ _ prf-cur prf-jmp-pc prf-mode prf-cmd prf-canStep) ¬ret-unt = refl
-- mode-preserved {p = p} {s = s} untrusted-s (step-Ret-Unt _ _ _ pc≤ mode≡false prf-cmd) ¬ret-unt = ⊥-elim (¬ret-unt (_ , prf-cmd))

-- only-ret-unt-transitions-to-trusted : ∀ {n} (p : Program n) (s s′ : State) (t : Trace) →
--   Untrusted s →
--   p , s —→ s′ , t →
--   Trusted s′ →
--   ∃ λ _ → lookup (p .Program.instructions) (fromℕ< {s .State.pc} _) ≡ Return-Unt
-- only-ret-unt-transitions-to-trusted p s s′ t untrusted-s (step-Ret-Unt _ _ _ _ _ prf-cmd) trusted-s′ = 
--   _ , prf-cmd
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

