module Agda.archive.programs.outputs.untrusted where
open import agda.commands
open import agda.host  renaming (State to Hstate)
open import agda.sentry
open import Data.Nat using (ℕ; compare; _≤_; _≥_;  _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; _≥?_)
open import Function.Base using (flip)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.List

proj : Hstate → State
proj [[ pc , registers , mode , UR , SR , ret-pc ]] = [ pc , registers ]
prog : Program 12
prog = program (NoOp ∷ Addi (# 1) (# 0) 4 ∷ Call-Unt 9 ∷ Load-UR (# 2) ∷ Add (# 3) (# 2) (# 2) ∷ Sub (# 5) (# 3) (# 1) ∷ Bgtz (# 5) 8 ∷ Alert ∷ Return ∷ Addi (# 10) (# 0) 2 ∷ Put-UR (# 10) ∷ Return-Unt ∷ [])
r-0 r-1 r-2 r-3 r-4 r-5 r-6 r-7 r-8 r-9 r-10 r-11  : Vec ℕ 32
r-0 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-1 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-2 = 0 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-3 = 0 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-4 = 0 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-5 = 0 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-6 = 0 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-7 = 0 ∷ 4 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-8 = 0 ∷ 4 ∷ 2 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-9 = 0 ∷ 4 ∷ 2 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-10 = 0 ∷ 4 ∷ 2 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-11 = 0 ∷ 4 ∷ 2 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
state-0 = [[ 0 , r-0 , true , 0 , r-0 , 0 ]]
state-1 = [[ 1 , r-1 , true , 0 , r-0 , 0 ]]
state-2 = [[ 2 , r-2 , true , 0 , r-0 , 0 ]]
state-3 = [[ 9 , r-3 , false , 0 , r-1 , 3 ]]
state-4 = [[ 10 , r-4 , false , 0 , r-1 , 3 ]]
state-5 = [[ 11 , r-5 , false , 2 , r-1 , 3 ]]
state-6 = [[ 3 , r-6 , true , 2 , r-1 , 3 ]]
-- state-6 = [[ state-5 .Hstate.ret-pc , state-5 .Hstate.SR , true , state-5 .Hstate.UR , state-5 .Hstate.SR , state-5 .Hstate.ret-pc ]]

state-7 = [[ 4 , r-7 , true , 2 , r-1 , 3 ]]
state-8 = [[ 5 , r-8 , true , 2 , r-1 , 3 ]]
state-9 = [[ 6 , r-9 , true , 2 , r-1 , 3 ]]
state-10 = [[ 7 , r-10 , true , 2 , r-1 , 3 ]]
state-11 = [[ 8 , r-11 , true , 2 , r-1 , 3 ]]
τ-0 τ-1 τ-2 τ-3 τ-4 τ-5 τ-6 τ-7 τ-8 τ-9 τ-10 τ-11  : Trace
τ-0 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 
τ-1 = ⟨ Addi (# 1) (# 0) 4 , 0 ∷ 4 ∷ 0 ∷ [] ⟩ 
τ-2 = ⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 
τ-3 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩                         --addi
τ-4 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩                         --put-ut
τ-5 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩                         --return-unt
τ-6 = ⟨ Load-UR (# 2) , 2 ∷ 0 ∷ 0 ∷ [] ⟩ 
τ-7 = ⟨ Add (# 3) (# 2) (# 2) , 2 ∷ 2 ∷ 4 ∷ [] ⟩ 
τ-8 = ⟨ Sub (# 5) (# 3) (# 1) , 4 ∷ 4 ∷ 0 ∷ [] ⟩ 
τ-9 = ⟨ Bgtz (# 5) 8 , 0 ∷ 7 ∷ 0 ∷ [] ⟩ 
τ-10 = ⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 
τ-11 = ⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 
-- 0→1 : prog , state-0 —→ state-1 , τ-0
-- 0→1 = step-NoOp prog state-0 ? refl refl
1→2 : prog , state-1 —→ state-2 , τ-1
1→2 = step-Addi prog state-1 (s≤s (s≤s z≤n)) refl (s≤s (s≤s z≤n))

2→3 : prog , state-2 —→ state-3 , τ-2
2→3 = {!   !} --step-Call-Unt prog state-2
3→4 : prog , state-3 —→ state-4 , τ-3
3→4 = step-Addi prog state-3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))) refl ((s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))
4→5 : prog , state-4 —→ state-5 , τ-4
4→5 = {!  !} --step-Put-UR prog state-4 ? refl ? ? ?
5→6 : prog , state-5 —→ state-6 , τ-5
5→6 = {!   !} --step-Ret-Unt prog state-5 ? ? ? refl

6→7 : prog , state-6 —→ state-7 , τ-6
6→7 = step-Load-UR prog state-6 (s≤s (s≤s (s≤s (s≤s z≤n)))) refl (s≤s (s≤s (s≤s (s≤s z≤n))))
7→8 : prog , state-7 —→ state-8 , τ-7
7→8 = step-Add prog state-7 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) refl (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
8→9 : prog , state-8 —→ state-9 , τ-8
8→9 = step-Sub prog state-8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) refl (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
9→10 : prog , state-9 —→ state-10 , τ-9
9→10 = step-Bgtz-l prog state-9 ((s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) refl refl (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
-- 10→11 : prog , state-10 —→ state-11 , τ-10
-- 10→11 = step-Alert prog state-10 ? refl
 