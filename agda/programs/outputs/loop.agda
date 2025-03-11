module Agda.programs.outputs.loop2 where
open import agda.commands
open import agda.host
open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Agda.Builtin.List
prog : Program 20
prog = program (NoOp ∷ Addi (# 4) (# 0) 25 ∷ Addi (# 1) (# 0) 5 ∷ Add (# 0) (# 0) (# 1) ∷ Sub (# 2) (# 4) (# 0) ∷ Bgtz (# 2) 3 ∷ Add (# 0) (# 0) (# 1) ∷ Sub (# 2) (# 4) (# 0) ∷ Bgtz (# 2) 3 ∷ Add (# 0) (# 0) (# 1) ∷ Sub (# 2) (# 4) (# 0) ∷ Bgtz (# 2) 3 ∷ Add (# 0) (# 0) (# 1) ∷ Sub (# 2) (# 4) (# 0) ∷ Bgtz (# 2) 3 ∷ Add (# 0) (# 0) (# 1) ∷ Sub (# 2) (# 4) (# 0) ∷ Bgtz (# 2) 3 ∷ Addi (# 10) (# 10) 10 ∷ NoOp ∷ [])
r-0 r-1 r-2 r-3 r-4 r-5 r-6 r-7 r-8 r-9 r-10 r-11 r-12 r-13 r-14 r-15 r-16 r-17 r-18 r-19  : Vec ℕ 32
r-0 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-1 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-2 = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-3 = 0 ∷ 5 ∷ 0 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-4 = 5 ∷ 5 ∷ 0 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-5 = 5 ∷ 5 ∷ 20 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-6 = 5 ∷ 5 ∷ 20 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-7 = 10 ∷ 5 ∷ 20 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-8 = 10 ∷ 5 ∷ 15 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-9 = 10 ∷ 5 ∷ 15 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-10 = 15 ∷ 5 ∷ 15 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-11 = 15 ∷ 5 ∷ 10 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-12 = 15 ∷ 5 ∷ 10 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-13 = 20 ∷ 5 ∷ 10 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-14 = 20 ∷ 5 ∷ 5 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-15 = 20 ∷ 5 ∷ 5 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-16 = 25 ∷ 5 ∷ 5 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-17 = 25 ∷ 5 ∷ 0 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-18 = 25 ∷ 5 ∷ 0 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
r-19 = 25 ∷ 5 ∷ 0 ∷ 0 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 10 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
state-0 = [ 0 , r-0 ] 
state-1 = [ 1 , r-1 ] 
state-2 = [ 2 , r-2 ] 
state-3 = [ 3 , r-3 ] 
state-4 = [ 4 , r-4 ] 
state-5 = [ 5 , r-5 ] 
state-6 = [ 3 , r-6 ] 
state-7 = [ 4 , r-7 ] 
state-8 = [ 5 , r-8 ] 
state-9 = [ 3 , r-9 ] 
state-10 = [ 4 , r-10 ] 
state-11 = [ 5 , r-11 ] 
state-12 = [ 3 , r-12 ] 
state-13 = [ 4 , r-13 ] 
state-14 = [ 5 , r-14 ] 
state-15 = [ 3 , r-15 ] 
state-16 = [ 4 , r-16 ] 
state-17 = [ 5 , r-17 ] 
state-18 = [ 6 , r-18 ] 
state-19 = [ 7 , r-19 ] 
τ-0 τ-1 τ-2 τ-3 τ-4 τ-5 τ-6 τ-7 τ-8 τ-9 τ-10 τ-11 τ-12 τ-13 τ-14 τ-15 τ-16 τ-17 τ-18 τ-19  : Trace
τ-0 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 
τ-1 = ⟨ Addi (# 4) (# 0) 25 , 0 ∷ 25 ∷ 0 ∷ [] ⟩ 
τ-2 = ⟨ Addi (# 1) (# 0) 5 , 0 ∷ 5 ∷ 0 ∷ [] ⟩ 
τ-3 = ⟨ Add (# 0) (# 0) (# 1) , 0 ∷ 5 ∷ 5 ∷ [] ⟩ 
τ-4 = ⟨ Sub (# 2) (# 4) (# 0) , 25 ∷ 5 ∷ 20 ∷ [] ⟩ 
τ-5 = ⟨ Bgtz (# 2) 3 , 20 ∷ 3 ∷ 0 ∷ [] ⟩ 
τ-6 = ⟨ Add (# 0) (# 0) (# 1) , 5 ∷ 5 ∷ 10 ∷ [] ⟩ 
τ-7 = ⟨ Sub (# 2) (# 4) (# 0) , 25 ∷ 10 ∷ 15 ∷ [] ⟩ 
τ-8 = ⟨ Bgtz (# 2) 3 , 15 ∷ 3 ∷ 0 ∷ [] ⟩ 
τ-9 = ⟨ Add (# 0) (# 0) (# 1) , 10 ∷ 5 ∷ 15 ∷ [] ⟩ 
τ-10 = ⟨ Sub (# 2) (# 4) (# 0) , 25 ∷ 15 ∷ 10 ∷ [] ⟩ 
τ-11 = ⟨ Bgtz (# 2) 3 , 10 ∷ 3 ∷ 0 ∷ [] ⟩ 
τ-12 = ⟨ Add (# 0) (# 0) (# 1) , 15 ∷ 5 ∷ 20 ∷ [] ⟩ 
τ-13 = ⟨ Sub (# 2) (# 4) (# 0) , 25 ∷ 20 ∷ 5 ∷ [] ⟩ 
τ-14 = ⟨ Bgtz (# 2) 3 , 5 ∷ 3 ∷ 0 ∷ [] ⟩ 
τ-15 = ⟨ Add (# 0) (# 0) (# 1) , 20 ∷ 5 ∷ 25 ∷ [] ⟩ 
τ-16 = ⟨ Sub (# 2) (# 4) (# 0) , 25 ∷ 25 ∷ 0 ∷ [] ⟩ 
τ-17 = ⟨ Bgtz (# 2) 3 , 0 ∷ 6 ∷ 0 ∷ [] ⟩ 
τ-18 = ⟨ Addi (# 10) (# 10) 10 , 0 ∷ 10 ∷ 0 ∷ [] ⟩ 
τ-19 = ⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩ 
0→1 : prog , state-0 —→ state-1 , τ-0
0→1 = step-NoOp prog state-0 (s≤s z≤n) refl
1→2 : prog , state-1 —→ state-2 , τ-1
1→2 = step-Addi prog state-1 (s≤s (s≤s z≤n)) refl
2→3 : prog , state-2 —→ state-3 , τ-2
2→3 = step-Addi prog state-2 (s≤s (s≤s (s≤s z≤n))) refl
3→4 : prog , state-3 —→ state-4 , τ-3
3→4 = step-Add prog state-3 (s≤s (s≤s (s≤s (s≤s z≤n)))) refl
4→5 : prog , state-4 —→ state-5 , τ-4
4→5 = step-Sub prog state-4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) refl
5→6 : prog , state-5 —→ state-6 , τ-5
5→6 = step-Bgtz-g prog state-5 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl
6→7 : prog , state-6 —→ state-7 , τ-6
6→7 = step-Add prog state-6 (s≤s (s≤s (s≤s (s≤s z≤n)))) refl
7→8 : prog , state-7 —→ state-8 , τ-7
7→8 = step-Sub prog state-7 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) refl
8→9 : prog , state-8 —→ state-9 , τ-8
8→9 = step-Bgtz-g prog state-8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl
9→10 : prog , state-9 —→ state-10 , τ-9
9→10 = step-Add prog state-9 (s≤s (s≤s (s≤s (s≤s z≤n)))) refl
10→11 : prog , state-10 —→ state-11 , τ-10
10→11 = step-Sub prog state-10 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) refl
11→12 : prog , state-11 —→ state-12 , τ-11
11→12 = step-Bgtz-g prog state-11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl
12→13 : prog , state-12 —→ state-13 , τ-12
12→13 = step-Add prog state-12 (s≤s (s≤s (s≤s (s≤s z≤n)))) refl
13→14 : prog , state-13 —→ state-14 , τ-13
13→14 = step-Sub prog state-13 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) refl
14→15 : prog , state-14 —→ state-15 , τ-14
14→15 = step-Bgtz-g prog state-14 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s z≤n) refl
15→16 : prog , state-15 —→ state-16 , τ-15
15→16 = step-Add prog state-15 (s≤s (s≤s (s≤s (s≤s z≤n)))) refl
16→17 : prog , state-16 —→ state-17 , τ-16
16→17 = step-Sub prog state-16 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) refl
17→18 : prog , state-17 —→ state-18 , τ-17
17→18 = step-Bgtz-l prog state-17 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (s≤s (s≤s (s≤s (s≤s z≤n)))) refl refl
-- 18→19 : prog , state-18 —→ state-19 , τ-18
-- 18→19 = step-Addi prog state-18 ? refl
