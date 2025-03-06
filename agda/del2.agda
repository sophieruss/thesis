open import Data.Nat using (ℕ;  _≤_)
open import Agda.Builtin.Bool
open import Data.Bool.Base using (if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


bgtzHelper : ℕ → ℕ → ℕ → ℕ
-- bgtzHelper src_val n pc with (src_val ≤ 0)
-- ... | true  = n
-- ... | false = pc 


-- bgtzHelper : ℕ → ℕ → ℕ → ℕ
-- bgtzHelper src_val n pc =
bgtzHelper src_val n pc with src_val
... | 0  = n
... | _ = pc 
  -- let b = (src_val ≡ 0)
  -- in if {!   !} then n else suc pc
  -- if src_val > 0 then n else pc + 1
    -- if src_val > 0 return n
    -- else return pc + 1


-- open import Data.List.Base using (List)
-- open import Data.List.Base renaming (lookup to listlookup; updateAt to listupdateAt; length to listlength; _∷_ to _∻_; [] to ⟨⟩)
-- open import Data.Maybe using (Maybe; just; nothing)

open import Data.List.Base using (List)
open import Data.List.Base renaming (lookup to listlookup; updateAt to listupdateAt; length to listlength; _∷_ to _∻_; [] to ⟨⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)


-- Define a list of natural numbers
a : List ℕ
a = 1 ∻ 2 ∻ 3 ∻ ⟨⟩

-- prf: n < length a
sophiel : Fin (listlength a)
sophiel = # 2

zzz = listlookup a sophiel

-- Use `Fin` to index the list
-- index0 : Fin (listlength a)
-- index0 = Fin.zero 


-- index1 : Fin (listlength a)
-- index1 = Fin.suc Fin.zero

-- -- Look up the element at index 1 in the list using `Fin`
-- z : Maybe ℕ
-- z = just ℕ.zero --listlookup a index1  -- This should return Just 2

-- -- Look up the element at index 4 (out-of-bounds) using `Fin`
-- -- This won't work since the list only has 3 elements (valid indices are 0, 1, 2)
-- zOutOfBounds : Maybe ℕ
-- zOutOfBounds = just (ℕ.suc ℕ.zero) --listlookup a (toℕ 4)  -- This will return `Nothing` as index 4 is out of bounds


-- mychecka = z ≡ 1
-- mycheck = ?