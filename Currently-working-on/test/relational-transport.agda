open import Data.Nat
open import Data.Bool
open import Data.List

Bin = List Bool

n+ : ℕ → ℕ → ℕ → Set
bin+ : Bin → Bin → Bin → Set
bin+ = {!   !}

-- prove that + corresponds to bin+
--  prove that + is associative
-- prove that this implies that bin+ is associative.
-- prove any property of + applies to bin+

-- "any statement which relies on only zero, suc, and +,
--     if it is true of (ℕ, +), then it is true of (Bin, bin+)"


-- can I do this stuff in a relational style without univalence?

rel : ℕ → Bin → Set

rel+ : ∀{a b c a' b' c'} → n+ a b c → rel a a' → rel b b' → rel c c' → bin+ a' b' c'

transp : (P : (N : Set) → (R : N → N → N → Set) → Set)
  → P ℕ n+ → P Bin bin+
transp P p = {!   !}
-- parametricity free theorem from P ??????

-- evan WITH univalence, how would I do this???
