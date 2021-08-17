open import Data.Nat
open import Data.Unit
open import Data.Product

mutual
  data SemTzero : Set where
    Π : (A : SemTzero) → (Semzero A → SemTzero) → SemTzero
  Semzero : SemTzero → Set
  Semzero (Π A B) = (a : Semzero A) → Semzero (B a)

module sucn (SemTn : Set) (Semn : SemTn → Set) where
  mutual
    data SemTsucn : Set where
        U : SemTsucn
        Π : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        cumu : SemTn → SemTsucn

    Semsucn : SemTsucn → Set
    Semsucn U = SemTn
    Semsucn (Π A B) = (a : Semsucn A) → Semsucn (B a)
    Semsucn (cumu T) = Semn T

open sucn

mutual
  SemT : ℕ → Set
  SemT zero = SemTzero
  SemT (suc n) = sucn.SemTsucn (SemT n) (Sem n)

  Sem : (n : ℕ) → SemT n → Set
  Sem zero T = Semzero T
  Sem (suc n) T = sucn.Semsucn _ _ T

-- getElem : ∀{n} → (T : SemT n) → Sem n T
-- getElem {suc n} U = {!   !}
-- getElem {suc n} (Π T x) = {!   !}
-- getElem {suc n} (cumu x) = {!   !}
--
-- getElem1 : (T : SemT 1) → Sem 1 T
-- getElem1 U = {!   !}
-- getElem1 (Π A B) =
--     -- let a = getElem1 A in
--     λ a₁ → getElem1 (B a₁)
-- getElem1 (cumu T) = {! T  !}

{-

If set SemT 0 and Sem 0 to something else, then
SemT0 is the types in the context at level 0, and
Sem 0 is the terms of those types.

-}
