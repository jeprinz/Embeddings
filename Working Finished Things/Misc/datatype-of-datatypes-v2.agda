open import Agda.Primitive
open import Data.Unit
open import Data.Empty
open import Data.Bool

{-

Another instance of a datatype which encodes datatypes. This one is presented
slightly differently, but also captures some Inductive-Recursive datatypes.

-}

module datatype-of-datatypes-v2 where


module DataType (Param : Set)
  (dataArg : Set)
  (recIn : dataArg → Set)
  (recParam : (x : dataArg) → recIn x → Param)
  (outParam : dataArg → Param)
  (fRec : (x : dataArg) → (recIn x → Set) → Set)
  (mutRecParam : (x : dataArg) → (y : recIn x) → Param)
  where


  mutual
    data DataType : Param → Set where
      c : (x : dataArg)
        → (r : (y : recIn x) → DataType (recParam x y))
        → ((y : recIn x) → (z : f (r y)) → DataType (mutRecParam x y))
        → DataType (outParam x)

    f : {par : Param} → DataType par → Set
    f (c x r m) = fRec x (λ (y : recIn x) → f (r y))

open DataType

-- Example : Natural Numbers!
ℕ : Set
ℕ = DataType
  ⊤ -- Param
  Bool -- dataArg = number of constructors in this case
  (λ {true → ⊥ ; false → ⊤}) -- recIn - defines the two constructors. ⊥ is zero because it has no inputs, ⊤ is succ because it has one input.
  (λ _ _ → tt) -- recParam
  (λ _ → tt) -- outParam
  (λ _ _ → ⊥) -- fRec -- not using the Inductive-recursive-ness, so just return empty
  (λ _ _ → tt)
  tt

zero : ℕ
zero = c true ⊥-elim (λ y z → ⊥-elim y) -- TODO: should be able to put z instead of y, but agda can't simplify z.

succ : ℕ → ℕ
succ (c x r m) = c false (λ tt → (c x r m)) (λ tt z → ⊥-elim z)

double : ℕ → ℕ
double (c true r m) = zero
double (c false r m) = succ (succ (double (r tt)))
