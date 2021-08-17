open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Agda.Primitive
open import Function

{-

Another instance of a datatype which encodes datatypes. This one is presented
slightly differently, but also captures some Inductive-Recursive datatypes.

-}

module Core-Sem-with-datatypes where


module DataType (Param : Set)
  (dataArg : Set)
  (recIn : dataArg → Set)
  (recParam : (x : dataArg) → recIn x → Param)
  (outParam : dataArg → Param)
  (fOut : Set)
  (fInterp : fOut → Set)
  (fRec : (x : dataArg) → (recIn x → fOut) → fOut)
  (mutRecParam : (x : dataArg) → (y : recIn x) → Param)
  where


  mutual
    data DataType : Param → Set where
      c : (x : dataArg)
        → (r : (y : recIn x) → DataType (recParam x y))
        → ((y : recIn x) → (z : fInterp (f (r y))) → DataType (mutRecParam x y))
        → DataType (outParam x)

    f : {par : Param} → DataType par → fOut
    f (c x r m) = fRec x (λ (y : recIn x) → f (r y))

open DataType

data SemT0 : Set where
Sem0 : SemT0 → Set
Sem0 ()

mutual
  data SemT1 : Set where
      U : SemT1
      Π : (A : SemT1) → (Sem1 A → SemT1) → SemT1
      Data :
        (Param : SemT0)
        → (dataArg : SemT0)
        → (recIn : Sem0 dataArg → SemT0)
        → (recParam : (x : Sem0 dataArg) → Sem0 (recIn x) → Sem0 Param)
        → (outParam : Sem0 dataArg → Sem0 Param)
        → (fOut : Set)
        → (fInterp : fOut → Set)
        → (fRec : (x : Sem0 dataArg) → (Sem0 (recIn x) → SemT0) → SemT0)
        → (mutRecParam : (x : Sem0 dataArg) → (y : Sem0 (recIn x)) → Sem0 Param)
        → DataType (Sem0 Param) (Sem0 dataArg) (Sem0 ∘ recIn)
            recParam outParam SemT0 Sem0 fRec mutRecParam {!   !}
        → {!   !}
      cumu : SemT0 → SemT1

  Sem1 : SemT1 → Set
  Sem1 U = SemT0
  Sem1 (Π A B) = (a : Sem1 A) → Sem1 (B a)
  Sem1 (cumu T) = Sem0 T
