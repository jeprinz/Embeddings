open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

{-

This is a model for dependent type theory in dependent type theory where types
are represented by a type called SemT, but terms are still represented by terms.

(In contrast to the "standard model" shallow embedding, where everything is
represented by itself.)

Surprisingly, it lets you cram arbitrarily many type levels into a single agda
type level.
Also, we CAN prove consistency!



Essentially we are defining datatypes SemT 0, Sem T 0, SemT 1, Sem T 1, ...
However, datatypes are not first class objects in Agda. Therefore, to make a
datatype parametrized by arbitrary things, one needs to use a module.
Thus, the crazy module stuff.

However, note that if one wants only finitely (but arbitrarily many) levels,
then one can define the types directly without any wierd module stuff.

-}

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

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

type⊥ : ∀{n} → SemT (2 + n)
type⊥ = Π U λ X → cumu X

consistency : ∀{n} → Sem (2 + n) type⊥ → ⊥
consistency {zero} e with (e U)
... | ()
consistency {suc n} e = consistency (e type⊥)

_⇒_ : ∀{n} → SemT n → SemT n → SemT n
_⇒_ {suc n} A B = Π A (λ _ → B)

typeBool : ∀{n} → SemT (suc n)
typeBool = Π U (λ X → (cumu X) ⇒ (cumu X ⇒ cumu X))
-- could put Π in SemT₀ and then put cumu outside ⇒'s
-- although would make proof of consistency impossible?
