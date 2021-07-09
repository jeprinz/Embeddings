open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

{-

Like Core.agda, but hopefully without mututally recursive function!

-}

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

-- previous level can still be as if from function, then implement type and function in terms of parametrized type
module sucn (SemTn : Set) (Semn : SemTn → Set) where
  data SemTsucn : Set → Set₁ where
      U : SemTsucn SemTn
      Π : {sA : Set} → {sB : sA → Set}
        → (A : SemTsucn sA) → ((a : sA) → SemTsucn (sB a)) → SemTsucn ((a : sA) → sB a)
      cumu : (T : SemTn) → SemTsucn (Semn T)
{-
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
-}
