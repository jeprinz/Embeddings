open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product renaming (Σ to Σbi) -- bi stands for built-in
open import Data.List

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

module sucn (SemTn : Set) (Semn : SemTn → Set) where
  mutual
    data SemTsucn : Set where
        U : SemTsucn
        Π : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        Σ : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        cumu : SemTn → SemTsucn

    Semsucn : SemTsucn → Set
    Semsucn U = SemTn
    Semsucn (Π A B) = (a : Semsucn A) → Semsucn (B a)
    Semsucn (Σ A B) = Σbi (Semsucn A) (λ a → Semsucn (B a))
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

{-
-- specification of an inductive type

A type has a dependent list of parameters
A type has a list of constructors
A constructor has a list of clauses
A clause is
  -- some number of arguments and then ends in the type being defined.
    -- Datawise, is dependent list of arguments and then instance of parameters.
    -- might as well just be a single type instead of list. Can be product or unit.
    -- However, then I need products.
  -- some type

(As I go, ensure all types im using themselves meet these criteria...)
-}

mutual
  data Test : Set₁ where
    test : ℕ → ℕ → Test
    test3 : (g : Set → Set) → (X : Set) → g X → Test -- dependency of arguments on previous ones
    test2 : (t : Test) → (f t → f t) → Test

  f : Test → Set
  f x = ℕ

Parameters : ℕ → Set
Parameters n = SemT n

data Clause : (n : ℕ) → Parameters n → Set where
  recursiveClause : ∀{n} → {P : Parameters (suc n)}
    → (T : SemT (suc n)) → Sem (suc n) (T ⇒ P) → Clause (suc n) P
  simpleClause : ∀{n} → {P : Parameters n}
    → (T : SemT n) → Clause n P

data Constructor : (n : ℕ) → Parameters n → Set where
  ∅ : ∀{n P} → Constructor n P
  -- _,_ : ∀{n P} → (c : Clause n P) → ({! c  !} → Constructor n P) → Constructor n P
  recClause : ∀{n} → {P : Parameters (suc n)}
    → (T : SemT (suc n)) → (f : Sem (suc n) (T ⇒ P))
    -- several things wrong here. subsequent arguments can depend on actual elements of type being defined, not just parameters. see Test above.
    → ((t : Sem (suc n) T) → {! (f t)  !} → Constructor (suc n) P) -- rest of constructor can depend on argument
    → Constructor (suc n) P
  regClause : ∀{n} → {P : Parameters n}
    → (T : SemT n)
    → (Sem n T → Constructor n P) -- rest of constructor can depend on argument
    → Constructor n P
{-


-- data Inductive : Set where
--   datatype : List Constructor → Inductive

-- data Index : List Constructor → Constructor → Set where
--   same : ∀{l e} → Index (e ∷ l) e
--   next : ∀{x y l} → Index l y → Index (x ∷ l) y

-- data Element : Inductive → Set where
-}
