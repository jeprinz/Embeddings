open import Data.Product hiding (map)
open import Data.List
open import Data.Unit
open import Data.Nat
{-

Foo is type being defined, for example

Types have
- parameters - w.l.o.g, exactly one parameter (use Σ, ⊤ for no parameters)
- constructors
  - for my purposes, these are completely independent of each other.
  - in general, subsequent constructors can depend on previous ones
Constructors are a list of clauses
- clauses
  - arguments - w.l.o.g, exactly one argument (again, use Σ and ⊤)
  - depends on previous clauses, which are functions ((t : T) → Foo (P t))
  - Two kinds:
    - pure data: no instance of parameter
    - recursion : instance of parameter


Working hypothesis: It is not necessary to have clauses depend on previous clauses.
Why? because: if pure data clause depends on pure data clause, could have just had
one clause with Σ.
Using the mutual function → parameter transformation, never need to depend on
recursion clause.
BUT!!!! recursion clause could depend on pure data clause.

SO IN CONCLUSION:::
    - Each constructor has one pure data clause and any number of recursion clauses,
      each of which depends only on the pure data clause.
      Also, output parameters.

-}

-- parameter is
-- data Clause : Set → Set where

-- parameter is defined datatype parameter
data Constructor : Set → Set₁ where
  constr : ∀{Param} → (dataClause : Set)
    → List (dataClause → Σ Set (λ T → T → Param))
    → (dataClause → Param) -- output parameters
    → Constructor Param
  constr1 : ∀{Param} → (dataClause : Set)
    -- → List (dataClause → Σ Set (λ T → T → Param))
    → (dataClause → Σ Set (λ T → T → Param))
    → (dataClause → Param) -- output parameters
    → Constructor Param

DataType : Set → Set₁
DataType Param = List (Constructor Param)

data CIndex : {Param : Set} → DataType Param → Constructor Param → Set where
  same : ∀{Param D C} → CIndex {Param} (C ∷ D) C
  next : ∀{Param D C C'} → CIndex {Param} D C → CIndex {Param} (C' ∷ D) C

data ⊤₁ : Set₁ where
  tt : ⊤₁

mutual
  RecData : (Param : Set) → DataType Param → List (Σ Set (λ T → T → Param)) → Set₁
  RecData Param D [] = ⊤₁
  RecData Param D ((T , outParam) ∷ clauses)
    = ((t : T) → Element D (outParam t)) × RecData Param D clauses

  data Element : {Param : Set} → DataType Param → Param → Set₁ where
    el : ∀{Param D dataClause recClauses outParam}
      → CIndex D (constr dataClause recClauses outParam)
      → (x : dataClause)
      → RecData Param D (map (λ clause → clause x) recClauses)
      → Element D (outParam x)
    -- The purpose of el1 is to demonstrate that having a mutually recursive
    -- RecData is not strictly necessary to make this work, although need an
    -- eln if one wants constructors with n recursive arguments. Luckily, for all
    -- n, eln can represent itself!!!!
    el1 : ∀{Param D dataClause recClause outParam}
      → CIndex D (constr1 dataClause recClause outParam)
      → (x : dataClause)
      -- → RecData Param D (map (λ clause → clause x) recClauses)
      → ((t : proj₁ (recClause x) ) → Element D (proj₂ (recClause x) t))
      → Element {Param} D (outParam x)

indPrincipleCtr : ∀{Param} → (Param → Set) → DataType Param → Constructor Param → Set₁
indPrincipleCtr P D (constr dataClause recClauses outParam) = {!   !}
indPrincipleCtr P D (constr1 dataClause recClause outParam)
  = (x : dataClause)
    → (t : proj₁ (recClause x))
    → Element D (proj₂ (recClause x) t)
    → {!   !}

-- induct : ∀{Param param} → (D : DataType Param) → Element D param
--   → (P : Param → Set)
--   → {!   !}
--   → Element D param
--   → P param
-- induct = {!   !}

NatSpecification : DataType ⊤
NatSpecification
  = constr ⊤ [] (λ _ → tt)
  ∷ constr ⊤ [ (λ _ → ⊤ , λ _ → tt )] (λ _ → tt)
  ∷ []

ℕ' : Set₁
ℕ' = Element NatSpecification tt

zero' : ℕ'
zero' = el same tt tt

succ' : ℕ' → ℕ'
succ' n = el (next same) tt ((λ _ → n) , tt)

{-

NOTE! I've made things unecessarily complicated up there, because
if there are multiple recClauses, can be consolidated into one recClause.
For example,
(A → T) × (B → T) ≃ (A + B → T)
So, effectively only need el1, and not el!!!! (or any other eln)

-}
