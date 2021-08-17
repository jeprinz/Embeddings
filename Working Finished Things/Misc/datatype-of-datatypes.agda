open import Data.Product hiding (map)
open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality

{-

This file defines a datatype which can capture any datatype.
Given Param : Set, it defines a type family

Bla : Param → Set

Specification Param holds a specification of the different constructors in the datatype.
Index should have one element for each constructor of the type, and
constrs then holds the different constructors.

Each constructor is assumed to be of the form in the following type:

data Bla : Param → Set where
  bla : (x : dataArg) → ((y : recInput) → Bla (recParam x y)) → Bla (outParam x)

If you think about it, this can capture basically any constructor. Any constructor
in any datatype must have two types of arguments, "data arguments" which are a type
unrelated to the type being defined, and "recursive arguments" which output an
element of the type being defined. All of the data arguments can be consolidated
into one, and all of the recursive arguments can be consolidated into one.

-}

record Constructor (Param : Set) : Set₁ where
  constructor constr
  field
     dataClause : Set
     recInput : dataClause → Set
     recParam : (x : dataClause) → recInput x → Param
     outParam : dataClause → Param

open Constructor

-- rename to Specification later
record Specification (Param : Set) : Set₁ where
  constructor specification
  field
    Index : Set -- one element for each constructor of the type
    constrs : Index → Constructor Param -- the actual constructors

open Specification

data Element {Param : Set} (spec : Specification Param) : (par : Param) → Set₁ where
  element :
    (index : Index spec)
    → (x : dataClause (constrs spec index))
    → (r : (y : recInput (constrs spec index) x) → Element spec (recParam (constrs spec index) x y))
    → Element _ (outParam (constrs spec index) x)

ind : {Param : Set} → {spec : Specification Param}
  → (P : (par : Param) → Element spec par → Set)
  → ((index : Index spec)
    → (x : dataClause (constrs spec index))
    → (r : (y : recInput (constrs spec index) x) → Element spec (recParam (constrs spec index) x y))
    → ((y : recInput (constrs spec index) x) → P _ (r y)) → P _ (element index x r))
  → (par : Param) → (x : Element spec par) → P par x
ind P el _ (element index x r) = el index x r (λ y → ind P el _ (r y))

NatSpecification : Specification ⊤
NatSpecification
   = specification Bool
      λ {true → constr ⊤ (λ _ → ⊥) (λ _ _ → tt) (λ _ → tt)
      ; false → constr ⊤ (λ _ → ⊤) (λ _ _ → tt) (λ _ → tt)}

ℕ' : Set₁
ℕ' = Element NatSpecification tt

zero' : ℕ'
zero' = element true tt (λ t → ⊥-elim t)

succ' : ℕ' → ℕ'
succ' n = element false tt (λ _ → n)

double : ℕ' → ℕ'
double (element true tt r) = zero' -- zero case
double (element false tt r) = succ' (succ' (double (r tt))) -- succ case

double2 : ℕ' → ℕ
double2 n = ind (λ _ _ → ℕ)
  (λ {true tt r y → zero
    ; false tt r y → 2 + y tt})
  tt n

test : double2 (succ' zero') ≡ 2
test = refl
