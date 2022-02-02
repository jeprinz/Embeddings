open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit

{-

The idea of this file is:
Normally, typecodes require an inductive-recursive definition.

One way to fix that is to parametrize by another argument.


However, in this file, I want to try a third approach:
Do what I do with the levels, with spines.

In other words, define typecodes by induction on levels and spines such that
they only are defined in terms of smaller typecodes.

There should be essentially no mutual definition whatsoever.

-}

data Spine : Set where
  U : Spine
  Π : Spine → Spine → Spine
  lift : Spine

-- data CtxSpine : Set where

-- while this is a mutual block, TypeCode and ⟦_⟧ should be able to be decoupled into
-- a single induction on the parameters that outputs a Σ of the two.
mutual
  TypeCode : ℕ → Spine → Set
  TypeCode zero T = ⊥
  TypeCode (suc n) U = ⊤
  TypeCode (suc n) (Π A B)
    = Σ (TypeCode (suc n) A) (λ A → ⟦ A ⟧ → TypeCode (suc n) B)
  TypeCode (suc n) lift = Σ Spine (TypeCode n)

  ⟦_⟧ : ∀{n T} → TypeCode n T → Set
  ⟦_⟧ {suc n} {U} T = Σ Spine (TypeCode n)
  ⟦_⟧ {suc n} {Π _ _} (A , B) = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦_⟧ {suc n} {lift} (t , T) = ⟦ T ⟧

{-
test : ∀{n t} → TypeCode n t → ℕ
test {suc n} {U} T = {!   !}
test {suc n} {Π a b} (A , B) = {!   !}
test {suc n} {lift} T = {!   !}

should be no different for terms, just include term spines.
sub only runs on smaller term spines.

(A : Term Γ U)
→ (B : Term (Γ , A) U)
→ (e₁ : Term Γ (Π A B))
→ (e₂ : Term Γ A)
→ Term Γ (sub B e₂)

In def of Ne and Nf, I could see Nf being defined in this way because
you can figure out the inputs purely based on the output of a given constructor.

-}

-- Original typecodes:
{-
data TypeCode₀ : Set where
⟦_⟧₀ : TypeCode₀ → Set
⟦_⟧₀ ()

module Universe {TypeCode : Set} {⟦_⟧ : TypeCode → Set} where
  mutual
    data TypeCodeₙ₊₁ : Set where
        `U : TypeCodeₙ₊₁
        `Π : (A : TypeCodeₙ₊₁) → (⟦_⟧ₙ₊₁ A → TypeCodeₙ₊₁) → TypeCodeₙ₊₁
        `lift : TypeCode → TypeCodeₙ₊₁

    ⟦_⟧ₙ₊₁ : TypeCodeₙ₊₁ → Set
    ⟦ `U ⟧ₙ₊₁ = TypeCode
    ⟦ `Π A B ⟧ₙ₊₁ = (a : ⟦ A ⟧ₙ₊₁) → ⟦ B a ⟧ₙ₊₁
    ⟦ `lift T ⟧ₙ₊₁ = ⟦ T ⟧

open Universe

mutual
  TypeCode : ℕ → Set
  TypeCode zero = TypeCode₀
  TypeCode (suc n) = TypeCodeₙ₊₁ {TypeCode n} {⟦_⟧}

  ⟦_⟧ : {n : ℕ} → TypeCode n → Set
  ⟦_⟧ {zero} T = ⟦ T ⟧₀
  ⟦_⟧ {suc n} T = ⟦ T ⟧ₙ₊₁
-}
