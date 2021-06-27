{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --without-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
-- open import Relation.Nullary
-- for universe levels
-- open import Agda.Primitive
-- open import Data.Empty
-- open import Data.Unit
open import Data.Nat

{-

The goal of this file is to implement an extrinsic definition of
dependent type theory. I have noticed that there is a particular
design decision that one has when implementing intrinsic type
theory.

For example, in the relation Γ ⊢ t :: T, Γ, t, and T are all preterms.
However, one could also ask for an input (Γ ctx). Or, one could also
just prove that if (Γ ⊢ t :: T) → Γ ctx.
In other words, do we just assume that things in the right position
must be correct, or do we require as arguments?

In this file, I just assume correct. This would require things like
type preservation to be proven separately later.

-}

data PVar : Set where
  z : PVar
  s : PVar → PVar

data PTerm : Set where
  Π : PTerm → PTerm → PTerm
  U : ℕ → PTerm
  -- level : ℕ → PTerm

  lam : PTerm → PTerm -- doesn't include type information
  app : PTerm → PTerm → PTerm
  var : PTerm → PTerm
  sub : PTerm → PVar → PTerm → PTerm

data PCtx : Set where
  _,_ : PCtx → PTerm → PCtx
  ∅ : PCtx


{-
Design questions:
Should I split PTerms into Ctx, Type, and Term?
Should I put Γ ctx in first arg of _⊢_::_ ?

-}

data _ctx : PCtx → Set
data _⊢_::_ : PCtx → PTerm → PTerm → Set
data _⊢_≃_ : PCtx → PTerm → PTerm → Set
data Var : PVar → PCtx → PTerm → Set

Sub : PCtx → PCtx → Set
Sub Γ₁ Γ₂ = ∀{} → Var x Γ₁ T → Var x Γ₂ (sub )

data _ctx where
  ∅ : ∅ ctx
  _,_ : ∀{Γ T n}
    → Γ ctx → Γ ⊢ T :: (U n)
    → (Γ , T) ctx

data _⊢_≃_ where

data _⊢_::_ where
  U : ∀{Γ} → (n : ℕ) → Γ ⊢ U n :: U (suc n)
  Π : ∀{Γ A B n}
    → Γ ⊢ A :: U n → (Γ , A) ⊢ B :: U n
    → Γ ⊢ (Π A B) :: U n
  lam : ∀{Γ A B e}
    → (Γ , A) ⊢ e :: B → Γ ⊢ (lam e) :: (Π A B)
  app : ∀{Γ A B e₁ e₂}
    → Γ ⊢ e₁ :: (Π A B) → Γ ⊢ e₂ :: A
    → Γ ⊢ (app e₁ e₂) :: (sub B z e₂)
  sub : ∀{}
    → Γ
  -- sub : ∀{Γ A B e n}
  --   → (Γ , A) ⊢ B :: (U n)
  --   → Γ ⊢ e :: A
  --   → Γ ⊢ (sub B e) :: (U n)


  β : ∀{Γ e A B}
    → Γ ⊢ e :: A
    → Γ ⊢ A ≃ B
    → Γ ⊢ e :: B

data Var where
