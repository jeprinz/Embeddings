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

In this file, I require everything possible as an argument. This will
make definitions more verbose, but hopefully still be possible. If it
does work, then it should get things like type preservation for free.

Concern: will doing this defeat the whole point of extrinsic?
Will it become just as hard as intrinsic?

-}

data PTerm : Set where
  Π : PTerm → PTerm → PTerm → PTerm
  U : ℕ → PTerm
  -- level : ℕ → PTerm

  -- which one ???
  lam : PTerm → PTerm → PTerm → PTerm -- A B e -- includes type information
  app : PTerm → PTerm → PTerm
  var : PTerm → PTerm

  -- _⊢_::_ : PTerm → PTerm → PTerm → PTerm

  _,_ : PTerm → PTerm → PTerm
  ∅ : PTerm


{-
Design questions:
Should I split PTerms into Ctx, Type, and Term?
Should I put Γ ctx in first arg of _⊢_::_ ?

-}

data _ctx : PTerm → Set
data _⊢_::U_ : {Γ : PTerm} → Γ ctx → PTerm → ℕ → Set
data _⊢_::_ : {Γ T : PTerm} → {n : ℕ} → (Γctx : Γ ctx) → PTerm
  → Γctx ⊢ T ::U n → Set
data _⊢_::_≃_ : {Γ a b T n : PTerm} → (Γ' : Γ ctx)
  → (T' : Γ' ⊢ T ::U n)
  → (a' : Γ' ⊢ a :: T') → (b' : Γ' ⊢ b :: T')
  → Set
⊢≃alternate : {Γ T A B : PTerm}
  → Γ ⊢ A :: T → Γ ⊢ B :: T
  → Set
⊢≃alternate = {!   !}

data _ctx where
  ∅ : ∅ ctx
  _,_ : ∀{Γ T n}
    → Γ ctx → Γ ⊢ T :: (U n)
    → (Γ , T) ctx

data _⊢_::_≃_ where

data _⊢_::U_ where

data _⊢_::_ where
  U : ∀{Γ} → (n : ℕ) → Γ ⊢ U n :: U (suc n)

  β : ∀{Γ e A B n}
    → Γ ⊢ e :: A
    → Γ ⊢ A ≃ B
    → Γ ⊢ e :: B
