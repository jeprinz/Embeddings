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

Just for learning sake, extrinsic STLC

-}

data PVar : Set where
  z : PVar
  s : PVar → PVar

data PType : Set where
  _⇒_ : PType → PType → PType
  base : PType

data PTerm : Set where
  lam : PTerm → PTerm -- doesn't include type information
  app : PTerm → PTerm → PTerm
  var : PVar → PTerm
  sub : PTerm → PVar → PTerm → PTerm

data PCtx : Set where
  _,_ : PCtx → PType → PCtx
  ∅ : PCtx

data _ctx : PCtx → Set
data _type : PType → Set
data _⊢_::_ : PCtx → PTerm → PType → Set
data _⊢_≃_ : PCtx → PTerm → PTerm → Set
data Var : PVar → PCtx → PType → Set

data _ctx where
  ∅ : ∅ ctx
  _,_ : ∀{Γ T}
    → Γ ctx → T type
    → (Γ , T) ctx

-- Sub : PCtx → PCtx → Set
-- Sub Γ₁ Γ₂ = ∀{} → Var x Γ₁ T →

-- TODO: do I even need Γ here?
data _⊢_≃_ where
  lam : ∀{Γ A e₁ e₂}
    -- → ∀{B}
    -- → (Γ , A) ⊢ e₁ :: B
    -- → (Γ , A) ⊢ e₂ :: B
    → (Γ , A) ⊢ e₁ ≃ e₂
    → Γ ⊢ (lam e₁) ≃ (lam e₂)
  app : ∀{Γ e₁ e₁' e₂ e₂'}
    -- → ∀{A B}
    -- → Γ ⊢ e₁ :: (A ⇒ B)
    -- → Γ ⊢ e₁' :: (A ⇒ B)
    -- → Γ ⊢ e₂ :: A
    -- → Γ ⊢ e₂' :: A
    → Γ ⊢ (app e₁ e₁') ≃ (app e₂ e₂')
  var : ∀{Γ x} -- huh?
    → Γ ⊢ (var x) ≃ (var x)
  -- sub
  subZvarZ : ∀{Γ e}
    → Γ ⊢ sub (var z) z e ≃ e
  subZvarS : ∀{Γ e x}
    → Γ ⊢ sub (var (s x)) z e ≃ var x
  subSvarZ : ∀{Γ e x}
    → Γ ⊢ sub (var z) (s x) e ≃ var z
  -- TODO: need to rethink substitutions...
  -- subSvarS : ∀{Γ e x y}
    -- → Γ ⊢ sub (var (s x)) (s y) e ≃ sub (var x) y e -- ????????????????
  -- sublam : ∀{Γ x e₁ e₂}
    -- → Γ ⊢ sub
  -- β : ∀{Γ e₁ e₂

-- not actually needed because STLC is so simple
data _type where
  _⇒_ : ∀{A B}
    → A type → B type
    → (A ⇒ B) type
  base : base type

data _⊢_::_ where
  lam : ∀{Γ A B e}
    → (Γ , A) ⊢ e :: B → Γ ⊢ (lam e) :: (A ⇒ B)
  app : ∀{Γ A B e₁ e₂}
    → Γ ⊢ e₁ :: (A ⇒ B) → Γ ⊢ e₂ :: A
    → Γ ⊢ (app e₁ e₂) :: B
  var : ∀{Γ x T}
    → Var x Γ T → Γ ⊢ (var x) :: T
  -- sub


  -- β : ∀{Γ e A B}
  --   → Γ ⊢ e :: A
  --   → Γ ⊢ A ≃ B
  --   → Γ ⊢ e :: B

data Var where
  z : ∀{Γ T} → Var z (Γ , T) T
  s : ∀{Γ A B x} → Var x Γ A → Var (s x) (Γ , B) A

ex1type : PType
ex1type = base ⇒ base

ex1term : PTerm
ex1term = lam (var z)

ex1derivation : ∅ ⊢ ex1term :: ex1type
ex1derivation = lam (var z)

-- note that the following is also possible:
ex1derivation' : ∅ ⊢ _ :: ex1type
ex1derivation' = lam (var z)
