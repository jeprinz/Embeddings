{-# OPTIONS --cumulativity --without-K #-}

{-

This is my original implementation of a shallow-ish embedding.
At the time, I didn't know what a shallow embedding was. It turns out that this is
essentially a shallow embedding, except using a datatype. This comes with certian
advantages in a programming language design sense, but not so much in a
mathematical sense. For example, see named-variables.agda

-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

------------------------------------------------------------
-- Representation of Dependent Type Theory in 30 lines
------------------------------------------------------------

mutual -- Γ ⊢ e : T    corresponds to     e : Exp Γ T
  data Exp : (Γ : Set i) → (T : Γ → Set i) → Set j where
    Lambda : {Γ : Set i} → {A : Γ → Set i} → {B : Σ {i} {i} Γ A → Set i} →
      Exp (Σ {i} {i} Γ A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    App : {Γ : Set i} → {A : Γ → Set i} → {B : Σ Γ A → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
    Weaken : {Γ : Set i} → {A B : Γ → Set i}
      → Exp Γ B → Exp (Σ Γ A) (λ γ → B (proj₁ γ))
    EndCtx : {Γ : Set i} → {A : Γ → Set i}
      → Exp (Σ Γ A) (λ γ → A (proj₁ γ))

  -- unquote
  unq : {Γ : Set i} → (γ : Γ) → {T : Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Weaken e) = unq (proj₁ γ) e
  unq γ (EndCtx) = proj₂ γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)

id : Exp ⊤ (λ _ → (X : Set) → X → X)
id = Lambda (Lambda EndCtx)

-- Examples:

idMap : ∀{Γ T} → Exp Γ T → Exp Γ T
idMap (Lambda e) = Lambda (idMap e)
idMap (App e₁ e₂) = {! e₁  !}
idMap (Weaken e) = Weaken (idMap e)
idMap EndCtx = EndCtx

-- NOT POSSIBLE!!!!
