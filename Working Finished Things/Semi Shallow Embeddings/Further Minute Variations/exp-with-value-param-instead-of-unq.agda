{-# OPTIONS --cumulativity --without-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Maybe

module exp-with-value-param-instead-of-unq where

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

Σi = Σ {i} {i}

mutual -- Γ ⊢ e : T    corresponds to     e : Exp Γ T
  data Exp : (Γ : Set i) → (T : Γ → Set i) → ((γ : Γ) → T γ) → Set j where
    Lambda : {Γ : Set i} → {A : Γ → Set i} → {B : Σi Γ A → Set i} → ∀{x}
      → Exp (Σ {i} {i} Γ A) B x → Exp Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ → λ a → x (γ , a))
    -- Π₀ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₀))
    --   → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₀))
    --   → Exp Γ (λ γ → Set₀)
    -- Π₁ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₁))
    --   → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₁))
    --   → Exp Γ (λ γ → Set₁)
    -- 𝓤₀ : {Γ : Set i} → Exp Γ (λ γ → Set₁)
    -- 𝓤₁ : {Γ : Set i} → Exp Γ (λ γ → Set₂)
    -- Cumulativity : ∀{Γ} → Exp Γ (λ _ → Set₀) → Exp Γ (λ _ → Set₁)
    App : {Γ : Set i} → {A : Γ → Set i} → {B : Σi Γ A → Set i} → ∀{x₁ x₂}
        → Exp Γ (λ γ → (a : A γ) → B (γ , a)) x₁ → (x : Exp Γ A x₂)
        → Exp Γ (λ γ → B (γ , x₂ γ)) λ γ → (x₁ γ) (x₂ γ)
    Weaken : {Γ : Set i} → {A B : Γ → Set i} → ∀ {x}
      → Exp Γ B x → Exp (Σ Γ A) (λ γ → B (proj₁ γ)) λ γ → x (proj₁ γ)
    EndCtx : {Γ : Set i} → {A : Γ → Set i}
      → Exp (Σ Γ A) (λ γ → A (proj₁ γ)) proj₂
    constℕ : {Γ : Set i} → (n : ℕ) → Exp Γ (λ _ → ℕ) (λ _ → n)
    plus : {Γ : Set i} → Exp Γ (λ _ → ℕ → ℕ → ℕ) (λ _ → _+_)

-- TODO: replace x's above with t

consistent : ∀{b} → ¬ (Exp ⊤ (λ _ → ⊥) b)
consistent {b} e = b tt

idMap : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
idMap (Lambda e) = Lambda (idMap e)
idMap (App e₁ e₂) = App (idMap e₁) (idMap e₂)
idMap (Weaken e) = Weaken (idMap e)
idMap EndCtx = EndCtx
idMap (constℕ n) = constℕ n
idMap plus = plus

-- slaps a (λ x . x) in front of every subterm
stupidTransform : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
stupidTransform (Lambda e) = Lambda (App (Lambda EndCtx) e)
stupidTransform (App e₁ e₂) = App (App (Lambda EndCtx) e₁) (App (Lambda EndCtx) e₂)
stupidTransform (Weaken e) = Weaken (App (Lambda EndCtx) e)
stupidTransform EndCtx = EndCtx
stupidTransform (constℕ n) = constℕ n
stupidTransform plus = plus

-- f : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
-- f (Lambda e) = {! e  !}
-- f (App e₁ e₂) = {! e₁  !}
-- f (Weaken e) = {!  e !}
-- f EndCtx = {!   !}
-- f (constℕ n) = {!   !}
-- f plus = {!   !}



unqStupid : ∀{Γ T t} → Exp Γ T t → (γ : Γ) → T γ
unqStupid {Γ} {T} {t} e = t
