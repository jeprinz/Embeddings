{-# OPTIONS --cumulativity #-}
open import Agda.Primitive
open import Data.Product

module test where

data ⊤ {i : Level} : Set i where
  tt : ⊤

-- out of sheer curiosity, what happens if I make datatype-by-Pi for augmented shallow embedding?

module Embedding (k : Level)
  (Contextk : Set k → Set (lsuc k))
  (InCtxk : {aΓ : Set k} → (Γ : Contextk aΓ) → (T : aΓ → Set k)
    → ((γ : aΓ) → T γ) → Set (lsuc k))
  (Expk : {aΓ : Set k} → (Γ : Contextk aΓ) → (T : aΓ → Set k)
    → ((γ : aΓ) → T γ) → Set (lsuc k))
  where

  i = lsuc k
  j = lsuc i

  data Context : Set i → Set j where
    cumu : {Γ : Set k} → Contextk Γ → Context Γ
    ∅ : Context ⊤
    _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ {i} {i} aΓ T)

  data InCtx : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
    → ((γ : aΓ) → T γ) → Set j where
    same : ∀{aΓ T} → {Γ : Context aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ)) proj₂
    next : ∀{aΓ Γ T A a} → InCtx {aΓ} Γ A a → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

  -- data Exp : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
  --   → ((γ : aΓ) → T γ) → Set j where
  --   Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a}
  --     → Exp (Γ , A) B a → Exp Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
  --   Var : {aΓ : Set i} → {Γ : Context aΓ} → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
  --     → (icx : InCtx Γ T a) → Exp {aΓ} Γ T a
  --   App : {aΓ : Set i} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
  --       → Exp Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Exp Γ A a₂)
  --       → Exp Γ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))
  --   Π₀ : {aΓ : Set i} → {Γ : Context aΓ} → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
  --     → (A : Exp Γ (λ _ → Set) a₁)
  --     → (B : Exp (Γ , (λ γ → a₁ γ)) (λ _ → Set) a₂)
  --     → Exp Γ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
  --   𝓤₀ : {aΓ : Set i} → {Γ : Context aΓ} → Exp {aΓ} Γ (λ _ → Set₁) (λ _ → Set₀)

-- tactics like try through augmented embeddings
-- instead of App taking an Exp A → B, Exp A and giving an Exp B,
-- it could

--            ↓ goal(s) plural, instead of just type
-- Exp : Γ → [T] → [t] →
