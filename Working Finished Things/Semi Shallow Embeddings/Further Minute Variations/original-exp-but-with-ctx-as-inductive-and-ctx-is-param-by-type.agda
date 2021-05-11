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
open import Data.Bool

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
mutual
  data Context : Set i → Set j where
    ∅ : Context ⊤
    _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ aΓ T)

  data InCtx : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j where
    same : ∀{aΓ T} → {Γ : Context aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ))
    next : ∀{aΓ Γ T A} → InCtx {aΓ} Γ A → InCtx (Γ , T) (λ γ → A (proj₁ γ))

  proj : ∀{aΓ} → {Γ : Context aΓ} → ∀{T} → (icx : InCtx Γ T)
    → (γ : aΓ) → T γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

mutual
  data Exp : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j where
    Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ aΓ A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Var : ∀{aΓ Γ T} → (icx : InCtx Γ T) → Exp {aΓ} Γ T
    App : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ aΓ A) → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
    Π₀ : ∀{aΓ} → {Γ : Context aΓ} → (A : Exp Γ (λ _ → Set))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ _ → Set))
      → Exp Γ (λ _ → Set)
    𝓤₀ : ∀{aΓ Γ} → Exp {aΓ} Γ (λ _ → Set₁)

  -- unquote
  unq : ∀{aΓ} → {Γ : Context aΓ} → (γ : aΓ) → {T : aΓ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Var icx) = proj icx γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set
