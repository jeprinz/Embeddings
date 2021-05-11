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
  data Context : Set j where
    ∅ : Context
    _,_ : (ctx : Context) → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ctx , h) = Σ (ctxType ctx) (λ t → h t)

  data InCtx : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    same : ∀{Γ T} → InCtx (Γ , T) (λ γ → T (proj₁ γ))
    next : ∀{Γ T A} → InCtx Γ A → InCtx (Γ , T) (λ γ → A (proj₁ γ))

  proj : ∀{Γ T} → (icx : InCtx Γ T) → (γ : ctxType Γ) → T γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

mutual
  data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Var : ∀{Γ T} → (icx : InCtx Γ T)
      → Exp Γ T
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
    Π₀ : {Γ : Context} → (A : Exp Γ (λ _ → Set))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ _ → Set))
      → Exp Γ (λ _ → Set)
    𝓤₀ : ∀{Γ} → Exp Γ (λ _ → Set₁)

  -- unquote
  unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Var icx) = proj icx γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set
