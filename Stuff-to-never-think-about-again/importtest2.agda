{-# OPTIONS --cumulativity #-}
{-# OPTIONS --without-K #-}

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

{-

This file is effectively the same as "original-exp-but-with-ctx-as-unq.agda",
but it incorporates ALL of the modifications which I have deemed to be good.

1) Context is a datatype, allowing storage of metadata for e.g. named vars
2) Parametrized by values rather than having unq, allowing for substitution

-}

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

data Context : Set i → Set j where
  ∅ : Context ⊤
  _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ {i} {i} aΓ T)

data InCtx : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
  → ((γ : aΓ) → T γ) → Set j where
  same : ∀{aΓ T} → {Γ : Context aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ)) proj₂
  next : ∀{aΓ Γ T A a} → InCtx {aΓ} Γ A a → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

data Exp : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
  → ((γ : aΓ) → T γ) → Set j where
  Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a}
    → Exp (Γ , A) B a → Exp Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
  Var : {aΓ : Set i} → {Γ : Context aΓ} → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
    → (icx : InCtx Γ T a) → Exp {aΓ} Γ T a
  App : {aΓ : Set i} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
      → Exp Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Exp Γ A a₂)
      → Exp Γ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))
  Π₀ : {aΓ : Set i} → {Γ : Context aΓ} → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
    → (A : Exp Γ (λ _ → Set) a₁)
    → (B : Exp (Γ , (λ γ → a₁ γ)) (λ _ → Set) a₂)
    → Exp Γ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
  𝓤₀ : {aΓ : Set i} → {Γ : Context aΓ} → Exp {aΓ} Γ (λ _ → Set₁) (λ _ → Set₀)

data Exp2 : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
  → ((γ : aΓ) → T γ) → Set j where
  Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a}
    → Exp2 (Γ , A) B a → Exp2 Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
  Var : {aΓ : Set i} → {Γ : Context aΓ} → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
    → (icx : InCtx Γ T a) → Exp2 {aΓ} Γ T a
  App : {aΓ : Set i} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
      → Exp2 Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Exp2 Γ A a₂)
      → Exp2 Γ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))
  Π₀ : {aΓ : Set i} → {Γ : Context aΓ} → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
    → (A : Exp2 Γ (λ _ → Set) a₁)
    → (B : Exp2 (Γ , (λ γ → a₁ γ)) (λ _ → Set) a₂)
    → Exp2 Γ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
  𝓤₀ : {aΓ : Set i} → {Γ : Context aΓ} → Exp2 {aΓ} Γ (λ _ → Set₁) (λ _ → Set₀)

lambdaCount : ∀{aΓ Γ T t} → Exp {aΓ} Γ T t → ℕ
lambdaCount (Lambda e) = 1 + (lambdaCount e)
lambdaCount (Var icx) = 0
lambdaCount (App e1 e2) = (lambdaCount e1) + (lambdaCount e2)
lambdaCount (Π₀ e1 e2) = (lambdaCount e1) + (lambdaCount e2)
lambdaCount 𝓤₀ = 0

test1 : ∀{aΓ Γ T t} → Exp {aΓ} Γ T t → Exp2 {aΓ} Γ T t
test1 (Lambda e) = Lambda (test1 e)
test1 (Var icx) = Var icx
test1 (App e₁ e₂) = ?
test1 (Π₀ e₁ e₂) = Π₀ (test1 e₁) (test1 e₂)
test1 𝓤₀ = 𝓤₀

mutual
  test : ∀{aΓ Γ T t} → Exp {aΓ} Γ T t → (γ : aΓ) → T γ
  test (Lambda e) γ = λ x → (test e) (γ , x)
  test (Var icx) γ = {!   !}
  test (App e₁ e₂) γ = {! (test e₁ γ) (test e₂ γ)  !}
  test (Π₀ e₁ e₂) γ = (x : test e₁ γ) → test e₂ (γ , {!   !} )
  test 𝓤₀ γ = {!   !}

  test≡ : ∀{aΓ Γ T t} → (e : Exp {aΓ} Γ T t) → test e ≡ t
  test≡ (Lambda e) = {!   !}
  test≡ (Var icx) = {!   !}
  test≡ (App e₁ e₂) = {!   !}
  test≡ (Π₀ e e₁) = {!   !}
  test≡ 𝓤₀ = {!   !}
