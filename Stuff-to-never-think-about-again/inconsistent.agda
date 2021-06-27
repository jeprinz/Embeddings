{-# OPTIONS --type-in-type #-}

-- per definition:
-- {-# TERMINATING #-}
-- {-# NO_POSITIVITY_CHECK #-}

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

Ctx : Set
Type : Ctx → Set
Term : (Γ : Ctx) → Type Γ → Set
Ctx = Set
Type Γ = Γ → Set
Term Γ T = (γ : Γ) → T γ

-- Context constructors
nil : Ctx
nil = ⊤

cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ Γ T

-- Type constructors
U : ∀{Γ} → Type Γ
U = λ γ → Set

Π : ∀{Γ} → (A : Type Γ) → (B : Type (cons Γ A)) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

weakenT : {Γ : Ctx} → {A : Type Γ} → Type Γ → Type (cons Γ A)
weakenT T = λ γ → T (proj₁ γ)

varT : {Γ : Ctx} → Type (cons Γ U)
varT = proj₂

sub : {Γ : Ctx} → {A : Type Γ} → Type (cons Γ A)
  → Term Γ A → Type Γ
sub T e = λ γ → T (γ , e γ)

-- Term constructors

lambda : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app  : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term Γ (Π A B) → (x : Term Γ A) → Term Γ (sub B x)
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

weaken : {Γ : Ctx} → {A T : Type Γ}
  → Term Γ T → Term (cons Γ A) (weakenT T)
weaken e = λ γ → e (proj₁ γ)

var : {Γ : Ctx} → {T : Type Γ}
  → Term (cons Γ T) (weakenT T)
var = proj₂

mutual
  data ECtx : Set → Set where
    ∅ : ECtx ⊤
    _,_ : ∀{aΓ} → (ctx : ECtx aΓ) → (T : aΓ → Set) → ECtx (Σ aΓ T)

  data InCtx : {aΓ : Set} → (Γ : ECtx aΓ) → (T : aΓ → Set)
    → ((γ : aΓ) → T γ) → Set where
    same : ∀{aΓ T} → {Γ : ECtx aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ)) proj₂
    next : ∀{aΓ Γ T A a} → InCtx {aΓ} Γ A a → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

mutual
  data Exp : {Γ : Set} → (EΓ : ECtx Γ) → (T : Type Γ)
    → ((γ : Γ) → T γ) → Set where
    Elambda : {Γ : Ctx} → {EΓ : ECtx Γ} → {A : Type Γ} → {B : Type (cons Γ A)} → ∀{a}
      → Exp (EΓ , A) B a → Exp EΓ (Π A B) (lambda a)
    Evar : {Γ : Ctx} → {EΓ : ECtx Γ} → {T : Type Γ} → {a : Term Γ T}
      → (icx : InCtx EΓ T a) → Exp {Γ} EΓ T a
    Eapp : {Γ : Ctx} → {EΓ : ECtx Γ} → {A : Type Γ} → {B : Type (cons Γ A)} → ∀{a₁ a₂}
        → Exp EΓ (Π A B) a₁ → Exp EΓ A a₂
        → Exp EΓ (sub B a₂) (app a₁ a₂)
    EΠ : {Γ : Set} → {EΓ : ECtx Γ} → {a₁ : Type Γ} → {a₂ : Type (cons Γ a₁)}
      → (A : Exp EΓ U a₁)
      → (B : Exp (EΓ , a₁) U a₂)
      → Exp EΓ U (Π a₁ a₂)
    EU : {Γ : Ctx} → {EΓ : ECtx Γ} → Exp {Γ} EΓ U U
