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

-}

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
k = lsuc j -- type level 1+i

Ctx : Set j
Type : Ctx → Set j
Term : (Γ : Ctx) → Type Γ → Set i
Ctx = Set i
Type Γ = Γ → Set i
Term Γ T = (γ : Γ) → T γ

-- Context constructors
nil : Ctx
nil = ⊤

cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ Γ T

-- Type constructors
U₀ : ∀{Γ} → Type Γ
U₀ = λ γ → Set₀

U₁ : ∀{Γ} → Type Γ
U₁ = λ γ → Set₁

U₂ : ∀{Γ} → Type Γ
U₂ = λ γ → Set₂

Π : ∀{Γ} → (A : Type Γ) → (B : Type (cons Γ A)) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

weakenT : {Γ : Ctx} → {A : Type Γ} → Type Γ → Type (cons Γ A)
weakenT T = λ γ → T (proj₁ γ)

varT : {Γ : Ctx} → Type (cons Γ U₀)
varT = proj₂

simpleSub : {Γ : Ctx} → {A : Type Γ} → Type (cons Γ A)
  → Term Γ A → Type Γ
simpleSub T e = λ γ → T (γ , e γ)

-- Term constructors

lambda : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app  : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term Γ (Π A B) → (x : Term Γ A) → Term Γ (simpleSub B x)
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

weaken : {Γ : Ctx} → {A T : Type Γ}
  → Term Γ T → Term (cons Γ A) (weakenT T)
weaken e = λ γ → e (proj₁ γ)

var : {Γ : Ctx} → {T : Type Γ}
  → Term (cons Γ T) (weakenT T)
var = proj₂

U₀' : ∀{Γ} → Term Γ U₁
U₀' = λ γ → Set₀

U₁' : ∀{Γ} → Term Γ U₂
U₁' = λ γ → Set₁

Π' : ∀{Γ} → (A : Term Γ U₀) → (B : Term (cons Γ A) U₀) → Term Γ U₀
Π' A B = λ γ → (a : A γ) → B (γ , a)

mutual
  data ECtx : Ctx → Set j where
    ∅ : ECtx ⊤
    _,_ : ∀{aΓ} → (ctx : ECtx aΓ) → (T : aΓ → Set i) → ECtx (Σ {i} {i} aΓ T)

  data InCtx : {aΓ : Ctx} → (Γ : ECtx aΓ) → (T : aΓ → Set i)
    → ((γ : aΓ) → T γ) → Set j where
    same : ∀{aΓ T} → {Γ : ECtx aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ)) proj₂
    next : ∀{aΓ Γ T A a} → InCtx {aΓ} Γ A a → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

mutual
  data Nf : {aΓ : Set i} → (Γ : ECtx aΓ) → (T : Type aΓ)
    → ((γ : aΓ) → T γ) → Set j where
    Elambda : ∀{aΓ} → {Γ : ECtx aΓ} → {A : Type aΓ} → {B : Type (cons aΓ A)} → ∀{a}
      → Nf (Γ , A) B a → Nf Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
    EΠ₀ : {aΓ : Set i} → {Γ : ECtx aΓ} → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
      → (A : Nf Γ (λ _ → Set) a₁)
      → (B : Nf (Γ , (λ γ → a₁ γ)) (λ _ → Set) a₂)
      → Nf Γ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
    EU₀ : {aΓ : Set i} → {Γ : ECtx aΓ} → Nf {aΓ} Γ U₁ U₀'
    fromNe : ∀{aΓ} → {Γ : ECtx aΓ} → {T : aΓ → Set i}
      → {a : (γ : aΓ) → T γ} → Ne Γ T a → Nf Γ T a

  data Ne : {aΓ : Set i} → (Γ : ECtx aΓ) → (T : Type aΓ)
    → ((γ : aΓ) → T γ) → Set j where
    Evar : {aΓ : Set i} → {Γ : ECtx aΓ} → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
      → (icx : InCtx Γ T a) → Ne {aΓ} Γ T a
    Eapp : {aΓ : Set i} → {Γ : ECtx aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
        → Ne Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Nf Γ A a₂)
        → Ne Γ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))

{-

What I want to simulate is:
Ctx : Set
Type : Ctx → Set
Term : (Γ : Ctx) → Type Γ → Set

---

Sem : (Γ : Ctx) → Type Γ → Set
eval : Term Γ T → Sem Γ T

instead, constructors of Term directly give elements of Sem Γ T.
Type constructors directly give Sem Γ T.
-}

Sub : Ctx → Ctx → Set j
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

subType : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
subType sub T = λ γ → T (sub γ)

subTerm : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → {T : Type Γ₁}
  → Term Γ₁ T → Term Γ₂ (subType sub T)
subTerm sub t = λ γ → t (sub γ)

append1sub : ∀{Γ₁ Γ₂ A} → (sub : Sub Γ₁ Γ₂) → Term Γ₂ (subType sub A)
  → Sub (cons Γ₁ A) Γ₂
append1sub sub t γ = sub γ , t γ

liftSub : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂)
  → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
liftSub sub (γ , t) = sub γ , t

ESub : {Γ₁ Γ₂ : Ctx} → Sub Γ₁ Γ₂ → ECtx Γ₁ → ECtx Γ₂ → Set j
ESub sub EΓ₁ EΓ₂
  = ∀{T t} → InCtx EΓ₁ T t → Nf EΓ₂ (subType sub T) (subTerm sub t)

EidSub : {Γ : Ctx} → {EΓ : ECtx Γ} → ESub idSub EΓ EΓ
EidSub x = fromNe (Evar x)

-- SType EΓ T t   is the intermediate value of a computation
-- it is the return type of Sem T
SType : (Γ : Ctx) → Type Γ → Set k
SType Γ T = (EΓ : ECtx Γ)
  → Term Γ T
  → Set j

-- Should OUTPUT an SType! this is supposed to be a step in Sem recursion,
-- so must both input and output SType!
-- SType is type of Sem OTHER THAN Type arg.

SemΠ : {Γ : Ctx} → {EΓ : ECtx Γ}
  → {A : Type Γ} → {B : Type (cons Γ A)}
  → (SA : SType Γ A) → (SB : SType (cons Γ A) B)
  -- → Set j
  → SType Γ
SemΠ {Γ} {EΓ} {A} {B} SA SB
  = Σ {i} {j} (Term Γ (Π A B))
  (λ f →
    Nf EΓ (Π A B) f
    × ((a : ∀{Γ'} → (sub : Sub Γ Γ') → Term Γ' (subType sub A))
      → (e : ∀{Γ' EΓ'} → {sub : Sub Γ Γ'} → (Esub : ESub sub EΓ EΓ')
        → Nf EΓ' (subType sub A) (a sub))
      → Nf EΓ (simpleSub B (a idSub)) (app f (a idSub)))
  )

-- Semlambda : {Γ : Ctx} → {EΓ : ECtx Γ}
--   → {A : Type Γ} → {B : Type (cons Γ A)}
--   → (SA : Set j) → (SB : Set j)
--   → {e : Term (cons Γ B) A}
--   → {Ee : Nf (EΓ , B) A}
