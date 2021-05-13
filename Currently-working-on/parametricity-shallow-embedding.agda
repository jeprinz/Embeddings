{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --without-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
-- open import Data.Sum
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

{-

A shallow embedding which instead of giving agda type and values, gives
FREE THEOREMS and PROOFS OF FREE THEOREMS.

Original concept from https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.LightweightFreeTheorems
I also referenced: https://bitbucket.org/akaposi/shallow/src/master/Agda/Param.agda

-}

-- module parametricity-shallow-embedding where

--------------------------------------------------------------------------------
-- STANDARD SHALLOW EMBEDDING --
--------------------------------------------------------------------------------
i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

Ctx : Set j
Ctx = Set i
Type₀ : Ctx → Set j
Type₀ Γ = Γ → Set₀
Term₀ : (Γ : Ctx) → Type₀ Γ → Set j
Term₀ Γ T = (γ : Γ) → T γ
Type₁ : Ctx → Set j
Type₁ Γ = Γ → Set₁
Term₁ : (Γ : Ctx) → Type₁ Γ → Set j
Term₁ Γ T = (γ : Γ) → T γ

-- Context constructors
nil : Ctx
nil = ⊤

cons₀ : (Γ : Ctx) → Type₀ Γ → Ctx
cons₀ Γ T = Σ Γ T

cons₁ : (Γ : Ctx) → Type₁ Γ → Ctx
cons₁ Γ T = Σ Γ T

-- Type constructors
U₀ : ∀{Γ} → Type₁ Γ
U₀ = λ γ → Set₀

Π₀ : ∀{Γ} → (A : Type₀ Γ) → (B : Type₀ (cons₀ Γ A)) → Type₀ Γ
Π₀ A B = λ γ → (a : A γ) → B (γ , a)

Π₁ : ∀{Γ} → (A : Type₁ Γ) → (B : Type₁ (cons₁ Γ A)) → Type₁ Γ
Π₁ A B = λ γ → (a : A γ) → B (γ , a)

weakenT₀ : {Γ : Ctx} → {A : Type₀ Γ} → Type₀ Γ → Type₀ (cons₀ Γ A)
weakenT₀ T = λ γ → T (proj₁ γ)

weakenT₁ : {Γ : Ctx} → {A : Type₁ Γ} → Type₁ Γ → Type₁ (cons₁ Γ A)
weakenT₁ T = λ γ → T (proj₁ γ)

varT₀ : {Γ : Ctx} → Type₀ (cons₁ Γ U₀)
varT₀ = proj₂

sub₀ : {Γ : Ctx} → {A : Type₀ Γ} → Type₀ (cons₀ Γ A)
  → Term₀ Γ A → Type₀ Γ
sub₀ T e = λ γ → T (γ , e γ)

sub₁ : {Γ : Ctx} → {A : Type₁ Γ} → Type₁ (cons₁ Γ A)
  → Term₁ Γ A → Type₁ Γ
sub₁ T e = λ γ → T (γ , e γ)

-- Term constructors

lambda₀ : {Γ : Ctx} → {A : Type₀ Γ} → {B : Type₀ (cons₀ Γ A)}
  → Term₀ (cons₀ Γ A) B → Term₀ Γ (Π₀ A B)
lambda₀ e = λ γ a → e (γ , a)

lambda₁ : {Γ : Ctx} → {A : Type₁ Γ} → {B : Type₁ (cons₁ Γ A)}
  → Term₁ (cons₁ Γ A) B → Term₁ Γ (Π₁ A B)
lambda₁ e = λ γ a → e (γ , a)

app₀  : {Γ : Ctx} → {A : Type₀ Γ} → {B : Type₀ (cons₀ Γ A)}
  → Term₀ Γ (Π₀ A B) → (x : Term₀ Γ A) → Term₀ Γ (sub₀ B x)
app₀ e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

weaken₀ : {Γ : Ctx} → {A T : Type₀ Γ}
  → Term₀ Γ T → Term₀ (cons₀ Γ A) (weakenT₀ T)
weaken₀ e = λ γ → e (proj₁ γ)

var₀ : {Γ : Ctx} → {T : Type₀ Γ}
  → Term₀ (cons₀ Γ T) (weakenT₀ T)
var₀ = proj₂

-- EXAMPLE:
-- λ X x . x : (X : Set) → X → X
exType : Type₁ nil
exType = Π₁ U₀ (Π₁ varT₀ (weakenT₁ varT₀))

exTerm : Term₁ nil exType
exTerm = lambda₁ (lambda₀ var₀) -- note some shenanigans with type level cumulativity combined with it being a shallow embedding, to Type₀ < Type₁ essentially.

--------------------------------------------------------------------------------

-- PARAMETRICITY EMBEDDING:

PCtx : Ctx → Ctx → Set j
PCtx Γ₁ Γ₂ = Γ₁ → Γ₂ → Set i

PType₀ : {Γ₁ Γ₂ : Ctx} → PCtx Γ₁ Γ₂ → (T₁ : Type₀ Γ₁) → (T₂ : Type₀ Γ₂) → Set j
PType₀ {Γ₁} {Γ₂} Γ T₁ T₂ = {γ₁ : Γ₁} → {γ₂ : Γ₂} → Γ γ₁ γ₂ → T₁ γ₁ → T₂ γ₂ → Set₁

PType₁ : {Γ₁ Γ₂ : Ctx} → PCtx Γ₁ Γ₂ → (T₁ : Type₁ Γ₁) → (T₂ : Type₁ Γ₂) → Set j
PType₁ {Γ₁} {Γ₂} Γ T₁ T₂ = {γ₁ : Γ₁} → {γ₂ : Γ₂} → Γ γ₁ γ₂ → T₁ γ₁ → T₂ γ₂ → Set₂

PTerm₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → PType₀ Γ T₁ T₂
  → Term₀ Γ₁ T₁ → Term₀ Γ₂ T₂ → Set j
PTerm₀ {Γ₁} {Γ₂} Γ T e₁ e₂ = {γ₁ : Γ₁} → {γ₂ : Γ₂} → (γ : Γ γ₁ γ₂)
  → T {γ₁} {γ₂} γ (e₁ γ₁) (e₂ γ₂)

PTerm₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → PType₁ Γ T₁ T₂
  → Term₁ Γ₁ T₁ → Term₁ Γ₂ T₂ → Set j
PTerm₁ {Γ₁} {Γ₂} Γ T e₁ e₂ = {γ₁ : Γ₁} → {γ₂ : Γ₂} → (γ : Γ γ₁ γ₂)
  → T {γ₁} {γ₂} γ (e₁ γ₁) (e₂ γ₂)

-- -- Context constructors
Pnil : PCtx nil nil
Pnil tt tt = ⊤

Pcons₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → PType₀ Γ T₁ T₂
  → PCtx (cons₀ Γ₁ T₁) (cons₀ Γ₂ T₂)
Pcons₀ Γ T (γ₁ , t₁) (γ₂ , t₂) = Σ {i} {i} (Γ γ₁ γ₂) (λ γ → T γ t₁ t₂)

Pcons₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → PType₁ Γ T₁ T₂
  → PCtx (cons₁ Γ₁ T₁) (cons₁ Γ₂ T₂)
Pcons₁ Γ T (γ₁ , t₁) (γ₂ , t₂) = Σ {i} {i} (Γ γ₁ γ₂) (λ γ → T γ t₁ t₂)

-- Type constructors
PU₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → PType₁ Γ U₀ U₀
PU₀ γ A B = A → B → Set₁ -- is it correct that this is Set₁? Corresponds with Set₂ in def of PType₁

PΠ₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂ B₁ B₂}
  → (A : PType₀ Γ A₁ A₂) → (B : PType₀ (Pcons₀ Γ A) B₁ B₂) → PType₀ Γ (Π₀ A₁ B₁) (Π₀ A₂ B₂)
PΠ₀ {Γ₁} {Γ₂} {Γ} {A₁} {A₂} A B {γ₁} {γ₂} γ f₁ f₂
  = {a₁ : A₁ γ₁} → {a₂ : A₂ γ₂} → (aR : A γ a₁ a₂) → B (γ , aR) (f₁ a₁) (f₂ a₂)

PΠ₁ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂ B₁ B₂}
  → (A : PType₁ Γ A₁ A₂) → (B : PType₁ (Pcons₁ Γ A) B₁ B₂) → PType₁ Γ (Π₁ A₁ B₁) (Π₁ A₂ B₂)
PΠ₁ {Γ₁} {Γ₂} {Γ} {A₁} {A₂} A B {γ₁} {γ₂} γ f₁ f₂
  = {a₁ : A₁ γ₁} → {a₂ : A₂ γ₂} → (aR : A γ a₁ a₂) → B (γ , aR) (f₁ a₁) (f₂ a₂)

PweakenT₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂ T₁ T₂} → {A : PType₀ Γ A₁ A₂}
  → PType₀ Γ T₁ T₂ → PType₀ (Pcons₀ Γ A) (weakenT₀ T₁) (weakenT₀ T₂)
PweakenT₀ T = λ γ → T (proj₁ γ)

PweakenT₁ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂ T₁ T₂} → {A : PType₁ Γ A₁ A₂}
  → PType₁ Γ T₁ T₂ → PType₁ (Pcons₁ Γ A) (weakenT₁ T₁) (weakenT₁ T₂)
PweakenT₁ T = λ γ → T (proj₁ γ)

-- sort of weird that PU₀ needs the {Γ} argument below.
PvarT₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → PType₀ (Pcons₁ Γ (PU₀ {_} {_} {Γ})) varT₀ varT₀
PvarT₀ = proj₂

Psub₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂ T₁ T₂ e₁ e₂} → {A : PType₀ Γ A₁ A₂}
  → PType₀ (Pcons₀ Γ A) T₁ T₂ → PTerm₀ Γ A e₁ e₂ → PType₀ Γ (sub₀ T₁ e₁) (sub₀ T₂ e₂)
Psub₀ T e = λ γ → T (γ , e γ)

-- Term constructors

Plambda₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂} → {A : PType₀ Γ A₁ A₂}
  → ∀{B₁ B₂} → {B : PType₀ (Pcons₀ Γ A) B₁ B₂}
  → ∀{e₁ e₂} → PTerm₀ (Pcons₀ Γ A) B e₁ e₂ → PTerm₀ Γ (PΠ₀ {_} {_} {Γ} A B) (lambda₀ e₁) (lambda₀ e₂)
Plambda₀ e = λ γ a → e (γ , a)

Plambda₁ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂} → {A : PType₁ Γ A₁ A₂}
  → ∀{B₁ B₂} → {B : PType₁ (Pcons₁ Γ A) B₁ B₂}
  → ∀{e₁ e₂} → PTerm₁ (Pcons₁ Γ A) B e₁ e₂ → PTerm₁ Γ (PΠ₁ {_} {_} {Γ} A B) (lambda₁ e₁) (lambda₁ e₂)
Plambda₁ e = λ γ a → e (γ , a)

-- note the crazy implicit arguments needed for Psub₀. I have no explanation for why some things are needed and others aren't. Then again, I havent thought about it.
Papp₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂} → {A : PType₀ Γ A₁ A₂}
  → ∀{B₁ B₂} → {B : PType₀ (Pcons₀ Γ A) B₁ B₂}
  → ∀{e₁ e₂ e₁' e₂'} → PTerm₀ Γ (PΠ₀ {_} {_} {Γ} A B) e₁ e₂ → (x : PTerm₀ Γ A e₁' e₂')
  → PTerm₀ Γ (Psub₀ {_} {_} {Γ} {A₁} {A₂} {_} {_} {e₁'} {e₂'} {A} B x) (app₀ e₁ e₁') (app₀ e₂ e₂')
Papp₀ e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

Pweaken₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{A₁ A₂ T₁ T₂} → {A : PType₀ Γ A₁ A₂}
  → {T : PType₀ Γ T₁ T₂} → ∀{e₁ e₂}
  → PTerm₀ Γ T e₁ e₂ → PTerm₀ (Pcons₀ Γ A) (PweakenT₀ {_} {_} {Γ} {_} {_} {_} {_} {A} T) (weaken₀ e₁) (weaken₀ e₂)
Pweaken₀ e = λ γ → e (proj₁ γ)

Pvar₀ : ∀{Γ₁ Γ₂} → {Γ : PCtx Γ₁ Γ₂} → ∀{T₁ T₂} → {T : PType₀ Γ T₁ T₂}
  → PTerm₀ (Pcons₀ Γ T) (PweakenT₀ {_} {_} {Γ} {_} {_} {_} {_} {T} T) var₀ var₀
Pvar₀ = proj₂


-- EXAMPLE:
-- λ X x . x : (X : Set) → X → X
PexType : PType₁ Pnil exType exType
PexType = PΠ₁ PU₀ (PΠ₁ PvarT₀ (PweakenT₁ PvarT₀))

-- PexTerm : Term₁ nil exType
-- PexTerm = lambda₁ (lambda₀ var₀) -- note some shenanigans with type level cumulativity combined with it being a shallow embedding, to Type₀ < Type₁ essentially.
