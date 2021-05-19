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

The goal of this file is to try to build an Exp type where the terms that are built
simultaneously build an Agda value corresponding with the term, but also build a
parametricity value. Bonus if I can write a constructor "parametricity" which moves
the value from the parametricity side to the value side.

IDEAS:
-- Probably I will need the parametricity value to be under a Maybe so that after the
  parametricity constructor, the resulting term can just have "nothing" in the
  parametricity spot. So won't be able to use parametricity on parametricity.

-}

module Exp-with-value-AND-param where

----------------------------------------------
-- I can't figure out how to import files in Agda, so the following is copied from
-- parametricity-shallow-embedding.agda

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
Type₂ : Ctx → Set j
Type₂ Γ = Γ → Set₂

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

U₁ : ∀{Γ} → Type₂ Γ
U₁ = λ γ → Set₁

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

app₁  : {Γ : Ctx} → {A : Type₁ Γ} → {B : Type₁ (cons₁ Γ A)}
  → Term₁ Γ (Π₁ A B) → (x : Term₁ Γ A) → Term₁ Γ (sub₁ B x)
app₁ e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

weaken₀ : {Γ : Ctx} → {A T : Type₀ Γ}
  → Term₀ Γ T → Term₀ (cons₀ Γ A) (weakenT₀ T)
weaken₀ e = λ γ → e (proj₁ γ)

weaken₁ : {Γ : Ctx} → {A T : Type₁ Γ}
  → Term₁ Γ T → Term₁ (cons₁ Γ A) (weakenT₁ T)
weaken₁ e = λ γ → e (proj₁ γ)

var₀ : {Γ : Ctx} → {T : Type₀ Γ}
  → Term₀ (cons₀ Γ T) (weakenT₀ T)
var₀ = proj₂

var₁ : {Γ : Ctx} → {T : Type₁ Γ}
  → Term₁ (cons₁ Γ T) (weakenT₁ T)
var₁ = proj₂

-- typeToTerm₀ : ∀{Γ} → Type₀ Γ → Term₁ Γ U₀
-- typeToTerm₀ T = T

-- EXAMPLE:
-- λ X x . x : (X : Set) → X → X
exType : Type₁ nil
exType = Π₁ U₀ (Π₀ varT₀ (weakenT₀ varT₀))

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

PType₂ : {Γ₁ Γ₂ : Ctx} → PCtx Γ₁ Γ₂ → (T₁ : Type₂ Γ₁) → (T₂ : Type₂ Γ₂) → Set j
PType₂ {Γ₁} {Γ₂} Γ T₁ T₂ = {γ₁ : Γ₁} → {γ₂ : Γ₂} → Γ γ₁ γ₂ → T₁ γ₁ → T₂ γ₂ → Set₃

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

-- Note that it would be desirable to have the Γ argument implicit, but it doesn't work.
PU₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → PType₁ Γ U₀ U₀
PU₀ Γ γ A B = A → B → Set₁ -- is it correct that this is Set₁? Corresponds with Set₂ in def of PType₁

PU₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → PType₂ Γ U₁ U₁
PU₁ Γ γ A B = A → B → Set₂

-- Note that it would be desirable to have the Γ argument implicit, but it doesn't work.
PΠ₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ B₁ B₂}
  → (A : PType₀ Γ A₁ A₂) → (B : PType₀ (Pcons₀ Γ A) B₁ B₂) → PType₀ Γ (Π₀ A₁ B₁) (Π₀ A₂ B₂)
PΠ₀ {Γ₁} {Γ₂} Γ {A₁} {A₂} A B {γ₁} {γ₂} γ f₁ f₂
  = {a₁ : A₁ γ₁} → {a₂ : A₂ γ₂} → (aR : A γ a₁ a₂) → B (γ , aR) (f₁ a₁) (f₂ a₂)

-- Note that it would be desirable to have the Γ argument implicit, but it doesn't work.
PΠ₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ B₁ B₂}
  → (A : PType₁ Γ A₁ A₂) → (B : PType₁ (Pcons₁ Γ A) B₁ B₂) → PType₁ Γ (Π₁ A₁ B₁) (Π₁ A₂ B₂)
PΠ₁ {Γ₁} {Γ₂} Γ {A₁} {A₂} A B {γ₁} {γ₂} γ f₁ f₂
  = {a₁ : A₁ γ₁} → {a₂ : A₂ γ₂} → (aR : A γ a₁ a₂) → B (γ , aR) (f₁ a₁) (f₂ a₂)

-- note that it would be desirable to have Γ and A be implicit, but Agda can't infer things without them later on.
PweakenT₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂} → (A : PType₀ Γ A₁ A₂)
  → PType₀ Γ T₁ T₂ → PType₀ (Pcons₀ Γ A) (weakenT₀ T₁) (weakenT₀ T₂)
PweakenT₀ Γ A T = λ γ → T (proj₁ γ)

PweakenT₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂} → (A : PType₁ Γ A₁ A₂)
  → PType₁ Γ T₁ T₂ → PType₁ (Pcons₁ Γ A) (weakenT₁ T₁) (weakenT₁ T₂)
PweakenT₁ Γ A T = λ γ → T (proj₁ γ)

PvarT₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → PType₀ (Pcons₁ Γ (PU₀ Γ)) varT₀ varT₀
PvarT₀ Γ = proj₂

-- note that it would be desirable to have Γ and A be implicit, but Agda can't infer things without them later on.
Psub₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂ e₁ e₂} → (A : PType₀ Γ A₁ A₂)
  → PType₀ (Pcons₀ Γ A) T₁ T₂ → PTerm₀ Γ A e₁ e₂ → PType₀ Γ (sub₀ T₁ e₁) (sub₀ T₂ e₂)
Psub₀ Γ A T e = λ γ → T (γ , e γ)

Psub₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂ e₁ e₂} → (A : PType₁ Γ A₁ A₂)
  → PType₁ (Pcons₁ Γ A) T₁ T₂ → PTerm₁ Γ A e₁ e₂ → PType₁ Γ (sub₁ T₁ e₁) (sub₁ T₂ e₂)
Psub₁ Γ A T e = λ γ → T (γ , e γ)

-- Term constructors

Plambda₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂} → (A : PType₀ Γ A₁ A₂)
  → ∀{B₁ B₂} → (B : PType₀ (Pcons₀ Γ A) B₁ B₂)
  → ∀{e₁ e₂} → PTerm₀ (Pcons₀ Γ A) B e₁ e₂ → PTerm₀ Γ (PΠ₀ Γ A B) (lambda₀ e₁) (lambda₀ e₂)
Plambda₀ Γ A B e = λ γ a → e (γ , a)

Plambda₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂} → (A : PType₁ Γ A₁ A₂)
  → ∀{B₁ B₂} → (B : PType₁ (Pcons₁ Γ A) B₁ B₂)
  → ∀{e₁ e₂} → PTerm₁ (Pcons₁ Γ A) B e₁ e₂ → PTerm₁ Γ (PΠ₁ Γ A B) (lambda₁ e₁) (lambda₁ e₂)
Plambda₁ Γ A B e = λ γ a → e (γ , a)

Papp₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂} → {A : PType₀ Γ A₁ A₂}
  → ∀{B₁ B₂} → (B : PType₀ (Pcons₀ Γ A) B₁ B₂)
  → ∀{e₁ e₂ e₁' e₂'} → PTerm₀ Γ (PΠ₀ Γ A B) e₁ e₂ → (x : PTerm₀ Γ A e₁' e₂')
  → PTerm₀ Γ (Psub₀ Γ A B x) (app₀ e₁ e₁') (app₀ e₂ e₂')
Papp₀ Γ B e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

Papp₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂} → {A : PType₁ Γ A₁ A₂}
  → ∀{B₁ B₂} → (B : PType₁ (Pcons₁ Γ A) B₁ B₂)
  → ∀{e₁ e₂ e₁' e₂'} → PTerm₁ Γ (PΠ₁ Γ A B) e₁ e₂ → (x : PTerm₁ Γ A e₁' e₂')
  → PTerm₁ Γ (Psub₁ Γ A B x) (app₁ e₁ e₁') (app₁ e₂ e₂')
Papp₁ Γ B e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

Pweaken₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂} → (A : PType₀ Γ A₁ A₂)
  → (T : PType₀ Γ T₁ T₂) → ∀{e₁ e₂}
  → PTerm₀ Γ T e₁ e₂ → PTerm₀ (Pcons₀ Γ A) (PweakenT₀ Γ A T) (weaken₀ e₁) (weaken₀ e₂)
Pweaken₀ Γ A T e = λ γ → e (proj₁ γ)

Pweaken₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂} → (A : PType₁ Γ A₁ A₂)
  → (T : PType₁ Γ T₁ T₂) → ∀{e₁ e₂}
  → PTerm₁ Γ T e₁ e₂ → PTerm₁ (Pcons₁ Γ A) (PweakenT₁ Γ A T) (weaken₁ e₁) (weaken₁ e₂)
Pweaken₁ Γ A T e = λ γ → e (proj₁ γ)

Pvar₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → (T : PType₀ Γ T₁ T₂)
  → PTerm₀ (Pcons₀ Γ T) (PweakenT₀ Γ T T) var₀ var₀
Pvar₀ Γ T = proj₂

Pvar₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → (T : PType₁ Γ T₁ T₂)
  → PTerm₁ (Pcons₁ Γ T) (PweakenT₁ Γ T T) var₁ var₁
Pvar₁ Γ T = proj₂

--------------------------------------------------------------------------------

PTypeToType∅ : {T : Type₀ nil}
  → PType₀ Pnil T T → Type₁ nil
PTypeToType∅ {T} PT = λ tt → (x y : T tt) → PT tt x y

PTypeToType : {Γ : Ctx} → {PΓ : PCtx Γ Γ} → {T : Type₀ Γ}
  → PType₀ PΓ T T → Type₀ Γ
PTypeToType PT = λ γ → {! (Pγ : )  !}

data Context : (aΓ : Ctx) → PCtx aΓ aΓ → Set j where
  ∅ : Context nil Pnil
  -- _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ {i} {i} aΓ T)
  Econs₀ : ∀{aΓ PΓ} → (ctx : Context aΓ PΓ) → (T : Type₀ aΓ)
    → (PT : PType₀ PΓ T T)
    → Context (cons₀ aΓ T) (Pcons₀ PΓ PT)
  Econs₁ : ∀{aΓ PΓ} → (ctx : Context aΓ PΓ) → (T : Type₁ aΓ)
    → (PT : PType₁ PΓ T T)
    → Context (cons₁ aΓ T) (Pcons₁ PΓ PT)

data InCtx₀ : ∀{aΓ PΓ} → (Γ : Context aΓ PΓ) → (T : Type₀ aΓ)
  → (PT : PType₀ PΓ T T) → (a : Term₀ aΓ T) → (PTerm₀ PΓ PT a a)
  → Set j where
  same : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {T : Type₀ aΓ} → {PT : PType₀ PΓ T T}
    → InCtx₀ (Econs₀ Γ T PT) (weakenT₀ T) (PweakenT₀ PΓ PT PT) var₀ (Pvar₀ PΓ PT)
  next : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {A T : Type₀ aΓ}
    → {PA : PType₀ PΓ A A} → {PT : PType₀ PΓ T T}
    → {a : Term₀ aΓ T} → {Pa : PTerm₀ PΓ PT a a}
    → InCtx₀ Γ T PT a Pa
    → InCtx₀ (Econs₀ Γ A PA) (weakenT₀ T) (PweakenT₀ PΓ PA PT)
        (weaken₀ a) (Pweaken₀ PΓ PA PT Pa)

data InCtx₁ : ∀{aΓ PΓ} → (Γ : Context aΓ PΓ) → (T : Type₁ aΓ)
  → (PT : PType₁ PΓ T T) → (a : Term₁ aΓ T) → (PTerm₁ PΓ PT a a)
  → Set j where
  same : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {T : Type₁ aΓ} → {PT : PType₁ PΓ T T}
    → InCtx₁ (Econs₁ Γ T PT) (weakenT₁ T) (PweakenT₁ PΓ PT PT) var₁ (Pvar₁ PΓ PT)
  next : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {A T : Type₁ aΓ}
    → {PA : PType₁ PΓ A A} → {PT : PType₁ PΓ T T}
    → {a : Term₁ aΓ T} → {Pa : PTerm₁ PΓ PT a a}
    → InCtx₁ Γ T PT a Pa
    → InCtx₁ (Econs₁ Γ A PA) (weakenT₁ T) (PweakenT₁ PΓ PA PT)
        (weaken₁ a) (Pweaken₁ PΓ PA PT Pa)

data Exp₀ : ∀{aΓ PΓ} → (Γ : Context aΓ PΓ)
  → (T : Type₀ aΓ) → (PT : PType₀ PΓ T T)
  → (a : Term₀ aΓ T) → PTerm₀ PΓ PT a a  → Set j where
  ELambda₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {A : Type₀ aΓ} → {B : Type₀ (cons₀ aΓ A)}
    → {PA : PType₀ PΓ A A} → {PB : PType₀ (Pcons₀ PΓ PA) B B}
    → {a : Term₀ (cons₀ aΓ A) B} → {Pa : PTerm₀ (Pcons₀ PΓ PA) PB a a}
    → Exp₀ (Econs₀ Γ A PA) B PB a Pa
    → Exp₀ Γ (Π₀ A B) (PΠ₀ PΓ PA PB) (lambda₀ a) (Plambda₀ PΓ PA PB Pa)
  EVar₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {T : Type₀ aΓ} → {a : Term₀ aΓ T}
    → {PT : PType₀ PΓ T T} → {Pa : PTerm₀ PΓ PT a a}
    → InCtx₀ Γ T PT a Pa → Exp₀ Γ T PT a Pa
  EApp₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → {A : Type₀ aΓ} → {B : Type₀ (cons₀ aΓ A)}
    → {PA : PType₀ PΓ A A} → {PB : PType₀ (Pcons₀ PΓ PA) B B}
    → {x : Term₀ aΓ (Π₀ A B)} → {Px : PTerm₀ PΓ (PΠ₀ PΓ PA PB) x x}
    → {y : Term₀ aΓ A} → {Py : PTerm₀ PΓ PA y y}
    → Exp₀ Γ (Π₀ A B) (PΠ₀ PΓ PA PB) x Px
    → Exp₀ Γ A PA y Py
    → Exp₀ Γ (sub₀ B y) (Psub₀ PΓ PA PB Py) (app₀ x y) (Papp₀ PΓ PB Px Py)

data Exp₁ : ∀{aΓ PΓ} → (Γ : Context aΓ PΓ)
  → (T : Type₁ aΓ) → (PT : PType₁ PΓ T T)
  → (a : Term₁ aΓ T) → PTerm₁ PΓ PT a a  → Set j where
  ELambda₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {A : Type₁ aΓ} → {B : Type₁ (cons₁ aΓ A)}
    → {PA : PType₁ PΓ A A} → {PB : PType₁ (Pcons₁ PΓ PA) B B}
    → {a : Term₁ (cons₁ aΓ A) B} → {Pa : PTerm₁ (Pcons₁ PΓ PA) PB a a}
    → Exp₁ (Econs₁ Γ A PA) B PB a Pa
    → Exp₁ Γ (Π₁ A B) (PΠ₁ PΓ PA PB) (lambda₁ a) (Plambda₁ PΓ PA PB Pa)
  EVar₁ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {T : Type₁ aΓ} → {a : Term₁ aΓ T}
    → {PT : PType₁ PΓ T T} → {Pa : PTerm₁ PΓ PT a a}
    → InCtx₁ Γ T PT a Pa → Exp₁ Γ T PT a Pa
  parametricity : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → {T : Type₀ aΓ} → {PT : PType₀ PΓ T T} → {a : Term₀ aΓ T} → {Pa : PTerm₀ PΓ PT a a}
    → Exp₀ Γ T PT a Pa → Exp₁ Γ {! PT  !} {!   !} {!   !} {!   !}
  EApp₁ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → {A : Type₁ aΓ} → {B : Type₁ (cons₁ aΓ A)}
    → {PA : PType₁ PΓ A A} → {PB : PType₁ (Pcons₁ PΓ PA) B B}
    → {x : Term₁ aΓ (Π₁ A B)} → {Px : PTerm₁ PΓ (PΠ₁ PΓ PA PB) x x}
    → {y : Term₁ aΓ A} → {Py : PTerm₁ PΓ PA y y}
    → Exp₁ Γ (Π₁ A B) (PΠ₁ PΓ PA PB) x Px
    → Exp₁ Γ A PA y Py
    → Exp₁ Γ (sub₁ B y) (Psub₁ PΓ PA PB Py) (app₁ x y) (Papp₁ PΓ PB Px Py)
  EU₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → Exp₁ {aΓ} Γ U₁ PU₁ U₀ PU₀

-- Exp₁' : Exp₁ ∅ U₀ PU₀ → Set j
-- Exp₁' e = Exp₁ (type e) (Ptype e)

-- data Exp : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
--   → ((γ : aΓ) → T γ) → Set j where
--   ELambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a}
--     → Exp (Γ , A) B a → Exp Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
--   EVar : {aΓ : Set i} → {Γ : Context aΓ} → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
--     → (icx : InCtx Γ T a) → Exp {aΓ} Γ T a
--   EApp : {aΓ : Set i} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
--       → Exp Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Exp Γ A a₂)
--       → Exp Γ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))
--   EΠ₀ : {aΓ : Set i} → {Γ : Context aΓ} → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
--     → (A : Exp Γ (λ _ → Set) a₁)
--     → (B : Exp (Γ , (λ γ → a₁ γ)) (λ _ → Set) a₂)
--     → Exp Γ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
--   EU₀ : {aΓ : Set i} → {Γ : Context aΓ} → Exp {aΓ} Γ (λ _ → Set₁) (λ _ → Set₀)
