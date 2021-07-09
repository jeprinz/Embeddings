{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

{-

Implementation of standard Normalization by Evaluation for Simply Typed
Lambda Calculus is Agda. Granted, maybe the variable names aren't standard.

-}

data Type : Set where
  _⇒_ : Type → Type → Type
  base : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data InCtx : (Γ : Ctx) → Type → Set where
  same : ∀{Γ T} → InCtx (Γ , T) T
  next : ∀{Γ T A} → InCtx Γ A → InCtx (Γ , T) A

data Exp : Ctx → Type → Set where
  var : ∀{Γ T} → (icx : InCtx Γ T) → Exp Γ T
  lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  ⋆ : ∀{Γ} → Exp Γ base

mutual
  data Ne : Ctx → Type → Set where
    var : ∀{Γ T} → (icx : InCtx Γ T) → Ne Γ T
    app : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

  data Nf : Ctx → Type → Set where
    lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    -- ne : ∀{Γ T} → Ne Γ T → Nf Γ T
    ne : ∀{Γ} → Ne Γ base → Nf Γ base -- the fact that its only base enforces expanded η form. The above version would also typecheck just fine though.
    ⋆ : ∀{Γ} → Nf Γ base

Ren : Ctx → Ctx → Set
Ren Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → InCtx Γ₂ T

forget1ren : ∀{Γ₁ Γ₂ T} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren ren x = ren (next x)

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

append1ren : ∀{Γ Γ' T} → Ren Γ Γ' → Ren (Γ , T) (Γ' , T)
append1ren ren same = same
append1ren ren (next x) = next (ren x)
mutual
  renNe : ∀{Γ Γ' T} → Ren Γ Γ' → Ne Γ T → Ne Γ' T
  renNf : ∀{Γ Γ' T} → Ren Γ Γ' → Nf Γ T → Nf Γ' T
  renNe ren (var icx) = var (ren icx)
  renNe ren (app e₁ e₂) = app (renNe ren e₁) (renNf ren e₂)
  renNf ren (lambda e) = lambda (renNf (append1ren ren) e)
  renNf ren (ne e) = ne (renNe ren e)
  renNf ren ⋆ = ⋆

Sem : Set → Type → Set₁
Sem X (A ⇒ B) = {X' : Set} → (X → X') → Sem X' A → Sem X' B
Sem X base = X -- X is Nf Γ base

mutual
  nApp : ∀{Γ T} → Ne Γ T → Sem (Nf Γ base) T
  nApp {_} {A ⇒ B} e = λ ren g → {! nApp  !}
  nApp {_} {base} e = ne e
  -- nApp {_} {A ⇒ B} e = λ ren g → nApp (app (renNe ren e) (reify g))
  -- nApp {_} {base} e = ne e

  nApp2 : ∀{Γ T X} → Ne Γ T → (Nf Γ base → X) → Sem X T
  nApp2 {_} {A ⇒ B} e f
    = λ ren g → nApp2 (nApp2 (app {! e  !} {!  !} ) {!   !} ) {!   !}
  nApp2 {_} {base} e f = f (ne e)

  reify2 : ∀{Γ T X} → Sem X T → (X → Nf Γ base) → Nf Γ T
  reify2 {Γ} {A ⇒ B} g f = lambda (reify2 {!   !} {!   !} )
  reify2 {Γ} {base} g f = f g

  reify : ∀{Γ T} → Sem (Nf Γ base) T → Nf Γ T
  reify {Γ} {A ⇒ B} g = lambda (reify (g (renNf (forget1ren idRen)) (nApp (var same))))
  reify {Γ} {base} g = g
  -- reify {Γ} {A ⇒ B} g = lambda (reify (g (forget1ren idRen) (nApp (var same))))
  -- reify {Γ} {base} g = g

-- mutual
--   Sem : Set → Type → Set₁
--   Sem X (A ⇒ B) = GSem X A → Sem X B
--   Sem X base = X -- Nf Γ base
--
--   GSem : Set → Type → Set₁
--   GSem X T = {X' : Set} → (X → X') → Sem X' T
--
-- mutual
--   nApp : ∀{Γ T} → Ne Γ T → Sem (Nf Γ base) T
--   nApp {_} {A ⇒ B} e = λ g → nApp (app e {! reify g  !} )
--   nApp {_} {base} e = ne e
--
--   reify : ∀{Γ T} → GSem (Nf Γ base) T → Nf Γ T
--   reify {Γ} {A ⇒ B} g
--     = lambda (reify λ ren → g {!   !} {!   !} )
--   reify {Γ} {base} g = {!   !}
{-

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → GSem Γ₂ T

idSub : ∀{Γ} → Sub Γ Γ
idSub x ren = nApp (var (ren x))

-- liftSub : ∀{Γ₁ Γ₂ T} → Sub Γ₁ Γ₂ → Sub (Γ₁ , T) (Γ₂ , T)
-- liftSub sub same ren = nApp (var (ren same))
-- liftSub sub (next x) ren = sub x (forget1ren ren)

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR sub ren x ren₂ = sub x (ren ∘ ren₂)

append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → GSem Γ₂ A → Sub (Γ₁ , A) Γ₂
append1sub sub e same ren = e ren
append1sub sub e (next x) ren = sub x ren

eval : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → Sem Γ₂ T
eval (var x) sub = sub x idRen
eval (lambda e) sub = λ a → eval e (append1sub sub a)
eval (app e₁ e₂) sub = (eval e₁ sub) (λ ren₁ → eval e₂ (transSR sub ren₁))
eval ⋆ sub = ⋆

normalize : ∀{Γ T} → Exp Γ T → Nf Γ T
normalize e = reify (λ ren → eval e (transSR idSub ren))

-- some examples to test it out:

e1 : Exp ∅ base
e1 = app (lambda (var same)) ⋆

test1 : normalize e1 ≡ ⋆
test1 = refl

e2 : Exp ∅ base -- (λ x . x ⋆) (λ x . x)
e2 = app (lambda (app (var same) ⋆ )) (lambda (var same))

test2 : normalize e2 ≡ ⋆
test2 = refl

e3 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) ⋆
e3 = lambda (app (lambda (var same)) ⋆)

test3 : normalize e3 ≡ lambda ⋆
test3 = refl

e4 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) x
e4 = lambda (app (lambda (var same)) (var same))

test4 : normalize e4 ≡ lambda (ne (var same))
test4 = refl
-}
