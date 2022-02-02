open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

{-

The concept of this is that expressions should always have a unique context that
they are in, and therefore renaming is unecessary.
Specifically, any variables not used can't be in the context, and they should appear in
the order that they are first used.

Unlike linear or affine types, this should NOT restrict which programs can be written.
Like normal forms, it makes it so a given program only has exactly one representation.

My hope is that this will simplify NbE because renamings never do anything.


Maybe a better representation is for contexts to have a variable one time
per use. Now that I think about it, I think that connor mcbride had something
about a variable representation like this.

-}

data Type : Set where
  _⇒_ : Type → Type → Type
  base : Type

infixr 10 _⇒_

data Ctx : Set where
  ∅ : Ctx
  -- _,_ : Ctx → Type → Ctx
  app : Ctx → Ctx → Ctx
  var : Type → Ctx

data Positions : Ctx → Type → Set where
  -- var : ∀{T} → Positions (var T) T
  var : {T : Type} → Positions ∅ T
  app : ∀{Γ₁ Γ₂ T}
      → Positions Γ₁ T → Positions Γ₂ T → Positions (app Γ₁ Γ₂) T
  ∅ : ∀{Γ} → {T : Type} → Positions Γ T -- does not appear

-- should be a relation? TODO
addInPositions : ∀{T} → (Γ : Ctx) → Positions Γ T → Ctx
addInPositions ∅ (var {T}) = var T
addInPositions (app Γ₁ Γ₂) (app pos₁ pos₂)
  = app (addInPositions Γ₁ pos₁) (addInPositions Γ₂ pos₂)
addInPositions Γ ∅ = Γ

data Exp : Ctx → Type → Set where
  var : ∀{T} → Exp (var T) T -- By the time you use a variable, it is the only thing in scope.
  -- lambdas must input a set of positions where their variable is used. This is
  -- then merged with the existing context to get the new one.
  lambda : ∀{Γ A B} → (pos : Positions Γ A)
      → Exp (addInPositions Γ pos) B → Exp Γ (A ⇒ B)
  -- apps must have two contexts, which when merged give the full one
  app : ∀{Γ₁ Γ₂ A B} → Exp Γ₁ (A ⇒ B) → Exp Γ₂ A → Exp (app Γ₁ Γ₂) B
  ⋆ : Exp ∅ base

-- λ x . x : Base → Base
example1 : Exp ∅ (base ⇒ base)
example1 = lambda var var

example2 : Exp ∅ (base ⇒ base)
example2 = lambda ∅ ⋆

mutual
  data Ne : Ctx → Type → Set where
    var : ∀{T} → Ne (var T) T -- By the time you use a variable, it is the only thing in scope.
    app : ∀{Γ₁ Γ₂ A B} → Ne Γ₁ (A ⇒ B) → Nf Γ₂ A → Ne (app Γ₁ Γ₂) B
    ⋆ : Ne ∅ base

  data Nf : Ctx → Type → Set where
    lambda : ∀{Γ A B} → (pos : Positions Γ A)
        → Nf (addInPositions Γ pos) B → Nf Γ (A ⇒ B)
    ne : ∀{Γ} → Ne Γ base → Nf Γ base -- the fact that its only base enforces expanded η form. The above version would also typecheck just fine though.


Sem : Ctx → Type → Set
Sem Γ (A ⇒ B) = ∀{Γ'} → Ren Γ Γ' → Sem Γ' A → Sem Γ' B -- alternate form!
Sem Γ base = Ne Γ base -- used to be Nf, but can be Ne!
{-

mutual
  nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
  nApp {_} {A ⇒ B} e = λ ren g → nApp  (app (renNe ren e) (reify g))
  nApp {_} {base} e = e

  reify : ∀{Γ T} → Sem Γ T → Nf Γ T
  reify {Γ} {A ⇒ B} g = lambda (reify {Γ , A} (g {Γ , A} (forget1ren idRen) (nApp (var same))))
  reify {Γ} {base} g = ne g

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → Sem Γ₂ T -- if Sub instead outputted a GSem, could renSem,renNf, and renNe be avoided?

idSub : ∀{Γ} → Sub Γ Γ
idSub x = nApp (var x)

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

renSem : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Sem Γ₁ T → Sem Γ₂ T
renSem {_} {_} {A ⇒ B} ren e = λ ren₁ a → e (ren ∘ ren₁) a
renSem {_} {_} {base} ren e = renNe ren e

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR sub ren x = renSem ren (sub x)

append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → Sem Γ₂ A → Sub (Γ₁ , A) Γ₂
append1sub sub e same = e
append1sub sub e (next x) = sub x

eval : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → Sem Γ₂ T
eval (var x) sub = sub x
-- eval (lambda e) sub = λ a → eval e (append1sub sub a)
eval (lambda e) sub = λ ren a → eval e (append1sub (transSR sub ren) a)
-- eval (app e₁ e₂) sub = (eval e₁ sub) (λ ren₁ → eval e₂ (transSR sub ren₁))
eval (app e₁ e₂) sub = (eval e₁ sub) idRen (eval e₂ sub)
eval ⋆ sub = ⋆

normalize : ∀{Γ T} → Exp Γ T → Nf Γ T
-- normalize e = reify (λ ren → eval e (transSR idSub ren))
normalize e = reify (eval e idSub)

-- some examples to test it out:

e1 : Exp ∅ base
e1 = app (lambda (var same)) ⋆

test1 : normalize e1 ≡ ne ⋆
test1 = refl

e2 : Exp ∅ base -- (λ x . x ⋆) (λ x . x)
e2 = app (lambda (app (var same) ⋆)) (lambda (var same))

test2 : normalize e2 ≡ ne ⋆
test2 = refl

e3 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) ⋆
e3 = lambda (app (lambda (var same)) ⋆)

test3 : normalize e3 ≡ lambda (ne ⋆)
test3 = refl

e4 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) x
e4 = lambda (app (lambda (var same)) (var same))

test4 : normalize e4 ≡ lambda (ne (var same))
test4 = refl
-}
