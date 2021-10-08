open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

{-

Alternate (from my perspective) definition of Sem
I think this might be the standard one?

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

forget1ren : ∀{Γ₁ Γ₂ T} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren ren x = ren (next x)

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

Sem : Ctx → Type → Set
Sem Γ (A ⇒ B) = Sem Γ A → Sem Γ B -- alternate form!
Sem Γ base = Nf Γ base

-- mutual
--   nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
--   nApp {_} {A ⇒ B} e = λ ren g → nApp (app (renNe ren e) (reify g))
--   nApp {_} {base} e = ne e
--
--   reify : ∀{Γ T} → Sem Γ T → Nf Γ T
--   reify {Γ} {A ⇒ B} g = lambda (reify (g (forget1ren idRen) (nApp (var same))))
--   reify {Γ} {base} g = g

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → Sem Γ₂ T -- if Sub instead outputted a GSem, could renSem,renNf, and renNe be avoided?

idSub : ∀{Γ} → Sub Γ Γ
idSub x = {! x  !}

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

renSem : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Sem Γ₁ T → Sem Γ₂ T
-- renSem {_} {_} {A ⇒ B} ren e = λ ren₁ a → e (ren ∘ ren₁) a
renSem {_} {_} {A ⇒ B} ren e = λ a → {! e a  !}
renSem {_} {_} {base} ren e = renNf ren e

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR sub ren x = renSem ren (sub x)

append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → Sem Γ₂ A → Sub (Γ₁ , A) Γ₂
append1sub sub e same = e
append1sub sub e (next x) = sub x

eval : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → Sem Γ₂ T
eval (var x) sub = sub x
-- eval (lambda e) sub = λ ren a → eval e (append1sub (transSR sub ren) a)
eval (lambda e) sub = {!   !}
-- eval (app e₁ e₂) sub = (eval e₁ sub) idRen (eval e₂ sub)
eval (app e₁ e₂) sub = {!   !}
eval ⋆ sub = ⋆

-- normalize : ∀{Γ T} → Exp Γ T → Nf Γ T
-- normalize e = reify (eval e idSub)
