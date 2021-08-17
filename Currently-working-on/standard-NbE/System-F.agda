module System-F where

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive

{-

Comparing to Racket implementation, any parameters of Exp should be consistent with
that implementation, right? Because there are no parameters in untyped land.
What range of definitions could be seen as typed versions of that untyped code?

So the idea of this file is to just do a standard deep embedding with NbE just like
the one for STLC.

The problem I seem to be running into now has to do with the fact that there are
two contexts.
SEE: renTRen

I can also consider both GSem and standard Sem approaches, see NbE for STLC files.

-}

data TCtx : Set -- where
data Type : TCtx → Set -- where
data TVar : TCtx → Set -- where
data SemT : TCtx → Set -- where
data Ctx : TCtx → Set -- where
data Var : ∀{Δ} → Ctx Δ → Type Δ → Set -- where
data Nf : (Δ : TCtx) → Ctx Δ → Type Δ → Set -- where
data Ne : (Δ : TCtx) → Ctx Δ → Type Δ → Set -- where

TRen : TCtx → TCtx → Set
-- Ren : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set -- TODO: maybe this?
Ren : ∀{Δ} → Ctx Δ → Ctx Δ → Set

TRen Δ₁ Δ₂ = TVar Δ₁ → TVar Δ₂
Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ T

TSub : TCtx → TCtx → Set
TSub Δ₁ Δ₂ = TVar Δ₁ → SemT Δ₂

-- BRen : (Δ₁ Δ₂ : TCtx) → Ctx Δ₁ → Ctx Δ₂ → Set
-- BRen Δ₁ Δ₂ Γ₁ Γ₂ =

renTCtx : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂

-- Wait! I think that it should be possible to not have positivity check merely by
-- doing predicative system F. Because of separate Δ and Γ.

data TCtx where
  ∅ : TCtx
  S : TCtx → TCtx

data Type where
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ
  all : ∀{Δ} → Type (S Δ) → Type Δ
  var : ∀{Δ} → TVar Δ → Type Δ

{-# NO_POSITIVITY_CHECK #-}
data SemT where
    all : ∀{Δ} → (∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ') → SemT Δ
    var : ∀{Δ} → TVar Δ → SemT Δ
    _⇒_ : ∀{Δ} → SemT Δ → SemT Δ → SemT Δ

Sem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
Sem Δ (all T) Γ -- how does this relate to TRen in all constructor???
  -- = ∀{Δ'} → (tren : TRen Δ Δ') → (a : SemT Δ')
  -- → Sem Δ' (T tren a) (renTCtx tren Γ)
  -- = ∀{Δ' Γ'} → (tren : TRen Δ Δ') → (ren : Ren (renTCtx tren Γ) Γ')
    -- → (a : SemT Δ') → Sem Δ' (T tren a) Γ'
  = ∀{Δ' Γ'} → (ren : Ren Γ Γ') → (tren : TRen Δ Δ')
    → (a : SemT Δ') → Sem Δ' (T tren a) (renTCtx tren Γ')
Sem Δ (A ⇒ B) Γ = ∀{Γ'} → Ren Γ Γ' → Sem Δ A Γ' → Sem Δ B Γ' -- maybe need Δ renaming as well????
Sem Δ (var X) Γ = Nf Δ Γ (var X)

-- _∘_ : {i j k : Level} → {A : Set i} → {B : Set j} → {C : Set k}
--   → (A → B) → (B → C) → (A → C)
-- f ∘ g = λ x → (g (f x))

data TVar where
  same : ∀{Δ} → TVar Δ
  next : ∀{Δ} → TVar Δ → TVar (S Δ)

idSubT : ∀{Δ} → TSub Δ Δ
idSubT x = var x

idRenT : ∀{Δ} → TRen Δ Δ
idRenT x = x

idRen : ∀{Δ} → {Γ : Ctx Δ} → Ren Γ Γ
idRen x = x

forget1renT : ∀{Δ₁ Δ₂} → TRen (S Δ₁) Δ₂ → TRen Δ₁ Δ₂
forget1renT ren x = ren (next x)

weaken1renT : ∀{Δ} → TRen Δ (S Δ)
weaken1renT x = next x

append1Tsub : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → SemT Δ₂ → TSub (S Δ₁) Δ₂
append1Tsub sub T same = T
append1Tsub sub T (next x) = sub x


renSemT : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → SemT Δ₁ → SemT Δ₂
renSemT tren (all T) = all (λ tren₂ X → T (tren₂ ∘ tren) X) -- huh? no recursion here?
renSemT tren (var x) = var (tren x)
renSemT tren (A ⇒ B) = (renSemT tren A) ⇒ (renSemT tren B)

renType : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Type Δ₁ → Type Δ₂

transTSR : ∀{Δ₁ Δ₂ Δ₃} → TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
transTSR sub ren x = renSemT ren (sub x)


data Ctx where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{Δ} → (Γ : Ctx Δ) → Type Δ → Ctx Δ

-- renTCtx : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
renTCtx ren ∅ = ∅
renTCtx ren (Γ , T) = renTCtx ren Γ , renType ren T

data Var where
  same : ∀{Δ Γ T} → Var {Δ} (Γ , T) T
  next : ∀{Δ Γ T A} → Var {Δ} Γ T → Var (Γ , A) T

append1renT : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → TRen (S Δ₁) (S Δ₂)
append1renT ren same = same
append1renT ren (next x) = next (ren x)

-- TODO: should I implement this in terms of reifyT/evalT? Should I switch to GSem approach so this is irrelevant?
renType ren (A ⇒ B) = (renType ren A) ⇒ (renType ren B)
renType ren (all T) = all (renType (append1renT ren) T)
renType ren (var x) = var (ren x)

evalT : ∀{Δ₁ Δ₂} → Type Δ₁ → TSub Δ₁ Δ₂ → SemT Δ₂
evalT (A ⇒ B) sub = evalT A sub ⇒ evalT B sub
evalT (all T) sub = all (λ tren X → evalT T (append1Tsub (transTSR sub tren) X))
evalT (var x) sub = sub x

reifyT : ∀{Δ} → SemT Δ → Type Δ
reifyT (all T) = all (reifyT (T weaken1renT (var same)))
reifyT (var x) = var x
reifyT (A ⇒ B) = reifyT A ⇒ reifyT B

data Ne where
  var : ∀{Δ Γ T} → Var {Δ} Γ T → Ne Δ Γ T
  app : ∀{Δ Γ A B} → Ne Δ Γ (A ⇒ B) → Nf Δ Γ A → Ne Δ Γ B
  App : ∀{Δ Γ T}
    → Ne Δ Γ (all T) → (A : Type Δ)
    → Ne Δ Γ (reifyT (evalT T (append1Tsub idSubT (evalT A idSubT))))

data Nf where
  lambda : ∀{Δ Γ A B} → Nf Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
  Lambda : ∀{Δ Γ T}
    → Nf (S Δ) (renTCtx weaken1renT Γ) T
    → Nf Δ Γ (all T)
  ne : ∀{Δ Γ x} → Ne Δ Γ (var x) → Nf Δ Γ (var x) -- restrict to eta-expanded forms

-- IDEA: Exp parametrized by Type but Nf parametrized by SemT?

data Exp : (Δ : TCtx) → Ctx Δ → Type Δ → Set where
  var : ∀{Δ Γ T} → Var {Δ} Γ T → Exp Δ Γ T
  app : ∀{Δ Γ A B} → Exp Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  lambda : ∀{Δ Γ A B} → Exp Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  App : ∀{Δ Γ T}
    → Exp Δ Γ (all T) → (A : Type Δ)
    → Exp Δ Γ (reifyT (evalT T (append1Tsub idSubT (evalT A idSubT))))
  Lambda : ∀{Δ Γ T}
    → Exp (S Δ) (renTCtx weaken1renT Γ) T
    → Exp Δ Γ (all T)

append1ren : ∀{Δ} → {Γ₁ Γ₂ : Ctx Δ} → ∀{T} → Ren Γ₁ Γ₂ → Ren (Γ₁ , T) (Γ₂ , T)
append1ren ren same = same
append1ren ren (next x) = next (ren x)

renTRen : ∀{Δ₁ Δ₂ Γ₁ Γ₂} → (tren : TRen Δ₁ Δ₂)
  → Ren Γ₁ Γ₂ → Ren (renTCtx tren Γ₁) (renTCtx tren Γ₂)
renTRen tren ren x = {! x  !}


mutual
  renNf : ∀{Δ Γ₁ Γ₂ T} → (ren : Ren Γ₁ Γ₂) → Nf Δ Γ₁ T → Nf Δ Γ₂ T
  renNf ren (lambda e) = lambda (renNf (append1ren ren) e)
  renNf ren (Lambda e) = Lambda (renNf (renTRen weaken1renT ren) e)
  renNf ren (ne e) = ne (renNe ren e)

  renNe : ∀{Δ Γ₁ Γ₂ T} → (ren : Ren Γ₁ Γ₂) → Ne Δ Γ₁ T → Ne Δ Γ₂ T
  renNe ren (var x) = var (ren x)
  renNe ren (app e₁ e₂) = app (renNe ren e₁) (renNf ren e₂)
  renNe ren (App e A) = App (renNe ren e) A

renSem : ∀{Δ T} → {Γ₁ Γ₂ : Ctx Δ} → Ren Γ₁ Γ₂
  → Sem Δ T Γ₁ → Sem Δ T Γ₂
-- renSem {_} {all x} ren e = λ tren a → renSem (renTRen tren ren) (e tren a)
renSem {_} {all x} ren e = λ ren₂ tren a → (e (ren₂ ∘ ren) tren a)
renSem {_} {A ⇒ B} ren e = λ ren₁ a → e (ren₁ ∘ ren) a
renSem {_} {var x} ren e = renNf ren e

-- renidSemT≡ : ∀{Δ} → {T : SemT Δ} → renSemT idRenT T ≡ T
-- renidSemT≡ {_} {all T} = refl
-- renidSemT≡ {_} {var x} = refl
-- renidSemT≡ {_} {A ⇒ B} = cong₂ _⇒_ renidSemT≡ renidSemT≡

-- renidCtx≡ : ∀{Δ} → {Γ : Ctx Δ} → renTCtx idRenT Γ ≡ Γ
-- renidCtx≡ {_} {∅} = refl
-- renidCtx≡ {_} {Γ , T} = cong₂ _,_ renidCtx≡ renidSemT≡

Sub : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Sub Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Sem _ (evalT T idSubT) Γ₂
-- Sub Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Nf _ Γ₂ T

append1sub : ∀{Δ A} → {Γ₁ Γ₂ : Ctx Δ} → Sub Γ₁ Γ₂ → Sem Δ (evalT A idSubT) Γ₂ → Sub (Γ₁ , A) Γ₂
append1sub sub e same = e
append1sub sub e (next x) = sub x

transSR : ∀{Δ} → {Γ₁ Γ₂ Γ₃ : Ctx Δ} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR sub ren x = renSem ren (sub x)

subCtx : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
subCtx tsub ∅ = ∅
subCtx tsub (Γ , T) = subCtx tsub Γ , reifyT (evalT T tsub) -- subSemT tsub T

subVar : ∀{Δ₁ Δ₂ T} → {Γ : Ctx Δ₁} → (tsub : TSub Δ₁ Δ₂)
  → Var Γ T → Var (subCtx tsub Γ) (reifyT (evalT T tsub))
subVar tsub same = same
subVar tsub (next x) = next (subVar tsub x)
{-

mutual
  -- nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
  -- nApp {_} {A ⇒ B} e = λ ren g → nApp (app (renNe ren e) (reify g))
  -- nApp {_} {base} e = ne e
  nApp : ∀{Δ Γ T} → Ne Δ Γ T → Sem Δ T Γ
  nApp {_} {_} {all T} e = λ tren a → nApp (App {! e  !} (reifyT a))
  nApp {_} {_} {var x} e = ne e
  nApp {_} {_} {A ⇒ B} e = λ ren a → nApp (app {! renNe ren e  !} (reify a))

  -- reify : ∀{Γ T} → Sem Γ T → Nf Γ T
  -- reify {Γ} {A ⇒ B} g = lambda (reify (g (forget1ren idRen) (nApp (var same))))
  -- reify {Γ} {base} g = g
  reify : ∀{Δ Γ T} → Sem Δ T Γ → Nf Δ Γ T
  reify {_} {_} {all T} e = Lambda (reify (e weaken1renT {! T weaken1renT (var same)  !} ))
  reify {_} {_} {var x} e = e
  reify {_} {_} {A ⇒ B} e = lambda (reify (e {! forget1ren idRen  !} (nApp (var same))))

eval2 : ∀{Δ₁ Δ₂} → {Γ₁ : Ctx Δ₁} → {Γ₂ : Ctx Δ₂} → {T : SemT Δ₁}
  → (tsub : TSub Δ₁ Δ₂) → Sub (subCtx tsub Γ₁) Γ₂
  → Exp Δ₁ Γ₁ T → Sem Δ₂ (subSemT tsub T) Γ₂
eval2 tsub sub (var x) = sub (subVar tsub x)
eval2 tsub sub (app e₁ e₂) = (eval2 tsub sub e₁) idRen (eval2 tsub sub e₂)
eval2 tsub sub (lambda e) = λ ren a → eval2 tsub ((append1sub (transSR sub ren) a)) e
eval2 tsub sub (App {Δ} {Γ₁} {T} e A)
  = let a = (eval2 tsub sub e) idRenT (evalT A tsub)
    in {! a  !}
eval2 tsub sub (Lambda e)
  = λ tren a → eval2 (append1Tsub (transTSR tsub tren) a) {! sub  !} e
-}
