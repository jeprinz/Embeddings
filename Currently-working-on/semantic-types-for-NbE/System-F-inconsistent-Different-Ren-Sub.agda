open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Function

data TCtx : Set -- where
data TVar : TCtx → Set -- where
data SemT : TCtx → Set -- where
data Ctx : TCtx → Set -- where
data Var : ∀{Δ} → Ctx Δ → SemT Δ → Set -- where
data Nf : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where
data Ne : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where

TRen : TCtx → TCtx → Set
TRen Δ₁ Δ₂ = TVar Δ₁ → TVar Δ₂

renSemT : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → SemT Δ₁ → SemT Δ₂

Ren : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set -- TODO: maybe this?
Ren tren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ (renSemT tren T)

TSub : TCtx → TCtx → Set
TSub Δ₁ Δ₂ = TVar Δ₁ → SemT Δ₂

-- Wait! I think that it should be possible to not have positivity check merely by
-- doing predicative system F. Because of separate Δ and Γ.
{-# NO_POSITIVITY_CHECK #-}
data SemT where
    all : ∀{Δ} → (∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ') → SemT Δ
    var : ∀{Δ} → TVar Δ → SemT Δ
    _⇒_ : ∀{Δ}
      → (∀{Δ'} → TRen Δ Δ' → SemT Δ')
      → (∀{Δ'} → TRen Δ Δ' → SemT Δ')
      → SemT Δ

Sem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
-- Sem Δ (all T) Γ = ∀{Δ'} → (tren : TRen Δ Δ') → (a : SemT Δ') -- how does this relate to TRen in all constructor???
--   → Sem Δ' (T tren a) (renTCtx tren Γ)
Sem Δ (all T) Γ = ∀{Δ' Γ'} → (tren : TRen Δ Δ') → Ren tren Γ Γ'
  → (a : SemT Δ') → Sem Δ' (T tren a) Γ'
-- Sem Δ (A ⇒ B) Γ = ∀{Γ'} → Ren Γ Γ' → Sem Δ A Γ' → Sem Δ B Γ' -- maybe need Δ renaming as well????
Sem Δ (A ⇒ B) Γ = ∀{Δ' Γ'} → (tren : TRen Δ Δ') → Ren tren Γ Γ'
  → Sem Δ' (A tren) Γ' → Sem Δ' (B tren) Γ'
Sem Δ (var X) Γ = Nf Δ Γ (var X)

subSemT : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → SemT Δ₁ → SemT Δ₂

-- Ren : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set -- TODO: maybe this?
-- Ren tren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ (renSemT tren T)
Sub : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set
Sub tsub Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Sem _ (subSemT tsub T) Γ₂

data TCtx where
  ∅ : TCtx
  S : TCtx → TCtx

data TVar where
  same : ∀{Δ} → TVar Δ
  next : ∀{Δ} → TVar Δ → TVar (S Δ)

idSubT : ∀{Δ} → TSub Δ Δ
idSubT x = var x

idRenT : ∀{Δ} → TRen Δ Δ
idRenT x = x


renSemT tren (all T) = all (λ tren₂ X → T (tren₂ ∘ tren) X) -- huh? no recursion here?
renSemT tren (var x) = var (tren x)
renSemT tren (A ⇒ B) = (renSemT tren A) ⇒ (renSemT tren B)
-- renVar : ∀{Δ₁ Δ₂ Γ T} → (tren : TRen Δ₁ Δ₂) → Var {Δ₁} Γ T
-- --   → Var {Δ₂} Γ (renSemT tren T)
-- -- renVar tren x = ?

idRen : ∀{Δ} → {Γ : Ctx Δ} → Ren idRenT Γ Γ
idRen x = {! x  !}

{-
forget1renT : ∀{Δ₁ Δ₂} → TRen (S Δ₁) Δ₂ → TRen Δ₁ Δ₂
forget1renT ren x = ren (next x)

weaken1renT : ∀{Δ} → TRen Δ (S Δ)
weaken1renT x = next x

append1Tsub : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → SemT Δ₂ → TSub (S Δ₁) Δ₂
append1Tsub sub T same = T
append1Tsub sub T (next x) = sub x


renSem : ∀{Δ T} → {Γ₁ Γ₂ : Ctx Δ} → Ren Γ₁ Γ₂
  → Sem Δ T Γ₁ → Sem Δ T Γ₂
renSem {_} {all x} ren e = λ tren a → renSem {!   !} (e tren a)
renSem {_} {A ⇒ B} ren e = λ ren₁ a → e (ren₁ ∘ ren) a
renSem {_} {var x} ren e = {! e  !} -- define renNf and renNe for this!!!

transTSR : ∀{Δ₁ Δ₂ Δ₃} → TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
transTSR sub ren x = renSemT ren (sub x)


data Ctx where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{Δ} → (Γ : Ctx Δ) → SemT Δ → Ctx Δ

renTCtx ren ∅ = ∅
renTCtx ren (Γ , T) = renTCtx ren Γ , renSemT ren T

data Var where
  same : ∀{Δ Γ T} → Var {Δ} (Γ , T) T
  next : ∀{Δ Γ T A} → Var {Δ} Γ T → Var (Γ , A) T

data Type : TCtx → Set where
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ
  all : ∀{Δ} → Type (S Δ) → Type Δ
  var : ∀{Δ} → TVar Δ → Type Δ

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
  App : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Ne Δ Γ (all T) → (A : Type Δ) → Ne Δ Γ (T idRenT (evalT A idSubT))

data Nf where
  lambda : ∀{Δ Γ A B} → Nf Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
  Lambda : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Nf (S Δ) (renTCtx weaken1renT Γ) (T weaken1renT (var same))
    → Nf Δ Γ (all T)
  ne : ∀{Δ Γ x} → Ne Δ Γ (var x) → Nf Δ Γ (var x) -- restrict to eta-expanded forms

data Exp : (Δ : TCtx) → Ctx Δ → SemT Δ → Set where
  var : ∀{Δ Γ T} → Var {Δ} Γ T → Exp Δ Γ T
  app : ∀{Δ Γ A B} → Exp Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  lambda : ∀{Δ Γ A B} → Exp Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  App : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Exp Δ Γ (all T) → (A : Type Δ) → Exp Δ Γ (T idRenT (evalT A idSubT))
  Lambda : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Exp (S Δ) (renTCtx weaken1renT Γ) (T weaken1renT (var same))
    → Exp Δ Γ (all T)
append1sub : ∀{Δ A} → {Γ₁ Γ₂ : Ctx Δ} → Sub Γ₁ Γ₂ → Sem Δ A Γ₂ → Sub (Γ₁ , A) Γ₂
append1sub sub e same = e
append1sub sub e (next x) = sub x

transSR : ∀{Δ} → {Γ₁ Γ₂ Γ₃ : Ctx Δ} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
-- transSR sub ren x = renSem ren (sub x)
transSR sub ren x = {! sub x  !}

eval : ∀{Δ} → {Γ₁ Γ₂ : Ctx Δ} → {T : SemT Δ}
  → Exp Δ Γ₁ T → Sub Γ₁ Γ₂ → Sem Δ T Γ₂
eval (var x) sub = sub x
eval (app e₁ e₂) sub = (eval e₁ sub) idRen (eval e₂ sub)
eval (lambda e) sub = λ ren a → eval e (append1sub (transSR sub ren) a)
eval (App e T) sub = {! (eval e sub) idRenT (evalT T idSubT)  !}
eval (Lambda e) sub = λ tren a → {! eval e ?  !}
-}
