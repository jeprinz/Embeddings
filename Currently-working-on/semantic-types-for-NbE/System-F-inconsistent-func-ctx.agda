module System-F-inconsistent-func-ctx where

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-

Essientially, the idea is to use GSemT in the hopes that it will eliminate the need
to prove annoying sub and ren lemmas. I'm not sure if this is even true.
However, there is another issue of that reify and nApp must be parametrized by SemT
and NOT GSemT so that they can pattern match on it. So, we are left with:

Things which use SemT:
reify
nApp

Things which use GSemT:
Exp / Nf / Ne

But, reify needs to input SemT and output Nf????

-}

data TCtx : Set -- where
data TVar : TCtx → Set -- where
data SemT : TCtx → Set -- where
data Ctx : TCtx → Set -- where
data Var : ∀{Δ} → Ctx Δ → SemT Δ → Set -- where
data Nf : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where
data Ne : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where

TRen : TCtx → TCtx → Set
-- Ren : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set -- TODO: maybe this?
Ren : ∀{Δ} → Ctx Δ → Ctx Δ → Set

TRen Δ₁ Δ₂ = TVar Δ₁ → TVar Δ₂
Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ T

TSub : TCtx → TCtx → Set
TSub Δ₁ Δ₂ = TVar Δ₁ → SemT Δ₂

-- Wait! I think that it should be possible to not have positivity check merely by
-- doing predicative system F. Because of separate Δ and Γ.
{-# NO_POSITIVITY_CHECK #-}
data SemT where
    all : ∀{Δ} → (∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ') → SemT Δ
    var : ∀{Δ} → TVar Δ → SemT Δ
    _⇒_ : ∀{Δ} → SemT Δ → SemT Δ → SemT Δ

Sem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
Sem Δ (all T) Γ = ∀{Δ'} → (tren : TRen Δ Δ') → (a : SemT Δ') -- how does this relate to TRen in all constructor???
  → Sem Δ' (T tren a) {!   !} -- (renTCtx tren Γ)
Sem Δ (A ⇒ B) Γ = ∀{Γ'} → Ren Γ Γ' → Sem Δ A Γ' → Sem Δ B Γ' -- maybe need Δ renaming as well????
Sem Δ (var X) Γ = Nf Δ Γ (var X)

data TCtx where
  ∅ : TCtx
  S : TCtx → TCtx

-- GSemT
Type : TCtx → Set
Type Δ = ∀{Δ'} → TRen Δ Δ' → TSub Δ Δ' → SemT Δ'

{-
We still need reify and eval to input SemT so that they can pattern match...
But Exp can be parametrized by Type? Makes no sense, they are related...
-}

GCtx : TCtx → Set
GCtx Δ = ∀{Δ'} → TRen Δ Δ' → Ctx Δ → Ctx Δ'

Sub : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Sub Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Sem _ T Γ₂

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


-- transTSR : ∀{Δ₁ Δ₂ Δ₃} → TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
-- transTSR sub ren x = renSemT ren (sub x)


data Ctx where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{Δ} → (Γ : Ctx Δ) → SemT Δ → Ctx Δ

data Var where
  same : ∀{Δ Γ T} → Var {Δ} (Γ , T) T
  next : ∀{Δ Γ T A} → Var {Δ} Γ T → Var (Γ , A) T

-- the equivalent of this would be part of Exp in dep thy version.
-- should be inputted by App constructor.
-- How does this appear in Lambda constructor? Need inference to work...
{-
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
  -- ne : ∀{Δ Γ T} → Ne Δ Γ T → Nf Δ Γ T
  ne : ∀{Δ Γ x} → Ne Δ Γ (var x) → Nf Δ Γ (var x) -- restrict to eta-expanded forms

-- what if Exp was parametrized by a Type instead of a SemT????

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

subSemT : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → SemT Δ₁ → SemT Δ₂
-- subSemT sub (all T) = all (λ tren X → subSemT {!   !} (T {!   !} X))
-- subSemT sub (var x) = sub x
-- subSemT sub (A ⇒ B) = subSemT sub A ⇒ subSemT sub B
subSemT tsub T = evalT (reifyT T) tsub

subCtx : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
subCtx tsub ∅ = ∅
subCtx tsub (Γ , T) = subCtx tsub Γ , subSemT tsub T

-- subVar : ∀{Δ₁ Δ₂ T} → {Γ : } → TSub Δ₁ Δ₂ → Var Δ₁ T → Var Δ₂ ?
-- subVar tsub same = same
-- subVar tsub (next x) = {!   !}
subVar : ∀{Δ₁ Δ₂ T} → {Γ : Ctx Δ₁} → (tsub : TSub Δ₁ Δ₂)
  → Var Γ T → Var (subCtx tsub Γ) (subSemT tsub T)
subVar tsub same = same
subVar tsub (next x) = next (subVar tsub x)
-}
