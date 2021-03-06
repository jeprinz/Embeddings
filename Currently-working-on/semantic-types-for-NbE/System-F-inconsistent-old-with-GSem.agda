module System-F-inconsistent-old-with-GSem where

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

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

GSemT : TCtx → Set
{-# NO_POSITIVITY_CHECK #-}
data SemT where
    all : ∀{Δ} → (GSemT Δ → SemT Δ) → SemT Δ
    var : ∀{Δ} → TVar Δ → SemT Δ
    _⇒_ : ∀{Δ} → SemT Δ → SemT Δ → SemT Δ

GSemT Δ = ∀{Δ'} → TRen Δ Δ' → SemT Δ'

GSem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
Sem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
Sem Δ (all T) Γ = (a : GSemT Δ) → Sem Δ (T a) Γ
Sem Δ (A ⇒ B) Γ = GSem Δ A Γ → Sem Δ B Γ
Sem Δ (var X) Γ = Nf Δ Γ (var X)

GSem Δ T Γ = ∀{Γ'}
  → (ren : Ren Γ Γ') →  Sem Δ T Γ'

data TCtx where
  ∅ : TCtx
  S : TCtx → TCtx

data TVar where
  same : ∀{Δ} → TVar Δ
  next : ∀{Δ} → TVar Δ → TVar (S Δ)

idRenT : ∀{Δ} → TRen Δ Δ
idRenT x = x

forget1renT : ∀{Δ₁ Δ₂} → TRen (S Δ₁) Δ₂ → TRen Δ₁ Δ₂
forget1renT ren x = ren (next x)

weaken1renT : ∀{Δ} → TRen Δ (S Δ)
weaken1renT x = next x

append1Tsub : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → SemT Δ₂ → TSub (S Δ₁) Δ₂
append1Tsub sub T same = T
append1Tsub sub T (next x) = sub x

GCtx : TCtx → Set
data Ctx where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{Δ} → (Γ : Ctx Δ) → SemT Δ → Ctx Δ
GCtx Δ = ∀{Δ'} → TRen Δ Δ' → Ctx Δ' -- do I use this somewhere?

data Var where
  same : ∀{Δ Γ T} → Var {Δ} (Γ , T) T
  next : ∀{Δ Γ T A} → Var {Δ} Γ T → Var (Γ , A) T

-- data Nf : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where
data Ne where

data Nf where

-- the equivalent of this would be part of Exp in dep thy version.
-- should be inputted by App constructor.
-- How does this appear in Lambda constructor? Need inference to work...
data Type : TCtx → Set where
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ
  all : ∀{Δ} → Type (S Δ) → Type Δ
  var : ∀{Δ} → TVar Δ → Type Δ

evalT : ∀{Δ₁ Δ₂} → Type Δ₁ → TSub Δ₁ Δ₂ → SemT Δ₂
evalT (A ⇒ B) sub = evalT A sub ⇒ evalT B sub
evalT (all T) sub = all (λ X → evalT T (append1Tsub sub (X idRenT)))
evalT (var x) sub = sub x

reifyT : ∀{Δ} → SemT Δ → Type Δ
reifyT (all T) = all {! reifyT T  !}
reifyT (var x) = var x
reifyT (A ⇒ B) = reifyT A ⇒ reifyT B

-- parametrized by GSemT? Then couldn't do pattern matching on types
data Exp : (Δ : TCtx) → Ctx Δ → SemT Δ → Set where
  var : ∀{Δ Γ T} → Var {Δ} Γ T → Exp Δ Γ T
  lambda : ∀{Δ Γ A B} → Exp Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B

  -- OK, here is the problem. Things dont seem like they make sense...
  -- Lambda : ∀{Δ Γ} → {T : SemT (S Δ)}
    -- → Exp (S Δ) {!   !} T → Exp Δ {!   !} (all {! λ X → sub T X  !} )
  Lambda : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → GSemT Δ' → SemT Δ'}
    → Exp (S Δ) {!   !} (T weaken1renT (λ ren → var (ren same))) → Exp Δ {!   !} (all (T idRenT) )

  {-
  TODO:
  The problem is, in Lambda, how can T be simultaneously a (SemT (S Δ))
  AND a (SemT Δ → SemT Δ)

  One answer: Be a    (Ren Δ Δ' → SemT Δ' → SemT Δ')
  and then input either (forget1ren idRen), var same, or
                        idRen

  But, can this function REALLY be inferred by argument?
  TODO TODO TODO!!!!! INPUT SHOULD BE SYNTACTIC TYPE, like it would be in racket program!
  Input to App specifically. What about Lambda?

  Should Exp be parametrized by syntactic type???
  -}


  -- seems fishy that would put a GSemT in source, considering GSem is generic and could return different types at different renamings.
  App : ∀{Δ Γ T} → Exp Δ Γ (all T) → (A : GSemT Δ) → Exp Δ Γ (T A)

canireify : ∀{Δ} → GSemT Δ → ℕ
canireify T = {! T  !}
