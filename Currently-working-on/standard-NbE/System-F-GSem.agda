module System-F-GSem where

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

data TCtx : Set -- where
data TVar : TCtx → Set -- where
data SemT : TCtx → Set -- where
data Ctx : TCtx → Set -- where
data Type : TCtx → Set -- where
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

GSemT : TCtx → Set
{-# NO_POSITIVITY_CHECK #-}
data SemT where
    -- Π : ∀{Γ} → (A : GSemT Γ) → (∀{Γ'} → (ren : Ren Γ Γ') → Sem (A ren) → SemT Γ') → SemT Γ
    all : ∀{Δ} → (∀{Δ'} → (tren : TRen Δ Δ') → SemT Δ' → SemT Δ') → SemT Δ
    var : ∀{Δ} → TVar Δ → SemT Δ
    _⇒_ : ∀{Δ} → SemT Δ → SemT Δ → SemT Δ

GSemT Δ = ∀{Δ'} → TRen Δ Δ' → SemT Δ'


data TCtx where
  ∅ : TCtx
  S : TCtx → TCtx

data Type where
  var : ∀{Δ} → TVar Δ → Type Δ
  all : ∀{Δ} → Type (S Δ) → Type Δ
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ

GSem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
Sem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
-- Sem {Γ} (Π A B) = ∀{Γ'} → (ren : Ren Γ Γ') → (a : Sem (A ren)) → Sem (B ren a)
Sem Δ (all T) Γ = ∀{Δ'} → (ren : TRen Δ Δ') → (X : SemT Δ') → SemT Δ'
Sem Δ (A ⇒ B) Γ = GSem Δ A Γ → Sem Δ B Γ
Sem Δ (var X) Γ = Nf Δ Γ (var X)

GSem Δ T Γ = ∀{Γ'}
  → (ren : Ren Γ Γ') →  Sem Δ T Γ'

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

idSubT : ∀{Δ} → TSub Δ Δ
idSubT = var

data Ctx where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{Δ} → (Γ : Ctx Δ) → Type Δ → Ctx Δ

data Var where
  same : ∀{Δ Γ T} → Var {Δ} (Γ , T) T
  next : ∀{Δ Γ T A} → Var {Δ} Γ T → Var (Γ , A) T

-- data Nf : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where
data Ne where

data Nf where


evalT : ∀{Δ₁ Δ₂} → Type Δ₁ → TSub Δ₁ Δ₂ → SemT Δ₂
evalT (A ⇒ B) sub = evalT A sub ⇒ evalT B sub
evalT (all T) sub = all (λ tren X → evalT T {! append1Tsub sub ?  !} ) -- unknown to me how exactly this, or all case of Sem, should work.
evalT (var x) sub = sub x

reifyT : ∀{Δ} → SemT Δ → Type Δ
reifyT (all T) = all (reifyT (T weaken1renT (var same)))
reifyT (var x) = var x
reifyT (A ⇒ B) = reifyT A ⇒ reifyT B

data Exp : (Δ : TCtx) → Ctx Δ → Type Δ → Set where
  var : ∀{Δ Γ T} → Var {Δ} Γ T → Exp Δ Γ T
  lambda : ∀{Δ Γ A B} → Exp Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  Lambda : ∀{Δ Γ T}
    → Exp (S Δ) {! renCtx  !} T → Exp Δ Γ (all T)
  App : ∀{Δ Γ T} → Exp Δ Γ (all T) → (A : Type Δ)
    → Exp Δ Γ (reifyT (evalT T (append1Tsub idSubT (evalT A idSubT))))
{-

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

canireify : ∀{Δ} → GSemT Δ → ℕ
canireify T = {! T  !}
-}
