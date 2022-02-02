open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality

{-

In this file, I'm not trying any of my crazy business with decoupling the
definitions. I'm just going to go for it in a straightforwards way.

-}

--------------------------------------------------------------------------------
------------ Main declarations -------------------------------------------------
--------------------------------------------------------------------------------

data Context : Set -- where

data Type : ℕ → Context → Set -- where

data Var : (n : ℕ) → (Γ : Context) → (Type n Γ) → Set -- where
data Term : (n : ℕ) → (Γ : Context) → (Type n Γ) → Set -- where

data Ren : Context → Context → Set -- where
data Sub : Context → Context → Set -- where

--------------------------------------------------------------------------------
------------- Main definitions -------------------------------------------------
--------------------------------------------------------------------------------

data Context where
  ∅ : Context
  _,_ : ∀{n} → (Γ : Context) → Type n Γ → Context


--------------------------------------------------------------------------------
renType : ∀{Γ₁ Γ₂ n} → Ren Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
renVar : ∀{Γ₁ Γ₂ n T} → (ren : Ren Γ₁ Γ₂) → Var n Γ₁ T → Var n Γ₂ (renType ren T)
--------------------------------------------------------------------------------
liftRen : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₁}
  → (ren : Ren Γ₁ Γ₂) → Ren (Γ₁ , T) (Γ₂ , renType ren T)
appendRen : ∀{Γ₁ Γ₂ n} → {T : Type n Γ₂}
  → (ren : Ren Γ₁ Γ₂) → Ren Γ₁ (Γ₂ , T)
idRen : ∀{Γ} → Ren Γ Γ
_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
--------------------------------------------------------------------------------
renTypeComm : ∀{Γ₁ Γ₂ Γ₃ n} → {ren₁ : Ren Γ₁ Γ₂} → {ren₂ : Ren Γ₂ Γ₃}
  → {T : Type n Γ₁}
  → renType ren₂ (renType  ren₁ T) ≡ renType (ren₁ ∘ ren₂) T
renVarComm : ∀{Γ₁ Γ₂ Γ₃ n} → {ren₁ : Ren Γ₁ Γ₂} → {ren₂ : Ren Γ₂ Γ₃}
  → {T : Type n Γ₁}
  → {x : Var n Γ₁ T}
  → (subst (λ T → Var n Γ₃ T) renTypeComm (renVar ren₂ (renVar ren₁ x)))
    ≡ renVar (ren₁ ∘ ren₂) x

--------------------------------------------------------------------------------

data Ren where
  ∅ : ∀{Γ} → Ren ∅ Γ
  _,_ : ∀{n Γ₁ Γ₂ T}
      → (ren : Ren Γ₁ Γ₂)
      → Var n Γ₂ (renType ren T)
      → Ren (Γ₁ , T) Γ₂

data Var where
  same : ∀{Γ n T} → Var n (Γ , T) (renType (appendRen idRen) T)
  next : ∀{n m Γ A} → {T : Type m Γ}
    → Var n Γ A
    → Var n (Γ , T) (renType (appendRen idRen) A)

∅ ∘ ren₂ = ∅
(ren₁ , x) ∘ ren₂ = (ren₁ ∘ ren₂) , subst (λ T → Var _ _ T) renTypeComm (renVar ren₂ x)

-- liftRen ren = {!   !}
appendRen ∅ = ∅
appendRen (ren , x) = appendRen ren , {! next x  !}

renVarComm {.(_ , _)} {Γ₂} {Γ₃} {n} {ren₁ , x₁} {ren₂} {T} {x} = {!   !}
-- maybe renTypeComm - induct on T then use renVarComm?
-- renTypeComm {.∅} {Γ₂} {Γ₃} {n} {∅} {ren₂} {T} = {! T  !}
-- renTypeComm {.(_ , _)} {Γ₂} {Γ₃} {n} {ren₁ , x} {ren₂} {T} = {!   !}
