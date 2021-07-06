module System-F where

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

module semantics (TCtx : Set) (Ctx : TCtx → Set) (TVar : ℕ → TCtx → Set)
  (TRen : TCtx → TCtx → Set) (Ren : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set)
  (Nf : ∀{n} → (Δ : TCtx) → Ctx Δ → TVar n Δ → Set) where

  data SemTzero : TCtx → Set where
  Semzero : (Δ : TCtx) → SemTzero Δ → Set
  Semzero Δ ()

  module sucn (SemTn : TCtx → Set) (Semn : (Δ : TCtx) → SemTn Δ → Ctx Δ → Set)
    (TVarsucn : TCtx → Set) (Nfsucn : (Δ : TCtx) → Ctx Δ → TVarsucn Δ → Set) where
    mutual
      data SemTsucn : TCtx → Set where
          All : ∀{Δ} → (SemTn Δ → SemTsucn Δ) → SemTsucn Δ
          cumu : ∀{Δ} → SemTn Δ → SemTsucn Δ
          Var : ∀{Δ} → TVarsucn Δ → SemTsucn Δ

      GSemTsucn : TCtx → Set
      GSemTsucn Γ = ∀{Γ'} → TRen Γ Γ' → SemTsucn Γ' -- obviously need renaming here

          -- parametrize by context?
      Semsucn : (Δ : TCtx) → SemTsucn Δ → Ctx Δ → Set
      Semsucn Δ (All T) Γ = (a : SemTn Δ) → Semsucn Δ (T a) Γ
      Semsucn Δ (cumu T) Γ = Semn Δ T Γ
      Semsucn Δ (Var X) Γ = Nfsucn Δ Γ X

      GSemsucn : (Δ : TCtx) → GSemTsucn Δ → Ctx Δ → Set
      GSemsucn Δ T Γ = ∀{Δ' Γ'} → {tren : TRen Δ Δ'}
        → (ren : Ren tren Γ Γ') →  Semsucn Δ' (T tren) Γ' -- obviously need renaming in here...

  open sucn
  mutual
    SemT : ℕ → TCtx → Set
    SemT zero Γ = SemTzero Γ
    SemT (suc n) Γ = sucn.SemTsucn (SemT n) (Sem n) (TVar (suc n)) Nf Γ

    Sem : (n : ℕ) → (Δ : TCtx) → SemT n Δ → Ctx Δ → Set
    Sem zero Δ T Γ = Semzero Δ T
    Sem (suc n) Δ T Γ = sucn.Semsucn _ _ (TVar (suc n)) Nf Δ T Γ


data TCtx : Set -- where
Type : ℕ → TCtx → Set
data TCtx where
  ∅ : TCtx
  _,_ : ∀{n} → (Δ : TCtx) → Type n Δ → TCtx
Type n Δ = semantics.SemT TCtx {!   !} {!   !} {!   !} {!   !} {!   !} n Δ
-- data Ctx : TCtx → Set -- where
-- data TVar : ℕ → TCtx → Set -- where

-- TRen : TCtx → TCtx → Set
-- Ren : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set
-- data Ctx where
-- data TCtx where
-- data TVar where
