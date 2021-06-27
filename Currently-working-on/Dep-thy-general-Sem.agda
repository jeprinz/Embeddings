open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

{-

The idea of this file is to get around the positivity issues with putting Ctx
in SemT by having semantics module parametrized by stuff. Could then use
Sem and SemT with any Ctx,Nf, Ne. Not just one specific one.

-}

module Dep-thy-general-Sem where

-- in reality, Ne represents Ne Γ U, and
-- Nf represents Nf Γ (ne e)
-- so,  not fully general Ne and Nf. But they are not needed.
-- TODO: TODO:
-- Or are they? consider where I ran into issues in defining reify in STLC one.
-- In fact, do stlc one first.
module semantics (Ctx : Set) (Ren : Ctx → Ctx → Set) (Ne : Ctx → Set) (Nf : (Γ : Ctx) → Ne Γ → Set) where

  data SemTzero : Ctx → Set where
  Semzero : (Γ : Ctx) → SemTzero Γ → Set
  Semzero Γ ()

  module sucn (SemTn : Ctx → Set) (Semn : (Γ : Ctx) → SemTn Γ → Set) where
    mutual
      data SemTsucn : Ctx → Set where
          U : ∀{Γ} → SemTsucn Γ
          Π : ∀{Γ} → (A : GSemTsucn Γ) → (GSemsucn Γ A → SemTsucn Γ) → SemTsucn Γ
          cumu : ∀{Γ} → SemTn Γ → SemTsucn Γ
          neutral : ∀{Γ} → Ne Γ → SemTsucn Γ

      GSemTsucn : Ctx → Set
      GSemTsucn Γ = ∀{Γ'} → Ren Γ Γ' → SemTsucn Γ' -- obviously need renaming here

          -- parametrize by context?
      Semsucn : (Γ : Ctx) → SemTsucn Γ → Set
      Semsucn Γ U = SemTn Γ
      Semsucn Γ (Π A B) = (a : GSemsucn Γ A) → Semsucn Γ (B a)
      Semsucn Γ (cumu T) = Semn Γ T
      Semsucn Γ (neutral e) = Nf Γ e

      GSemsucn : (Γ : Ctx) → GSemTsucn Γ → Set
      GSemsucn Γ T = ∀{Γ'} → (ren : Ren Γ Γ') → Semsucn Γ' (T ren) -- obviously need renaming in here...

  open sucn

  mutual
    SemT : ℕ → Ctx → Set
    SemT zero Γ = SemTzero Γ
    SemT (suc n) Γ = sucn.SemTsucn (SemT n) (Sem n) Γ

    Sem : (n : ℕ) → (Γ : Ctx) → SemT n Γ → Set
    Sem zero Γ T = Semzero Γ T
    Sem (suc n) Γ T = sucn.Semsucn _ _ Γ T

open semantics

mutual
  data Ctx : Set where
    ∅ : Ctx
    -- _,_ : ∀{n} → SemT

  -- SemT' : ℕ → Ctx → Set
  -- data Nf : {n : ℕ} → (Γ : Ctx) → SemT' n Γ → Set where
  -- data Ne : {n : ℕ} → (Γ : Ctx) → SemT' n Γ → Set where
  -- U' : ∀{n Γ} → SemT' (suc n) Γ
  -- neutral' : ∀{n Γ} → Ne {suc n} Γ U' → SemT' (suc n) Γ
  -- SemT' n Γ = SemT Ctx (λ Γ → Ne Γ (U' {suc n})) (λ Γ e → Nf Γ (neutral' e)) n Γ
  -- U' = semantics.sucn.SemTsucn.U
  -- neutral' = sucn.neutral
