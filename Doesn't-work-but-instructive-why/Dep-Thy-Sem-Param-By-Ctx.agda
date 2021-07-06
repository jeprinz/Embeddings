{-# OPTIONS --cumulativity #-}

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

data Ctx : Set
SemT : ℕ → Ctx → Set₁
Sem : (n : ℕ) → (Γ : Ctx) → SemT n Γ → Set₁
data Nf : ∀{n} → (Γ : Ctx) → SemT n Γ → Set
data Ne : ∀{n} → (Γ : Ctx) → SemT n Γ → Set
U' : ∀{n Γ} → SemT (suc n) Γ
ne' : ∀{n Γ} → Ne Γ (U' {n}) → SemT (suc n) Γ


data SemTzero : Ctx → Set₁ where
Semzero : (Γ : Ctx) → SemTzero Γ → Set
Semzero Γ ()

module sucn (SemTn : Ctx → Set₁) (Semn : (Γ : Ctx) → SemTn Γ → Set₁) where
  data SemTsucn : Ctx → Set₁
  Semsucn : (Γ : Ctx) → SemTsucn Γ → Set₁
  data SemTsucn where
      U : ∀{Γ} → SemTsucn Γ
      Π : ∀{Γ} → (A : SemTsucn Γ) → (Semsucn Γ A → SemTsucn Γ) → SemTsucn Γ
      cumu : ∀{Γ} → SemTn Γ → SemTsucn Γ
      ne : ∀{n Γ} → Ne Γ (U' {n}) → SemTsucn Γ
      neIDKMAYBE : ∀{Γ} → Set → SemTsucn Γ

  Semsucn Γ U = SemTn Γ
  Semsucn Γ (Π A B) = (a : Semsucn Γ A) → Semsucn Γ (B a)
  Semsucn Γ (cumu T) = Semn Γ T
  Semsucn Γ (ne x) = Nf Γ (ne' x)
  Semsucn Γ (neIDKMAYBE T) = T


open sucn

SemT zero Γ = SemTzero Γ
SemT (suc n) Γ = sucn.SemTsucn (SemT n) (Sem n) Γ

Sem zero Γ T = Semzero Γ T
Sem (suc n) Γ T = sucn.Semsucn (SemT n) _ Γ T

U' = U
ne' = ne

data Ctx where

data Nf where

data Ne where
  U : ∀{n Γ} → Ne Γ (U' {n})
  test : ∀{Γ} → Ne {2} Γ (neIDKMAYBE (Ne Γ (U' {2})) )
  test2 : ∀{Γ A B} → Ne {2} Γ (Π A B)
  -- test3 : ∀{}

--
-- _⇒_ : ∀{n} → SemT n → SemT n → SemT n
-- _⇒_ {suc n} A B = Π A (λ _ → B)
