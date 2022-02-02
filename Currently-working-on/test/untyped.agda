-- {-# OPTIONS --cumulativity #-}
open import Data.Nat
open import Data.Bool
open import Data.Maybe
-- open import Data.Unit
-- open import Data.Empty
open import Data.Product

data Thing : Set₁ where
  num : ℕ → Thing
  bool : Bool → Thing
  -- func : (Thing → Thing → Set) → Thing

plus : Thing → Thing → Maybe Thing
plus (num n) (num m) = just (num (n + m))
plus _ _ = nothing

mutual
  data SpineT : Set where
    U : SpineT
    Π : SpineT → SpineT → SpineT
  data Spine : Set where
    TYPE : Spine
    FROMNE : Spine
    FUN : Spine → Spine

data ⊥ {l} : Set l where

data ⊤ {l} : Set l where
  tt : ⊤

mutual
  SemT : ℕ → SpineT → Set₁
  SemT zero U = ⊥
  SemT (suc n) U = ⊤
  SemT n (Π A B) = (SemT n A) × ((Σ Spine (Sem n)) → (SemT n B) → Set)

  Sem : ℕ → Spine → Set₁
  Sem zero TYPE = ⊥
  Sem (suc n) TYPE = Σ SpineT (SemT n)
  Sem n FROMNE = {!   !}
  Sem n (FUN S) = (Σ Spine (Sem n)) → (Sem n S) → Set

{-
data SemT where
  -- Π : ∀{Γ n} → SemT Γ n → (Sem Γ n ⇒ SemT Γ n) → SemT Γ n
  U : ∀{Γ n} → SemT Γ (suc n)
  -- Π : ∀{Γ n} → SemT Γ n → (∀{Γ'} → Ren Γ Γ' → Sem Γ' n → SemT Γ' n) → SemT Γ n
  Π : ∀{Γ n} → SemT Γ n → (∀{Γ'} → Ren Γ Γ' → Sem Γ' n → SemT Γ' n → Set) → SemT Γ n
  fromNe : ∀{Γ n} → Ne Γ (suc n) → SemT Γ n
data Sem where -- this represents the "untyped" output of eval as in racket. "untyped" in the sense that it is one of these cases
  TYPE : ∀{Γ n} → SemT Γ n → Sem Γ (suc n)
  FROMNE : ∀{Γ n} → Ne Γ n → Sem Γ n
  -- FUN : ∀{Γ n} → (∀{Γ'} → Sem Γ' n → Sem Γ' n) → Sem Γ n
  FUN : ∀{Γ n} → (∀{Γ'} → Sem Γ' n → Sem Γ' n → Set) → Sem Γ n
-}
