{-# OPTIONS --without-K #-}
{-# OPTIONS --type-in-type #-}

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function

Sub : Set → Set → Set
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

idRen : ∀{Γ} → Sub Γ Γ
idRen γ = γ

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

module sucn (SemTn : Set → Set) (Semn : (Γ : Set) → SemTn Γ → Set) where
  mutual
    data SemTsucn (Γ : Set) : Set where
        U : SemTsucn Γ
        Π : (A : SemTsucn Γ)
          → (Semsucn Γ A → SemTsucn Γ)
          → SemTsucn Γ
        cumu : SemTn Γ → SemTsucn Γ
        ne : (Γ → SemTsucn Γ) → SemTsucn Γ

    Semsucn : (Γ : Set) → SemTsucn Γ → Set
    Semsucn Γ U = Γ → SemTn Γ
    Semsucn Γ (Π A B)
      = (a : Semsucn Γ A) → Semsucn Γ (B a)
    Semsucn Γ (cumu T) = Semn Γ T
    Semsucn Γ (ne e) = (γ : Γ) → Semsucn Γ (e γ)

open sucn

mutual
  SemT : ℕ → Set → Set
  SemT zero Γ = SemTzero
  SemT (suc n) Γ = sucn.SemTsucn (SemT n) (Sem n) Γ

  Sem : (n : ℕ) → (Γ : Set) → SemT n Γ → Set
  Sem zero Γ T = Semzero T
  Sem (suc n) Γ T = sucn.Semsucn _ _ Γ T

Ctx = Set
cons : ∀{n} → (Γ : Ctx) → SemT n Γ → Ctx
cons Γ T = Σ Γ (λ γ → Sem _ Γ T)

nil : Ctx
nil = ⊤

forget1ren : ∀{n Γ} → {T : SemT n Γ} → Sub Γ (cons Γ T)
forget1ren (γ , t) = γ

test : Sem 1 nil (Π U (λ _ → U))
test = λ T → T

test2 : Sem 1 (cons nil U) U
test2 = λ (_ , T) → T tt


{-
subSemT : ∀{n Γ₁ Γ₂} → Sub Γ₁ Γ₂ → SemT n Γ₁ → SemT n Γ₂
subSemT {suc n} ren U = U
subSemT {suc n} ren (Π A B)
  -- = Π (λ ren₁ → A (ren ∘ ren₁)) (λ ren₁ → B (ren ∘ ren₁))
  = Π (subSemT ren A) {! subSemT ? B  !}
subSemT {suc n} ren (cumu T) = cumu (subSemT ren T)
subSemT {suc n} ren (ne e)
  -- = ne (λ γ₂ → subSemT ren (e (ren γ₂)))
  = {!   !}

-- toNothing : ∀{} → Γ → SemT n Γ → SemT n ⊤
-- toSomething : ∀{} → (Γ → SemT n ⊤) → SemT n Γ
-- toSomething' : ∀{} → SemT n Γ → (Γ → SemT n ⊤)
-- subSemTMore : ∀{n Γ₁ Γ₂} → (Γ₂ → Γ₁) → SemT n Γ₁ → SemT n Γ₂
-- toSomethingMore : ∀{} → (Γ₂ → SemT n Γ₁) → (Γ₂ → Γ₁) → SemT n Γ₂
-- toSomethingMore' : ∀{} → (Γ₂ → Γ₁) → SemT n Γ₂ → (Γ₂ → SemT n Γ₁)

-- won't work, because I need nApp.
Svar : ∀{n Γ} → {A : SemT (suc n) Γ}
  → Sem (suc n) (cons Γ A) (subSemT (forget1ren {suc n} {_} {A}) A) -- (λ γ → (A (proj₁ γ)))
Svar = {!   !} -- ne ?

append1sub : ∀{n Γ₁ Γ₂} → (A : SemT n Γ₁) → (sub : Sub Γ₁ Γ₂)
  → (Γ₂ → Sem n Γ₁ A) → Sub (cons Γ₁ A) Γ₂
append1sub A sub a γ = sub γ , a γ

-- append1sub : ∀{n Γ₁ Γ₂} → (A : SemT n Γ₁) → (sub : Sub Γ₁ Γ₂) → Sem n Γ₂ (subSemT sub A) → Sub (cons Γ₁ A) Γ₂
-- append1sub A sub a γ = sub γ , {! a  !}

SΠ : ∀{n Γ} → (A : SemT (suc n) Γ) → SemT (suc n) (cons Γ A) → SemT (suc n) Γ
-- SΠ A B = λ γ → Π (A γ) ((λ a → B (γ , a)))
SΠ A B = Π (λ sub → subSemT sub A) (λ sub a → subSemT (append1sub A sub {! toSomething sub ? !} ) B)

-- renSem : ∀{n Γ₁ Γ₂} → (ren : Sub Γ₁ Γ₂) → (T : SemT n Γ₁)
--   → Sem n Γ₁ T → Sem n Γ₂ (subSemT ren T)
-- renSem {suc n} ren U T = subSemT ren T
-- renSem {suc n} ren (Π A B) e = renSem ren {! B forget1ren ()  !} (e ?)
-- renSem {suc n} ren (cumu T) e = {!   !}
-- renSem {suc n} ren (ne T) e = {!   !}
-}
