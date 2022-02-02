{-# OPTIONS --cumulativity #-}
{-# OPTIONS --type-in-type #-}

open import Data.Product
open import Agda.Primitive
open import Data.Unit

import Dep-Thy-shallow as S

mutual
  data Context : S.Ctx → Set where
    ∅ : Context S.∅
    _,_ : ∀{sΓ} → Context sΓ → {T : S.Type sΓ}
      → Type sΓ T
      → Context (S.cons sΓ T)

  data Var : (sΓ : S.Ctx) → (T : S.Type sΓ)
    → (S.Term sΓ T) → Set where
    same : ∀{sΓ T} → Var (S.cons sΓ T) (S.weakenT T) S.same
    next : ∀{sΓ T A s} → Var sΓ A s → Var (S.cons sΓ T) (S.weakenT A) (S.next s)

  data Type : (sΓ : S.Ctx) → (T : S.Type sΓ) → Set where
    Π : {sΓ : S.Ctx} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
      → (A : Type sΓ s₁)
      → (B : Type (S.cons sΓ s₁) s₂)
      → Type sΓ (S.Π s₁ s₂)
    U : ∀{sΓ} → Type sΓ (λ _ → Set)
    Lift : ∀{sΓ s} → Type sΓ s → Type sΓ (S.Lift s)
  data Ne : (sΓ : S.Ctx) → (T : S.Type sΓ)
    → S.Term sΓ T → Set where
    var : {sΓ : S.Ctx} → {T : S.Type sΓ} → {s : S.Term sΓ T}
      → Var sΓ T s → Ne sΓ T s
    app : {sΓ : S.Ctx} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
        → Ne sΓ (S.Π A B) s₁ → (x : Nf sΓ A s₂)
        → Ne sΓ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
    lower : ∀{sΓ} → {T : S.Type₀ sΓ} → {s : S.Term sΓ T}
      → Ne sΓ (S.Lift T) (S.lift s) → Ne sΓ T s
  data Nf : (sΓ : S.Ctx) → (T : S.Type sΓ)
    → S.Term sΓ T → Set where
    lambda : {sΓ : S.Ctx} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s}
      → Nf (S.cons sΓ A) B s → Nf sΓ (S.Π A B) (S.lambda s)
    lift : ∀{sΓ} → {T : S.Type₀ sΓ} → {s : S.Term sΓ T}
      → Nf sΓ T s → Nf sΓ (S.Lift T) (S.lift s)
    ne : ∀{sΓ T t} → Ne sΓ T t → Nf sΓ T t
    type : ∀{sΓ T} → Type sΓ T → Nf sΓ (λ _ → Set) T

-- Can I extract a well-formed description of the type of a term from
-- the knowledge that the term and it's context are well formed?

typeOfVar : ∀{sΓ sT st} → Context sΓ → Var sΓ sT st → Type sΓ sT
typeOfVar Γ same = {! Γ  !}
typeOfVar Γ (next x) = {!   !}

typeOfNf : ∀{sΓ sT st} → Context sΓ → Nf sΓ sT st → Type sΓ sT
typeOfNf Γ e = {!   !}
