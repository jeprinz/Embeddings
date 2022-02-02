{-# OPTIONS --cumulativity #-}

open import Data.Product

data TC₀ : Set where

mutual
  data TC₁ : Set₁ where
    U : TC₁
    Π : (A : TC₁) → (⟦ A ⟧₁ → TC₁) → TC₁
    -- Lift : TC₀ → TC₁
    Lift : Set → TC₁

  ⟦_⟧₁ : TC₁ → Set₁
  ⟦ U ⟧₁ = Set
  ⟦ Π A B ⟧₁ = (a : ⟦ A ⟧₁) → ⟦ B a ⟧₁
  ⟦ Lift T ⟧₁ = T

mutual
  data TC₂ : Set₂ where
    U : TC₂
    Π : (A : TC₂) → (⟦ A ⟧₂ → TC₂) → TC₂
    -- Lift : TC₁ → TC₂
    Lift : Set₁ → TC₂

  ⟦_⟧₂ : TC₂ → Set₂
  ⟦ U ⟧₂ = Set₁
  ⟦ Π A B ⟧₂ = (a : ⟦ A ⟧₂) → ⟦ B a ⟧₂
  -- ⟦ Lift T ⟧₂ = ⟦ T ⟧₁
  ⟦ Lift T ⟧₂ = T

-- (P : Set → Set) → (X : Set) → P X
ex1 : TC₁
ex1 = Π (Π U λ _ → U) λ P → Π U λ X → Lift (P X → P X)
-- ex1 = Π (Π U λ _ → U) λ P → Π U λ X → Π (Lift (P X)) (λ _ → Lift (P X))

ext1 : ⟦ ex1 ⟧₁
ext1 = λ P X px → px

-- a = {! ⟦ ex1 ⟧₁  !}

data TC0 : Set → Set₁ where

data TC1 : Set₁ → Set₂ where
  U : TC1 Set
  Π : {TA : Set₁} → {TB : TA → Set₁}
    → (A : TC1 TA)
    → ((a : TA) → TC1 (TB a)) → TC1 ((a : TA) → TB a)
  Lift : {T : Set} → TC0 T → TC1 T

data TC2 : Set₂ → Set₃ where
  -- U : TC2 Set₁
  U : TC2 (Σ Set₁ TC1)
  Π : {TA : Set₂} → {TB : TA → Set₂}
    → (A : TC2 TA)
    → ((a : TA) → TC2 (TB a)) → TC2 ((a : TA) → TB a)
  Lift : {T : Set₁} → TC1 T → TC2 T
  -- Lift : (T : Set₁) → TC2 T

exT2 : TC2 _
-- exT2 = Π (Π U λ _ → U) λ P → Π U (λ X → Lift (Π {! P X  !} {!   !}))
-- exT2 = Π (Π U λ _ → U) λ P → Π U (λ X → Lift (P X → P X))
exT2 = Π (Π U λ _ → U) λ P → Π U (λ X → Lift (Π (proj₂ (P X)) λ _ → proj₂ (P X)))

⟦_⟧2 : ∀{T} → TC2 T → Set₂
⟦_⟧2 {T} _ = T

ex2 : ⟦ exT2 ⟧2
ex2 = λ P X px → px

test : ∀{T} → TC2 T → Set₂
test U = Set
test (Π A B) = (a : test A) → {! B a  !}
test (Lift x) = {!   !}

{-
something like an augmented shallow embedding, except that it isn't parametrized
by the context. INstead, lambda and Pi take a function argument.
-}
