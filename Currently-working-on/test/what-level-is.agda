{-

-- There is a tricky interaction of lets and type levels.
-- Suppose that we use church encodings, so no datatypes.

-}

ℕ : Set₁
ℕ = (X : Set₀) → X → (X → X) → X

-- Even : ℕ → Set₁
-- Even n = n ()

ℕ₁ : Set₂
ℕ₁ = (X : Set₁) → X → (X → X) → X
ℕ₂ : Set₃
ℕ₂ = (X : Set₂) → X → (X → X) → X

_×_ : Set₁ → Set₁ → Set₁
A × B = (X : Set₀) → (A → B → X) → X

powType : Set₃
powType = Set₁ → ℕ₂ → Set₁
pow : Set₁ → ℕ₂ → Set₁
pow T n = n Set₁ T (λ X → T × X)


fType : Set₃
fType = (n : ℕ₂) → pow ℕ n
f : (n : ℕ₂) → pow ℕ n
f n = {!   !}
