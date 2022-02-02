open import Data.Unit
open import Data.Sum

-- data ℕ : Set₁ where
--   c : (n : ℕ)
--     → ((P : ℕ → Set) → (∀{n} → P n → P {!   !} ) → P {!   !} → P n)
--     → ℕ



-- F = A → F,   or μ F . A → F
data F : Set where
  wrap : (⊤ → F) → F

unwrap : F → (⊤ → F)
unwrap (wrap f) = f

-- ℕ = μ N . ⊤ ⊎ N

data ℕ : Set where
  wrap : (⊤ ⊎ ℕ) → ℕ

unwrapℕ : ℕ → (⊤ ⊎ ℕ)
unwrapℕ (wrap x) = x

three : ℕ
three = wrap (inj₂ (wrap (inj₂ (wrap (inj₁ tt)))))

{-# NO_POSITIVITY_CHECK #-}
data ℕ2 : Set₁ where
  wrap : (n : ℕ2)
    → ((P : ℕ2 → Set) → (∀{n} → P n → P {! wrap ? ?  !})
      → P {!   !} → P n)
    → ℕ2
