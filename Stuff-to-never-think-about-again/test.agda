open import Agda.Primitive
open import Data.Nat

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

mutual


  Context : Set
  data Exp : (Γ : Context) → Set j → Set j where
    -- Lambda : ∀{Γ} → Exp Γ {!   !} → Exp Γ ({!   !} → Exp Γ ?)
    -- App : ∀{Γ} → Exp Γ ({!   !} → Exp Γ ?) → Exp Γ {!   !} → Exp Γ {!   !}

  Context = {!   !}

data Fin : ℕ → Set where
  z : ∀{n} → Fin n
  s : ∀{n} → Fin n → Fin (suc n)

Fin = μ Fin . λ (n : ℕ) → self x
  → (P : (n : ℕ) → Fin n → Set)
  → (∀{n} → P n (z n))
  → (∀{n} → {f : Fin n} → P f → P (s f))
  → P n x

Bad = μ Bad . Bad → ⊥
bad : Bad
bad = λ b → b bad
