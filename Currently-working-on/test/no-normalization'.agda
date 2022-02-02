{-# OPTIONS --type-in-type #-}

ℕ : Set
ℕ = (X : Set) → X → (X → X) → X

Z : ℕ
Z X x f = x

S : ℕ → ℕ
S n X x f = f (n X x f)

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  z : ∀{n} → Z + n ≡ n
  s : ∀{a b c} → a + b ≡ c → (S a) + b ≡ S c

data +-z : (n : ℕ) → n + Z ≡ n → Set where
  z : +-z Z z
  s : ∀{n p} → +-z n p → +-z (S n) (s p)

proof : ∀{n} → +-z n p

-- {-# NON_TERMINATING #-} -- this just makes Agda not normalize the function.
-- +-z : ∀{n} → n + Z ≡ n
-- +-z {Z} = z
-- +-z {S n} = s +-z
{-

{-# NON_TERMINATING #-} -- this just makes Agda not normalize the function.
+-s : ∀{a b c} → a + b ≡ c → a + (S b) ≡ S c
+-s z = z
+-s (s r) = s (+-s r)

{-# NON_TERMINATING #-} -- this just makes Agda not normalize the function.
+-comm : ∀{a b c} → a + b ≡ c → b + a ≡ c
+-comm z = +-z
+-comm (s r) = +-s (+-comm r)

data Vec : Set → ℕ → Set where
  ∅ : ∀{T} → Vec T Z
  _,_ : ∀{T n} → T → Vec T n → Vec T (S n)

infixl 10 _,_

data append : ∀{T a b c}
  → a + b ≡ c
  → Vec T a → Vec T b → Vec T c → Set where
  z : ∀{T n} → {v : Vec T n} → append z ∅ v v
  s : ∀{T a b c r t} → {v₁ : Vec T a} → {v₂ : Vec T b} → {v₃ : Vec T c}
      → append r v₁ v₂ v₃
      → append (s r) (t , v₁) v₂ (t , v₃)
-}
