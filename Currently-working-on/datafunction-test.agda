open import Data.Nat
open import Data.Fin

{-
Task: define functions
      (Fin n) → T
As a datatype which stores n things.
Can it work nice? Can I get induction principle?
-}

data Fun : ℕ → Set → Set₁ where
  ∅ : ∀{T} → Fun 0 T
  cons : ∀{n T} → (ren : Fun n T)
    → T
    → Fun (suc n) T

example : ∀{n} → Fin n → Fin n
example zero = zero
example (suc f) = suc (example f)

howbou : ∀{n} → Fun n (Fin n)
howbou {zero} = ∅
howbou {suc n} = cons {!   !} {!   !}
