open import Data.Nat
open import Data.Fin

{-
Task: define functions
      (Fin n) → T
As a datatype which stores n things.
Can it work nice? Can I get induction principle?
-}

data Fun : ℕ → (ℕ → Set) → Set₁ where
  ∅ : ∀{P} → Fun 0 P
  cons : ∀{n P} → (ren : Fun n P)
    → P n
    → Fun (suc n) P

-- apply : ∀{n T} → Fun n T → Fin n → T
-- apply (cons f x) zero = x
-- apply (cons f x) (suc n) = apply f n

mapsuc : ∀{n} → {P : ℕ → Set}
  → Fun n P → (∀{n} → P n → P (suc n)) → P 0 → Fun (suc n) P
mapsuc ∅ s z = cons ∅ z
mapsuc (cons f x) s z = cons (mapsuc f s z) (s x)

example : ∀{n} → Fin n → Fin n
example zero = zero
example (suc f) = suc (example f)

howbou : ∀{n} → Fun n (λ x → Fin (suc x))
howbou {zero} = ∅
-- howbou {suc n} = cons {! mapsuc (howbou {n}) suc ?  !} {! n  !}
howbou {suc n} = mapsuc (howbou {n}) suc zero


-- ind : ?????

{-
Using dependent types, why isnt it possible to have a function
getType : Var Γ → Set, so that

getType ∅ =

Ren : Ctx → Ctx → Set
Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ (getType Γ₁ )

Ren Γ₁ Γ₂ = self ren . ∀{T} → Var Γ₁ T → Var Γ₂ (renType ren T)


-}
