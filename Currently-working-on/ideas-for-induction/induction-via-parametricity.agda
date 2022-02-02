open import Relation.Binary.PropositionalEquality

Bool : Set₁
Bool = (X : Set) → X → X → X

not : Bool → Bool
not b X x₁ x₂ = b X x₂ x₁

theorem : ∀{b} → not (not b) ≡ b
-- no way to prove this without induction.

-- parametricity theorem (unary) for booleans:
freeBool : (bool : Bool) → (X : Set) → (P : X → Set) → (a b : X)
  → P a → P b → P (bool X a b)
freeBool bool X P a b pa pb = {!   !}
-- Don't think it is possible to prove this internally

-- theorem {b} = {! freeBool b ?   !}
theorem2 : ∀{b X x₁ x₂} → (not (not b)) X x₁ x₂ ≡ b X x₁ x₂
theorem2 {b} {X} {x₁} {x₂}
  -- = {! freeBool b X ()  !}
  = refl -- wait it wasn't supposed to be that easy...
  -- = freeBool b X {!   !} {!   !} {!   !} {!   !} {!   !}

ℕ : Set₁
ℕ = (X : Set) → X → (X → X) → X

freeℕ : (n : ℕ) → (X : Set) → (P : X → Set) → (z : X) → (s : X → X)
  → P z → ((x : X) → P x → P (s x)) → P (n X z s)

_+_ : ℕ → ℕ → ℕ
(n + m) X z s = n X z (λ x → m X x s)
-- this somehow corresponds to the standard definition:
-- zero + n = n
-- (suc n) + m = suc (n + m)

assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
assoc a b c = {! a  !}

_==_ : {X : Set} → X → X → Set₁
x₁ == x₂ = (P : _ → Set) → P x₁ → P x₂

-- assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
-- assoc zero b c = refl
-- assoc (suc a) b c = cong suc (assoc a b c)
assoc' : (a b c : ℕ) → (X : Set) → (z : X) → (s : X → X)
  → ((a + b) + c) X z s == (a + (b + c)) X z s
assoc' a b c X z s P = λ p → p
-- wait what? that wasn't supposed to also be refl...

_+'_ : {X : Set} → (X → (X → X) → X) → (X → (X → X) → X) → (X → (X → X) → X)
(n +' m) z s = n z (λ x → m x s)

-- comm : (a b : ℕ) → a + b ≡ b + a
-- comm zero b = lem1 b
-- comm (suc a) b = trans (cong suc (comm a b)) (sym (lem2 b a))
comm : (a b : ℕ) → (X : Set) → (z : X) → (s : X → X)
  → (a + b) X z s == (b + a) X z s
comm a b X z s P
  -- = freeℕ a
      -- (X → (X → X) → X)
      -- {! λ a' → (b' : X → (X → X) → X) → (z : X) → (s : X → X) →   !}
      -- {!   !} {!   !} {!   !} {!   !}
= {! freeℕ a (X → (X → X) → X) (λ a' → (b' : X → (X → X) → X) → (z : X) → (s : X → X) → P ((a' +' b') z s) → P ((b' +' a') z s )) (a X) () !}

-- maybe for a first example, come up with something simpler on booleans
-- BUT that isn't just definitionally true.

-- But in either case the idea is to e.g. use (X → (X → X) → X) as recursive
-- argument to output instead of ℕ because then there aren't type level problems.
