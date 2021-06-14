open import Relation.Binary.PropositionalEquality

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

even : ℕ → Bool
even z = true
even (s n) = not (even n)

-- e.g.
test : even (s (s (s z))) ≡ false
test = refl

-- But now, define even without ℕ or induction:

z-even : Bool
z-even = true

s-even : Bool → Bool
s-even = not

-- e.g.

test2 : s-even (s-even (s-even z-even)) ≡ false
test2 = refl
