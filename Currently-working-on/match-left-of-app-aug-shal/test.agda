open import Data.Bool
open import Data.Nat

P : Bool → Set
P true = ℕ
P false = Bool

f : (b : Bool) → P b → ℕ
f true n = n
f false true = 5
f false false = 6

test : ℕ
test = let x = true in f x 6

-- test' : ℕ
-- test' = (λ x → f x 6) true

test'' : ℕ
test'' = ((λ x → f x) true) 6

test''' : ℕ
test''' = (let x = true in f x) 6

-- let f = (let x = true in f x) in f 6

data Bla : Set where
  B : (ℕ → Bla) → Bla

mutual
  f1 : ℕ → Bla → ℕ
  -- f1 0 = 10
  f1 m (B f) = f1 m (f m) + (f2 m (f m))

  f2 : ℕ → Bla → ℕ
  f2 m (B f) = (f1 m (f m)) + (f2 m (f m))
