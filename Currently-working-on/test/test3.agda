{-# OPTIONS --without-K #-}

open import Data.Empty

{-# NO_POSITIVITY_CHECK #-}
data Bad : Set where
  c : (Bad → ⊥) → Bad

nb : Bad → ⊥
nb (c x) = x (c x)

b : Bad
b = c nb

contradiction : ⊥
contradiction = nb b
