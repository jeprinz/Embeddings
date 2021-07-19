open import Data.Product
open import Data.Bool

data A : Set where
  a : A
data B : Set where
  a : B
  b : B
{-

The point of this file is to show that a function mutually defined with and on
a type is equivalent to adding an extra parameter to the type

-}

mutual
  data WithMut : Set where
    a : WithMut
    b : WithMut
    c : (w : WithMut) → P w → WithMut

  P : WithMut → Set
  P a = A
  P b = B
  P (c T t) = P T

data WithoutMut : Set → Set where
  a : WithoutMut A
  b : WithoutMut B
  c : ∀{X} → WithoutMut X → X → WithoutMut X

WithMut' = Σ Set (λ X → WithoutMut X)
P' : WithMut' → Set
P' (X , w) = X
a' : WithMut'
a' = (A , a)
b' : WithMut'
b' = (B , b)
c' : (w : WithMut') → P' w → WithMut'
c' (X , w) x = X , c w x

data Example1 : Set where
  c : (x y : Example1) → 
