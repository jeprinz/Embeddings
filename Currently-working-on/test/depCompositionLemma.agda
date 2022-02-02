{-

Purpose: prove that for dependent composition,

(f ∘ g) x = f (g x)

should just be definitionally?

-}

_∘_ : {A : Set} → {B : (a : A) → Set} → {C : (a : A) → (b : B a) → Set}
  → (f : (a : A) → B a)
  → (g : (a : A) → (b : B a) → C a b)
  → (a : A) → C a (f a)
f ∘ g = λ x → g x (f x)
