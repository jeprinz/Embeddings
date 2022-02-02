{-# OPTIONS --type-in-type #-}

-- data Bad : Set₁ where
  -- bad : (Bad → ⊥) → Bad

-- Does having that type but only with recursion principle cause problem?
-- or only problem with induction principle?

⊥ : Set
⊥ = (X : Set) → X

Bad : Set
Bad = (X : Set) → (X → ⊥) → X

recBad : (X : Set) → ((Bad → ⊥) → X) → X
recBad X f = {!   !}

bad : (Bad → ⊥) → Bad
bad nb = {! recBad Bad  !}

nbad : Bad → ⊥
-- nbad b = b (Bad → ⊥) (λ nb → nb b) b
nbad b = b ⊥ (λ x → x) -- doesn't require type-in-type
