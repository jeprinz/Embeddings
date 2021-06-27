
-- what about contexts?
data TSem : Set
Sem : TSem → Set

{-# NO_POSITIVITY_CHECK #-}
data TSem where
  U : TSem
  Π : (A : TSem) → (Sem A → TSem) → TSem
_⇒_ : TSem → TSem → TSem
_⇒_ A B = Π A (λ _ → B)

Sem U = TSem -- maybe with the introduction of levels would be fine?
Sem (Π A B) = (a : Sem A) → Sem (B a)

extype1 : TSem
extype1 = Π U (λ X → X ⇒ X)

-- this is not what reification is anyway... should output Exp
-- also, can't really get anything out of f except more Sems.
reifyexample1 : Sem extype1 → ((X : Set) → X → X)
reifyexample1 f = λ X x → {! f X  !}
