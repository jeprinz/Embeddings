{-# OPTIONS --type-in-type #-}

open import Data.Product

L = Σ Set (λ X → X)


data ⊥ : Set where
¬_ : Set → Set
¬ T = T → ⊥

-- prov : L → Set
-- prov (T , t) = {!   !}

data Prov : (X : Set) → X → Set where
  prov : ∀{X : Set} → X → Prov Set X

data Prov2 : L → L → Set where
  prov2 : {X : Set} → {x : X}
    → Prov2 (Set , X) (X , x)

data App : L → L → L → Set where
  app : {A B : Set} → {f : A → B} → {e : A}
    → App ((A → B) , f) (A , e) (B , f e)

SelfProv : L → Set
SelfProv P = Σ L (λ proof → Σ L (λ A → App P P A × Prov2 A proof))

-- SelfProv : (X : Set) → X → Set
-- SelfProv T t = P _ P

-- I'm not sure this is the right way to do it, since with Godel numberings it would be done in a relational style
-- consider that in https://plato.stanford.edu/entries/goedel-incompleteness/#DerCon
-- everything is done relationally, including the construction of G.
-- see if that is possible here?
G : Set
G = SelfProv (_ , (λ term → ¬ SelfProv term))

lemma1 : G → ¬ G
lemma1 (fst , g) = {!   !}
