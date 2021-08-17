open import Agda.Primitive

module church-sigma where

-- this approach really seems like it would work, but doesn't. this is known,
-- e.g. https://stackoverflow.com/questions/55205231/church-encoding-of-dependent-pair
module attempt1 (i : Level) where
  j = lsuc i

  Σ : (A : Set i) → (B : A → Set i) → Set j
  Σ A B = (P : Set i) → ((a : A) → B a → P) → P

  _,_ : {A : Set i} → {B : A → Set i} → (a : A) → B a → Σ A B
  a , b = λ P p → p a b

  proj₁ : {A : Set i} → {B : A → Set i} → Σ A B → A
  proj₁ p = p _ (λ a _ → a)

  proj₂ : {A : Set i} → {B : A → Set i} → (p : Σ A B) → (B (proj₁ p))
  proj₂ {A} {B} p = p (B (proj₁ p)) (λ a b → {! b  !})

-- on the other hand, this approach does seem to work! however,
-- it is wierd and unsatisfying that proj₁ must be recursive while
-- proj₂ is inductive. What if one were to define a dependent triple?
module attempt2 (i : Level) where
  j = lsuc i

  Σ : (A : Set i) → (B : A → Set i) → Set j
  Σ A B = (P : Set i) → ((a : A) → B a → P) → P

  _,_ : {A : Set i} → {B : A → Set i} → (a : A) → B a → Σ A B
  a , b = λ P p → p a b

  proj₁ : {A : Set i} → {B : A → Set i} → Σ A B → A
  proj₁ p = p _ (λ a _ → a)

  IΣ : {A : Set i} → {B : A → Set i} → Σ A B → Set j
  IΣ {A} {B} p = (P : Σ A B → Set i) → ((a : A) → (b : B a) → P (a , b)) → P p

  _i,_ : {A : Set i} → {B : A → Set i} → (a : A) → (b : B a) → IΣ {A} {B} (a , b)
  a i, b = λ P p → p a b

  proj₂ : {A : Set i} → {B : A → Set i} → (r : Σ A B) → (i : IΣ r) → B (proj₁ r)
  proj₂ {A} {B} r i = i (λ r → B (proj₁ r)) (λ a b → b)

module triple (i : Level) where
  j = lsuc i

  Triple : (A : Set i) → (B : A → Set i) → (C : (a : A) → (b : B a) → Set i) → Set j
  Triple A B C = (P : Set i) → ((a : A) → (b : B a) → C a b → P) → P

  triple : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → (a : A) → (b : B a) → C a b → Triple A B C
  triple a b c = λ P p → p a b c

  proj₁ : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → Triple A B C → A
  proj₁ p = p _ (λ a _ _ → a)

  ITriple : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → Triple A B C → Set j
  ITriple {A} {B} {C} r
    = (P : Triple A B C → Set i)
      → ((a : A) → (b : B a) → (c : C a b) → P (triple a b c))
      → P r

  itriple : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → (a : A) → (b : B a) → (c : C a b) → ITriple {A} {B} {C} (triple a b c)
  itriple a b c = λ P p → p a b c

  proj₂ : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → (r : Triple A B C) → (i : ITriple r) → B (proj₁ r)
  proj₂ {A} {B} {C} r i = i (λ r → B (proj₁ r)) (λ a b c → b)

  -- again, this doesn't work!
  -- proj₃ : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    -- → (r : Triple A B C) → (i : ITriple r) → C (proj₁ r) (proj₂ r i)
  -- proj₃ {A} {B} {C} r i = i (λ r → C (proj₁ r) {!   !} ) {!   !}

  IITriple : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → {r : Triple A B C} → ITriple r → Set j
  IITriple {A} {B} {C} {r} t
    = (P : (r : Triple A B C) → ITriple r → Set i)
      → ((a : A) → (b : B a) → (c : C a b) → P (triple a b c) (itriple a b c))
      → P r t

  iitriple : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → (a : A) → (b : B a) → (c : C a b)
    → IITriple {A} {B} {C} {triple a b c} (itriple a b c)
  iitriple a b c = λ P p → p a b c

  proj₃ : {A : Set i} → {B : A → Set i} → {C : (a : A) → B a → Set i}
    → (r : Triple A B C) → (ind : ITriple r) → IITriple ind
    → C (proj₁ r) (proj₂ r ind)
  proj₃ {A} {B} {C} r ind iind
    = iind (λ r ind → C (proj₁ r) (proj₂ r ind)) (λ a b c → c)
