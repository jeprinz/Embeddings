-- {-# OPTIONS --cumulativity #-}
open import Data.Product
open import Agda.Primitive
open import Data.Sum

module datatypes-from-pi where

rec⊎ : {i j k : Level}
  → {A : Set i} → {B : Set j} → {C : Set k}
  → A ⊎ B → (A → C) → (B → C) → C
rec⊎ (inj₁ x) a b = a x
rec⊎ (inj₂ y) a b = b y

module normal where

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  data ⊤ : Set where
    tt : ⊤

  data ⊥ : Set where

  Even : ℕ → Set
  Even zero = ⊤
  Even (succ n) = (Even n) → ⊥


  lemma : (n : ℕ) → Even n ⊎ (Even n → ⊥)
  lemma zero = inj₁ tt
  lemma (succ n) = rec⊎ (lemma n)
    (λ e → inj₂ λ f → f e)
    (λ e → inj₁ e)

  data _≡_ : {A : Set} → A → A → Set where
    refl : ∀{A} → {a : A} → a ≡ a

  ap : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  succ a + b = succ (a + b)

  assoc : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
  assoc zero b c = refl
  assoc (succ a) b c = ap succ (assoc a b c)

  -- test : (n : ℕ) → (n + zero) ≡ n
  -- test zero = refl
  -- test (succ n) = {!   !}

module only-pi-types where

  lssuc : Level → Level
  lssuc l = lsuc (lsuc l)
  lsssuc : Level → Level
  lsssuc l = lsuc (lsuc (lsuc l))
  module Bool (i : Level) where
    R : Set (lssuc i)
    R = (X : Set (lsuc i)) → X → X → X

    rtrue : R
    rtrue = λ X a b → a

    rfalse : R
    rfalse = λ X a b → b

    I : R → Set (lssuc i)
    I b = (P : R → Set) → P rtrue → P rfalse → P b

    itrue : I rtrue
    itrue P a b = a

    ifalse : I rfalse
    ifalse P a b = b

    Bool : Set (lssuc i)
    Bool = Σ R (λ b → I b)

    indBool : (P : R → Set) → P rtrue → P rfalse → ((r , i) : Bool) → P r
    indBool P Ptrue Pfalse (r , i) = i P Ptrue Pfalse

  module ℕ (i : Level) where
    R : Set (lsuc i)
    R = (X : Set i) → X → (X → X) → X

    rzero : R
    rzero X z s = z

    rsucc : R → R
    rsucc n X z s = s (n X z s)

    I : R → Set (lsuc i)
    I n = (P : R → Set i)
      → P rzero → ((n : R) → P n → P (rsucc n))
      → P n

    I' : (l : Level) → R → Set (lsuc i ⊔ lsuc l)
    I' l n = (P : R → Set l)
      → P rzero → ((n : R) → P n → P (rsucc n))
      → P n

    I2 : R → Set (lsssuc i)
    I2 n = (P : R → Set (lssuc i))
      → P rzero → ((n : R) → P n → P (rsucc n))
      → P n

    izero : I rzero
    izero P z s = z

    isucc : ∀{n} → I n → I (rsucc n)
    isucc n P z s = s _ (n P z s)

    RI : Set (lsuc i)
    RI = Σ R (λ r → I r)

    ind : (P : R → Set i) → P rzero → ((n : R) → P n → P (rsucc n))
      → ((r , i) : RI) → P r
    ind P Pz Ps (r , i) = i P Pz Ps

  module ⊤ (i : Level) where
    R : Set (lsuc i)
    R = (X : Set i) → X → X

    rtt : R
    rtt X x = x

    I : R → Set (lsuc i)
    I x = (P : R → Set i) → P rtt → P x

    itt : I rtt
    itt P ptt = ptt
    -- dont really need induction principles because IT is itself the induction principle

    ⊤ : Set (lsuc i)
    ⊤ = Σ R (λ r → I r)

  module ⊥ (i : Level) where
    R : Set (lsuc i)
    R = (X : Set i) → X

    I : R → Set (lsuc i)
    I x = (P : R → Set i) → P x

  module eq (i : Level) where
    R : {A : Set i} → A → A → Set (lsuc i)
    R {A} x y
      = (P : A → A → Set i)
        → ((a : A) → P a a)
        → P x y

    rrefl : {A : Set i} → {a : A} → R a a
    rrefl {A} {a} = λ P refl → refl a

    I : {A : Set i} → {x y : A} → R x y → Set (lsuc i)
    I {A} {x} {y} r
      = (P : (x y : A) → R x y → Set i)
        → ((a : A) → P a a (rrefl {_} {a}))
        → P x y r

    irefl : {A : Set i} → {a : A} → I (rrefl {_} {a})
    irefl {A} {a} = λ P refl → refl a

    RI : {A : Set i} → A → A → Set (lsuc i)
    RI x y = Σ  (R x y) (λ r → I r)

    ind : {A : Set i} → (P : (x y : A) → R x y → Set i)
      → ({a : A} → (r : R a a) → P a a r)
      → {x y : A}
      → ((r , i) : RI x y)
      → P x y r
    ind P refl (r , i) = i P (λ a → refl {a} rrefl)

  -- NOTE: this ap works with cumulativity turned on.
  -- ap : {l : Level} → {A B : Set l}
  --   → {x y : A} → (f : A → B) → ((r , i) : eq.RI (lsuc l) x y)
  --   → eq.RI l (f x) (f y)
  -- ap {l} {A} {B} f p = eq.ind (lsuc l) (λ x y r → eq.RI l (f x) (f y))
  --   (λ {a} r → eq.rrefl l , eq.irefl l)
  --   p

  _+_ : ∀{i} → ℕ.R (lsuc i) → ℕ.R i → ℕ.R i
  _+_ {i} a = a (ℕ.R i → ℕ.R i)
    (λ b → b)
    (λ a'+b b → ℕ.rsucc i (a'+b b))
  -- _+_ : ℕ → ℕ → ℕ
  -- zero + b = b
  -- succ a + b = succ (a + b)

  -- assoc : {i : Level}
  --   → (a b c : ℕ.R i)
  --   → (ai : ℕ.I i a)
  --   → eq.RI i ((a + b) + c) (a + (b + c))
  -- assoc a b c ai = ?

  -- test : {l : Level}
  --   → ((r , i) : ℕ.RI l)
  --   → eq.R (lsuc l) ((ℕ.rzero (lsuc l)) + r ) r
  -- test {l} n
  --   = ℕ.ind l
  --     (λ r → {!  eq.R (lsuc l) ((ℕ.rzero (lsuc l)) + r ) r !} )
  --     {!   !}
  --     {!   !} n

  -- test : {l : Level}
  --   → (r : ℕ.R l) → (i : ℕ.I2 l r)
  --   → eq.R (lsuc l) ((ℕ.rzero (lsuc l)) + r ) r
  -- test {l} r i = i
  --   (λ r → eq.R (lsuc l) ((ℕ.rzero (lsuc l)) + r ) r)
  --   {!   !}
  --   {!   !}

  -- bla : {l : Level} → (r : ℕ.R l) → ℕ.I2 l r
  -- bla = {!   !}



  Even : {l : Level} → ℕ.R (lssuc l) → Set (lsuc l)
  Even {l} n = n (Set (lsuc l)) (⊤.R l) (λ X → X → ⊥.R l)

  -- lemma : (n : ℕ) → Even n ⊎ (Even n → ⊥)
  -- lemma zero = inj₁ tt
  -- lemma (succ n) = rec⊎ (lemma n)
  --   (λ e → inj₂ λ f → f e)
  --   (λ e → inj₁ e)

  lemma : {l : Level}
    → (r : ℕ.R (lssuc l))
    → (i : ℕ.I' (lssuc l) (lsuc l) r)
    → (Even r) ⊎ (Even r → ⊥.R l)
  lemma {l} r i
    = i (λ r → ((Even r) ⊎ (Even {l} r → ⊥.R l)))
      (inj₁ (⊤.rtt l))
      λ n IH → rec⊎ IH
        (λ e → inj₂ (λ f → f e))
        (λ e → inj₁ e)
