{-# OPTIONS --cumulativity #-}

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data Bool : Set where
  true : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

mutual
  data Ctx : Set where
    ∅ : Ctx
    -- cons₀ : (Γ : Ctx) → SemT₀ → Ctx
    -- cons₁ : (Γ : Ctx) → SemT₁ Γ → Ctx
    -- cons₂ : (Γ : Ctx) → SemT₂ Γ → Ctx

  data SemT₀ : Set where
  Sem₀ : SemT₀ → Set
  Sem₀ ()

  data SemT₁ : Set where
    U : SemT₁
    Π : (A : SemT₁) → (Sem₁ A → SemT₁) → SemT₁
    cumu : SemT₀ → SemT₁

  Sem₁ : SemT₁ → Set
  Sem₁ U = SemT₀
  Sem₁ (Π A B) = (a : Sem₁ A) → Sem₁ (B a)
  Sem₁ (cumu T) = Sem₀ T

  data SemT₂ : Set where
    U : SemT₂
    Π : (A : SemT₂) → (Sem₂ A → SemT₂) → SemT₂
    cumu : SemT₁ → SemT₂
  Sem₂ : SemT₂ → Set
  Sem₂ U = SemT₁
  Sem₂ (Π A B) = (a : Sem₂ A) → Sem₂ (B a)
  Sem₂ (cumu T) = Sem₁ T

{-
QUESTION: what terms can I not represent here?
-}
-- for example, λ X x . x : ∀ X . X → X
type1 : SemT₁
type1 = Π U (λ a → Π (cumu a) (λ _ → (cumu a)))

term1 : Sem₁ type1
term1 = λ T t → t
-- note that variables are represented purely by functions!

-- what about a type with terms in it, like
-- (P : U → U) → (T : U) → P T → P T

type2 : SemT₁
type2 = Π (Π U (λ _ → U)) (λ P → Π U (λ T → Π (cumu (P T)) (λ _ → cumu (P T))))

term2 : Sem₁ type2
term2 = λ P T x → x


unqT₀ : SemT₀ → Set₀
unqT₀ ()
unq₀ : ∀{T} → Sem₀ T → unqT₀ T
unq₀ {()} t
unqT₁ : SemT₁ → Set₁
unqT₁ U = Set -- this is never used properly though...
unqT₁ (Π A B) = unqT₁ A → (a : Sem₁ A) → unqT₁ (B a) -- first argument does nothing...
unqT₁ (cumu T) = unqT₀ T     -- requires type level cumulativity
unq₁ : {T : SemT₁} → Sem₁ T → unqT₁ T
unq₁ {U} t = unqT₀ t
unq₁ {Π A B} t = λ x a → unq₁ {B a} (t a)
unqT₂ : SemT₂ → Set₂
unqT₂ U = Set₁
unqT₂ (Π A B) = (a : Sem₂ A) → unqT₂ (B a)
unqT₂ (cumu T) = unqT₁ T
unq₂ : ∀{T} → Sem₂ T → unqT₂ T
unq₂ {U} t = unqT₁ t
unq₂ {Π A B} t = λ a → unq₂ {B a} (t a)
unq₂ {cumu T} t = unq₁ {T} t

{-

Sem / SemT, as defined here, along with proper context thing, could clearly be
used as a model for an embedding. Essentially very similar to a shallow embedding.

Whats not clear to me is that reification to Exp is possible.
On the posistive side, given an element t : Sem T, can pattern match on T, and then
know what kind of thing t is.
On negative side, can't input anything I want into t, so not very useful.

-}

-- can I tell true and false apart somehow?
type3 : SemT₁
type3 = Π U (λ X → Π (cumu X) (λ _ → Π (cumu X) (λ _ → cumu X)))

termtrue : Sem₁ type3
termtrue = λ X x y → x

termfalse : Sem₁ type3
termfalse = λ X x y → y

reifyBool : Sem₁ type3 → Bool
reifyBool e = {!   !}

type⊥ : SemT₂
type⊥ = Π U (λ X → cumu X)

reify⊥ : Sem₂ type⊥ → ⊥
reify⊥ e with e U
... | ()


-- can I define all levels at once?
-- The following is not positive.
-- If instead Agda allowed datatype definitions is arbitrary expressions
-- (rather than just at top level), then it should be possible to do something
-- like this. Rather than a single type parametrized by ℕ, it would be a
-- FUNCTION ℕ → Set, which outputs a different datatype for each n : ℕ by induction.
-- This would also require datatype equivalence to be by VALUE rather than NAME.
-- The existence of self types would do all of this at once.
{-
mutual
  data SemT : ℕ → Set where
    U : ∀{n} → SemT (suc n)
    Π : ∀{n} → (A : SemT n) → (Sem A → SemT n) → SemT n
    cumu : ∀{n} → SemT n → SemT (suc n)
  Sem : ∀{n} → SemT n → Set
  Sem (U {n}) = SemT n
  Sem (Π A B) = (a : Sem A) → Sem (B a)
  Sem (cumu T) = Sem T
-}

data SemTzero : Set where
module sucn (SemTn : Set) (Semn : SemTn → Set) where
  mutual
    data SemTsucn : Set where
        U : SemTsucn
        Π : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        cumu : SemTn → SemTsucn

    Semsucn : SemTsucn → Set
    Semsucn U = SemTn
    Semsucn (Π A B) = (a : Semsucn A) → Semsucn (B a)
    Semsucn (cumu T) = Semn T

open sucn

mutual
  SemT : ℕ → Set
  SemT zero = SemTzero
  SemT (suc n) = sucn.SemTsucn (SemT n) (Sem n)

  Sem : (n : ℕ) → SemT n → Set
  Sem (suc n) T = sucn.Semsucn _ _ T
