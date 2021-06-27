open import Data.Nat
open import Data.Bool
-- mutual
--   data Ctx : Set where
--     ∅ : Ctx
--     cons₀ : (Γ : Ctx) → SemT₀ Γ → Ctx
--
--   data SemT₁ : Set where
--     U₀ : SemT₁
--     _⇒_ : SemT₁ → SemT₁ → SemT₁

  -- Sem₁ : (Γ : Ctx) → SemT₁ Γ → Set₀
  -- Sem₁ U₀ =

{-

I want to think about how to implement NbE as I have in Racket, with the
Semantic and Syntactic domains, where the types in semantic domain are still
data.
Its ok if I have to turn off consistency features like posistivity or
collapse type heirarchy. I just want to see how it fits into dependent types.

I'm not sure how to put that here. Right of Π should have function.

-}


  -- data SemT₀ : Ctx → Set where
  --   U : ∀{Γ} → SemT₀ Γ
  --   -- Π : ∀{Γ} → (A : SemT₀ Γ) → SemT₀ (cons₀ Γ A) → SemT₀ Γ
  --   Π : ∀{Γ} → (A : SemT₀ ?) → (Sem₀ {!Γ   !} A → SemT₀ ?) → SemT₀ {!   !}
  --   -- Π : ∀{Γ} → (A : SemT₀ Γ) → Sem₀ (cons₀ Γ A) U → SemT₀ Γ
  --   -- Π : ∀{Γ} → (A : SemT₀ Γ) → (Sem₀ {!   !} {!   !} → {!   !}) → SemT₀ Γ
  --   -- value : ∀{Γ}
  --
  -- Sem₀ : (Γ : Ctx) → SemT₀ Γ → Set₀
  -- Sem₀ Γ U = SemT₀ Γ
  -- Sem₀ Γ (Π A B) = Sem₀ Γ A → Sem₀ Γ {! B  !}

-- data Spine : Set where
--   bla : Spine
--   Π : Spine → Spine → Spine
--
-- mutual
--   data SemT₀ : Spine → Set where
--     U : SemT₀ bla
--     Π : ∀{s1 s2} → (A : SemT₀ s1) → ((s : Spine) → Sem₀ A s → SemT₀ s2) → SemT₀ (Π s1 s2)
--
--   Sem₀ : ∀{s} → SemT₀ s → Spine → Set₀
--   Sem₀ U s = SemT₀ s
--   Sem₀ (Π A B) s = {!   !}
--   -- Sem₀ (Π A B) s = Sem₀ A → Sem₀ {! B  !}
--
--
-- data Bool : Set where
--   true : Bool
--   false : Bool
--
-- example : Bool → Set
-- example true = {! data T : Set where  !}
-- example false = {!   !}

data SemT₀ : Set where
  bla : SemT₀

mutual
  data SemT₁ : Set where
    U₀ : SemT₁
    Π : (A : SemT₁) → (Sem₁ A → SemT₁) → SemT₁
    -- netural : ∀{Γ} → Ne₂ U₁ → SemT₁ Γ -- SemT₁ needs an extra Γ argument, which I think is only used here!
        -- a concern is that it needs to be parametrized by Ne₂, which is at higher level?
        -- Maybe need NeT₁ instead?

  Sem₁ : SemT₁ → Set₀
  Sem₁ U₀ = SemT₀
  Sem₁ (Π A B) = (a : Sem₁ A) → Sem₁ (B a) -- why does this pass the termination checker?
  -- is this an Agda bug, or does this actually satisfy the induction principle?
  -- Verify by thinking in terms of induction principle.

data Example : Set where
  e : Example
  f : (Bool → Example) → Example

f1 : Bool → Example
f1 true = e
f1 false = e

e1 : Example
e1 =  f f1

f2 : Bool → Example
f2 true = e
f2 false = e1

e2 : Example
e2 = f f2
