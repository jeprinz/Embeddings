{-

The idea of this file is:
There are not types at level 0
Therefore, nothing is ever substituted at level 1 so effectively
  there are no dependent types (sort of) at level 1
Level 2?
Level 3?

The problem with a one level at a time definition is that
CONTEXTS, VARIABLES, and therefore NEUTRAL FORMS must
(maybe not variables?)
refer to all of the levels!

For example, if T : U₉, and P : T → U₀, then P t is a a low level while t is at high level.

-}

data Context : Set -- where

data Type₀ : Context → Set where
data Var₀ : (Γ : Context) → Type₀ Γ → Set where
data Nf₀ : (Γ : Context) → Type₀ Γ → Set where
-- data Ne₀ : (Γ : Context) → Type₀ Γ → Set where


data Type₁ : Context → Set -- where

cons₁' : (Γ : Context) → Type₁ Γ → Context

data Type₁ where
  U : ∀{Γ} → Type₁ Γ
  Π : ∀{Γ} → (A : Type₁ Γ) → Type₁ (cons₁' Γ A) → Type₁ Γ

data Nf₁ : (Γ : Context) → Type₁ Γ → Set -- where

data Ne₁ : (Γ : Context) → Type₁ Γ → Set -- where

-- TODO: at this level, normalization is basically STLC, because nothing can
-- ever be plugged into U.
-- sub₁ : ∀{Γ} → Type₁

data Nf₁ where
  lambda : ∀{Γ A B} → Nf₁ (cons₁' Γ A) B → Nf₁ Γ (Π A B)
  app : ∀{Γ A B}
    → Nf₁ Γ (Π A B)
    → (e : Nf₁ Γ A)
    → Nf₁ Γ {!   !}
  ne : ∀{Γ T} → Ne₁ Γ T → Nf₁ Γ T

-- NOTE: Neₙ can refer to arguments at ANY level
-- so e.g. in (x e₁ e₂ e₃) : T : Type₁
-- x will output at Type₁ , but e₁ could be at any level.
-- Var should be a single type I think, not for each level.
-- Neₙ will have a separate app constructor for each level, who'se definition
-- will be deferred until that level has been defined.
-- NOTE: I can defer the definition of some constructors of a datatype by using a second
--     dummy datatype to be defined later, have constructor input that one, and put real definition in there.
data Ne₁ where
  -- var :

data Context where
  cons₁ : (Γ : Context) → Type₁ Γ → Context

cons₁' = cons₁
