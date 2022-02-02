-- Intrinsic embeddings contain redundant information becuase a type derivation
-- can be computed from a term derivation.

-- But what if terms are actually functions and not a datatype?

{- this is dep thy with type-in-type. Goal is to merely DEFINE, not compute
 normalization. -}

data Context : Set -- where
data Type : Context → Set -- where
data Var : (Γ : Context) → Type Γ → Set -- where
data Ne : (Γ : Context) → Type Γ → Set -- where
Term : (Γ : Context) → Type Γ → Set

data Context where
  ∅ : Context
  _,_ : (Γ : Context) → Type Γ → Context

data Type where
  U : ∀{Γ} → Type Γ
  Π : ∀{Γ} → (A : Type Γ) → Type (Γ , A) → Type Γ
  ne : ∀{Γ} → Ne Γ U → Type Γ

Term Γ U = Type Γ
Term Γ (Π A B) = Term (Γ , A) B
Term Γ (ne e) = Ne Γ (ne e)
