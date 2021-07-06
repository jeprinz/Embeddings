

{-

This is the sort of embedding from Data-Type Value-Term, but trying to make it
deep. Problem comes from positivity of types.

-}

mutual
  data Ctx : Set where -- what does Ctx type accomplish? It does nothing in Sem. In Exp, it seems necessary. Maybe Ctx should be a type?
    ∅ : Ctx
    cons₀ : (Γ : Ctx) → SemT₀ Γ → Ctx
    cons₁ : (Γ : Ctx) → SemT₁ Γ → Ctx
    cons₂ : (Γ : Ctx) → SemT₂ Γ → Ctx

  data SemT₀ : Ctx → Set where
  Sem₀ : (Γ : Ctx) → SemT₀ Γ → Set
  Sem₀ Γ ()

  data SemT₁ : Ctx → Set
  NeT₂ : (Γ : Ctx) → Set

  data SemT₁ where
    U : ∀{Γ} → SemT₁ Γ -- special case of neutral?
    Π : ∀{Γ} → (A : SemT₁ Γ) → (Sem₁ Γ A → SemT₁ Γ) → SemT₁ Γ -- note have to probably do GExp thing here
    cumu : ∀{Γ} → SemT₀ Γ → SemT₁ Γ
    neutral : ∀{Γ} → NeT₂ Γ → SemT₁ Γ

  Sem₁ : (Γ : Ctx) → SemT₁ Γ → Set
  data Nf₁ : (Γ : Ctx) → (T : SemT₁ Γ) → Set where
    lambda : ∀{Γ A B} → Nf₁ (cons₁ Γ A) B → Nf₁ Γ (Π A {! B  !} )
  data Ne₁ : (Γ : Ctx) → (T : SemT₁ Γ) → Set where
  Sem₁ Γ U = Nf₁ Γ U -- SemT₀ Γ
  Sem₁ Γ (Π A B) = (a : Sem₁ Γ A) → Sem₁ Γ (B a)
  Sem₁ Γ (cumu T) = Sem₀ Γ T
  Sem₁ Γ (neutral e) = Nf₁ Γ (neutral e)

  data SemT₂ : Ctx → Set where
    U : ∀{Γ} → SemT₂ Γ
    Π : ∀{Γ} → (A : SemT₂ Γ) → (Sem₂ Γ A → SemT₂ Γ) → SemT₂ Γ -- note have to probably do GExp thing here
    cumu : ∀{Γ} → SemT₁ Γ → SemT₂ Γ
  Sem₂ : (Γ : Ctx) → SemT₂ Γ → Set
  data Nf₂ : (Γ : Ctx) → (T : SemT₂ Γ) → Set where
  Sem₂ Γ U = Nf₂ Γ U -- SemT₁ Γ    -- two things: 1) putting SemT₁ Γ sets off positivity error. 2) Putting Nf is more consistent with the neutral case!
  Sem₂ Γ (Π A B) = (a : Sem₂ Γ A) → Sem₂ Γ (B a)
  Sem₂ Γ (cumu T) = Sem₁ Γ T

  -- data Nf₀ : (Γ : Ctx) → (T : SemT₀ Γ) → Sem₀ Γ T → Set where
  -- data Nf₁ : (Γ : Ctx) → (T : SemT₁ Γ) → Sem₁ Γ T → Set where
  -- data Nf₂ : (Γ : Ctx) → (T : SemT₂ Γ) → Sem₂ Γ T → Set where -- TODO: do I go with the "parametrized by eval result" design or not?
  data Nf₀ : (Γ : Ctx) → (T : SemT₀ Γ) → Set where
  data Ne₀ : (Γ : Ctx) → (T : SemT₀ Γ) → Set where
  data Ne₂ : (Γ : Ctx) → (T : SemT₂ Γ) → Set where

  NeT₂ Γ = Ne₂ Γ U

  -- reify₀ : ∀{Γ T} → Nf₀ Γ T
  -- reify₀ e = {!   !}

{-

first TODO:
How does value constructor work? Where does Nf appear in definition of Sem₁?
Think about it in terms of handwritten reification of dep thy, and Racket program.

BIG TODO:
Think about why GExp is still necessary, and put it in here everywhere where is is
in STLC NbE.

-}
