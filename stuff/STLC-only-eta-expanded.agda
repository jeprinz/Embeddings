
data Type : Set where
  _⇒_ : Type → Type → Type
  base : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data InCtx : (Γ : Ctx) → Type → Set where
  same : ∀{Γ T} → InCtx (Γ , T) T
  next : ∀{Γ T A} → InCtx Γ A → InCtx (Γ , T) A

data Exp : Ctx → Type → Set where
  var : ∀{Γ T} → (icx : InCtx Γ T) → Exp Γ T
  lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  ⋆ : ∀{Γ} → Exp Γ base

mutual
  data Ne : Ctx → Type → Set where
    var : ∀{Γ T} → (icx : InCtx Γ T) → Ne Γ T
    app : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

  -- TODO: how do I enforce expanded normal form?
  data Nf : Ctx → Type → Set where
    lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    ne : ∀{Γ T} → Ne Γ T → Nf Γ T
    ⋆ : ∀{Γ} → Nf Γ base

-- Nf can store non η-expanded things!!!
-- like for example:
test1a : Nf (∅ , (base ⇒ base)) (base ⇒ base)
test1a = ne (var same)
test1b : Nf (∅ , (base ⇒ base)) (base ⇒ base)
test1b = lambda (ne (app (var (next same)) (ne (var same))))
-- these are both really the same term!!!!!!!!!!!

mutual
  data Ne2 : Ctx → Type → Set where
    var : ∀{Γ T} → (icx : InCtx Γ T) → Ne2 Γ T
    app : ∀{Γ A B} → Ne2 Γ (A ⇒ B) → Nf2 Γ A → Ne2 Γ B

  -- TODO: how do I enforce expanded normal form?
  data Nf2 : Ctx → Type → Set where
    lambda : ∀{Γ A B} → Nf2 (Γ , A) B → Nf2 Γ (A ⇒ B)
    ne : ∀{Γ} → Ne2 Γ base → Nf2 Γ base
    ⋆ : ∀{Γ} → Nf2 Γ base
-- test1a2 : Nf2 (∅ , (base ⇒ base)) (base ⇒ base)
-- test1a2 = ne (var same)
test1b2 : Nf2 (∅ , (base ⇒ base)) (base ⇒ base)
test1b2 = lambda (ne (app (var (next same)) (ne (var same))))

-- here, test1a2 does not compile!

-- reify would not be necessary because
