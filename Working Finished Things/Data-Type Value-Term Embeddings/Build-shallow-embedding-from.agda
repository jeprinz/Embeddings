open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

{-

The embedding from Core.agda, but built into a shallow embedding and stored
shallow embedding. Doesn't seem to gain particularly much from doing this.

-}

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

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
  Sem zero T = Semzero T
  Sem (suc n) T = sucn.Semsucn _ _ T

type⊥ : ∀{n} → SemT (2 + n)
type⊥ = Π U λ X → cumu X

consistency : ∀{n} → Sem (2 + n) type⊥ → ⊥
consistency {zero} e with (e U)
... | ()
consistency {suc n} e = consistency (e type⊥)

_⇒_ : ∀{n} → SemT n → SemT n → SemT n
_⇒_ {suc n} A B = Π A (λ _ → B)

typeBool : ∀{n} → SemT (suc n)
typeBool = Π U (λ X → (cumu X) ⇒ (cumu X ⇒ cumu X))
-- could put Π in SemT₀ and then put cumu outside ⇒'s
-- although would make proof of consistency impossible?

-- reifyBool : Sem 2 typeBool → Bool
-- reifyBool e = let a = e (Π U (λ _ → U)) (λ x → x) (λ x → x) in {! a  !}

reifyTest : Sem 2 (U ⇒ U) → ℕ
reifyTest e = {! e U  !}

{-
BIG QUESTION: how can I get stuff out of Sems other than Sems?
-- In STLC Sem, you COULD use it like a shallow embedding like I am here!
   If it wasn't parametrized by Γ and didn't have Nf in base case, thats all you would be able to do.
-- Inspired by unquote-n, need Sem here to output two things: Syn AND Sem

IDEA: if I made a "shallow++" embedding over this instead of standard shallow embedding,
then both the type and term would be data?
-}

------------------------  "Shallow" embedding   --------------------------------

Ctx = Set
Type : ℕ → Ctx → Set
Type n Γ = Γ → SemT n
Term : ∀{n} → (Γ : Ctx) → Type n Γ → Set
Term Γ T = (γ : Γ) → Sem _ (T γ)
nil : Ctx
nil = ⊤
cons : ∀{n} → (Γ : Ctx) → Type n Γ → Ctx
cons Γ T = Σ Γ (λ γ → Sem _ (T γ))

SU : ∀{n Γ} → Type (suc n) Γ
SU = λ _ → U

SΠ : ∀{n Γ} → (A : Type (suc n) Γ) → Type (suc n) (cons Γ A) → Type (suc n) Γ
SΠ A B = λ γ → Π (A γ) ((λ a → B (γ , a)))

Slambda : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (SΠ A B)
Slambda e = λ γ → λ a → e (γ , a)

Sapp : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term Γ (SΠ A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
Sapp e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

Svar : ∀{n Γ} → {A : Type (suc n) Γ} → Term (cons Γ A) (λ γ → (A (proj₁ γ)))
Svar = proj₂

Sweaken : ∀{n Γ} → {T A : Type n Γ} → Term Γ T → Term (cons Γ A) (λ γ → (T (proj₁ γ)))
Sweaken e = λ γ → e (proj₁ γ)

ScumuT : ∀{n Γ} → (T : Type n Γ) → Type (suc n) Γ
ScumuT T = λ γ → cumu (T γ)

Scumu : ∀{n Γ} → {T : Type n Γ} → Term Γ T → Term Γ (ScumuT T)
Scumu e = e

-------------------- Augmented "shallow" embedding -----------------------------

data Context : Ctx → Set₁ where
  ∅ : Context nil
  _,_ : ∀{n SΓ} → (ctx : Context SΓ) → (T : Type n SΓ) → Context (cons SΓ T)

data InCtx : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Type n SΓ} → {Γ : Context SΓ}
    → InCtx {n} (Γ , T) (λ γ → T (proj₁ γ)) proj₂
  next : ∀{n m SΓ Γ A a} → {T : Type n SΓ} → InCtx {m} {SΓ} Γ A a
    → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

data Exp : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
    → {B : Type (suc n) (cons SΓ A)} → ∀{a}
    → Exp (Γ , A) B a → Exp Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
  Evar : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → {a : Term SΓ T}
    → (icx : InCtx Γ T a) → Exp {n} {SΓ} Γ T a
  Eapp : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
      → {B : Type (suc n) (cons SΓ A)} → ∀{a₁ a₂}
      → Exp {suc n} Γ (SΠ A B) a₁ → (x : Exp {suc n} Γ A a₂)
      → Exp {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sapp {n} {SΓ} {A} {B} a₁ a₂)
  EΠ : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {a₁ : Term SΓ (SU {suc n})}
    → {a₂ : Type (suc n) (cons SΓ a₁)} → (A : Exp Γ (SU {suc n}) a₁)
    → (B : Exp (Γ , a₁) (SU {suc n}) a₂)
    → Exp Γ (SU {suc n}) (SΠ {n} a₁ a₂)
  EU : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → Exp {suc (suc n)} {SΓ} Γ SU SU
  -- TODO: shouldn't have to be 2+n there. Something funky with way I've defined things above!
  -- Eweaken : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ}
    -- → {A : Type n SΓ} → ∀{a}
    -- → Exp Γ T a → Exp (Γ , A) (λ γ → (T (proj₁ γ))) (Sweaken {_} {_} {T} {A} a)
  EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
    → Exp Γ T a → Exp Γ (ScumuT T) (Scumu {n} {_} {T} a)
  Ecumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
    → Exp Γ (SU {n}) a → Exp Γ (SU {suc n}) (ScumuT a)

extractTerm : ∀{n SΓ Γ T t} → Exp {n} {SΓ} Γ T t → Term SΓ T
extractTerm {_} {_} {_} {_} {t} e = t

exampleType : Exp {2} ∅ SU _
exampleType = EΠ EU (EΠ (Ecumu (Evar same)) (Ecumu (Evar (next same))))

exampleTerm : Exp ∅ (extractTerm exampleType) _
exampleTerm = Elambda (Elambda (Evar same))
