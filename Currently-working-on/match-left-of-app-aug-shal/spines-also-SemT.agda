-- {-# OPTIONS --without-K #-}

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

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

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

subType : ∀{n Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
subType sub T = λ γ → T (sub γ)

append1sub : ∀{n Γ₁ Γ₂} → {T : Type n Γ₁} → Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
append1sub sub e γ₂ = sub γ₂ , e (sub γ₂)

append1ren : ∀{n Γ₁ Γ₂} → {T : Type n Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
append1ren sub (γ₂ , t) = sub γ₂


idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

-- weaken1Ren : ∀{Γ T} → Sub Γ (cons Γ T)
-- weaken1Ren = proj₁

forget1ren : ∀{n Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → (T : Type n Γ₁)
  → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
forget1ren sub T (γ , t) = sub γ , t

--------------------------- Spine stuff ----------------------------------------

mutual
  data TSpine : Set where
    U : TSpine
    Π : TSpine → TSpine → TSpine
    cumu : TSpine
    -- ne : ?

  -- data Spine : Set where

data hasTSpine : ∀{n Γ} → Type n Γ → TSpine → Set where
  U : ∀{n Γ} → hasTSpine (SU {n} {Γ}) U
  Π : ∀{n Γ SpA SpB A B}
    → hasTSpine {suc n} {Γ} A SpA → hasTSpine B SpB
    → hasTSpine (SΠ A B) (Π SpA SpB)
  cumu : ∀{n Γ SpT T} → hasTSpine {n} {Γ} T SpT
    → hasTSpine {suc n} (ScumuT T) cumu

subSpineT : ∀{n Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂)
  → {T : Type n Γ₁} → {SpT : TSpine}
  → hasTSpine T SpT → hasTSpine (subType sub T) SpT
subSpineT sub U = U
subSpineT sub (Π {_} {_} {_} {_} {A} htsA htsB)
  = Π (subSpineT sub htsA) (subSpineT (forget1ren sub A) htsB)
subSpineT sub (cumu hts) = cumu (subSpineT sub hts)

-------------------- Augmented "shallow" embedding -----------------------------

data Context : Ctx → Set₁ where
  ∅ : Context nil
  Econs : ∀{n SΓ} → (ctx : Context SΓ) → (T : Type n SΓ)
    → (SpT : TSpine) → hasTSpine T SpT → Context (cons SΓ T)

data InCtx : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → (SpT : TSpine) → hasTSpine T SpT → Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Type n SΓ} → {Γ : Context SΓ} → ∀{SpT hts}
    → InCtx {n} (Econs Γ T SpT hts) (λ γ → T (proj₁ γ)) SpT {! hts  !} proj₂
    -- TODO: show that renaming preserves hasTSpine
    -- TODO: or maybe, this is where ne case of TSpine comes in!
    -- hasTSpine correlates ne with instances of SemT which happen to represent Ne's.
  -- next : ∀{n m SΓ Γ A a} → {T : Type n SΓ} → InCtx {m} {SΓ} Γ A a
    -- → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))
data Exp : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → (SpT : TSpine) → hasTSpine T SpT
  → Term SΓ T → Set₁ where
  -- Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
  --   → {B : Type (suc n) (cons SΓ A)} → ∀{a}
  --   → Exp (Γ , A) B a → Exp Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
  Evar : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → {a : Term SΓ T}
    → ∀{SpT hts} → (icx : InCtx Γ T SpT hts a) → Exp {n} {SΓ} Γ T SpT hts a
  Eapp : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
      → {B : Type (suc n) (cons SΓ A)} → ∀{a₁ a₂ SpA SpB htsA htsB}
      → Exp {suc n} Γ (SΠ A B) (Π SpA SpB) (hasTSpine.Π htsA htsB) a₁
      → (x : Exp {suc n} Γ A SpA htsA a₂)
      → Exp {suc n} Γ (λ γ → B (γ , a₂ γ)) SpB
          (subSpineT (append1sub {_} {_} {_} {A} idSub a₂) htsB)
          (Sapp {n} {SΓ} {A} {B} a₁ a₂)

test : ∀{n SΓ Γ T SpT hts t} → Exp {n} {SΓ} Γ T SpT hts t → ℕ
test (Evar icx) = {!   !}
test (Eapp e e₁) = {! e₁  !}

lemmaA : ∀{n Γ} → {A A' : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → {B' : Type (suc n) (cons Γ A')}
  → {SpA SpB SpA' SpB' : TSpine}
  → {htsA : hasTSpine A SpA} → {htsB : hasTSpine B SpB}
  → {htsA' : hasTSpine A' SpA'} → {htsB' : hasTSpine B' SpB'}
  → (p₁ : SΠ A B ≡ SΠ A' B')
  → (p₂ : TSpine.Π SpA SpB ≡ Π SpA' SpB')
  → hasTSpine.Π htsA htsB ≡ subst (λ hts → hasTSpine hts (Π SpA SpB)) (sym p₁) (subst (λ s → hasTSpine (SΠ A' B') s) (sym p₂) (hasTSpine.Π htsA' htsB'))
  → A ≡ A'
lemmaA p₁ refl p₃ = {!   !}
