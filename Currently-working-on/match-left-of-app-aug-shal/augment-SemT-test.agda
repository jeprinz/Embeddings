-- {-# OPTIONS --without-K #-}
{-# OPTIONS --type-in-type #-}
{-
IDEA: maybe can fix the type-in-type issue by making Γ at level n for SemT n.
Then, contexts can only hold stuff from lower levels.
-}

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function

{-

The embedding from Core.agda, but built into a shallow embedding and stored
shallow embedding. Doesn't seem to gain particularly much from doing this.

-}

Sub : Set → Set → Set
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

idRen : ∀{Γ} → Sub Γ Γ
idRen γ = γ

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

module sucn (SemTn : Set → Set) (Semn : (Γ : Set) → SemTn Γ → Set) where
  mutual
    data SemTsucn (Γ : Set) : Set where
        U : SemTsucn Γ
        Π : (A : ∀{Γ'} → Sub Γ Γ' → SemTsucn Γ')
          → (∀{Γ'} → (ren : Sub Γ Γ') → Semsucn Γ' (A ren) → SemTsucn Γ') → SemTsucn Γ
        cumu : SemTn Γ → SemTsucn Γ
        ne : (Γ → SemTsucn Γ) → SemTsucn Γ

    Semsucn : (Γ : Set) → SemTsucn Γ → Set
    Semsucn Γ U = Γ → SemTn Γ
    Semsucn Γ (Π A B)
      = (a : ∀{Γ'} → (ren : Sub Γ Γ') → Semsucn Γ' (A ren)) → Semsucn Γ (B idRen (a idRen))
    Semsucn Γ (cumu T) = Semn Γ T
    Semsucn Γ (ne e) = (γ : Γ) → Semsucn Γ (e γ)

open sucn

mutual
  SemT : ℕ → Set → Set
  SemT zero Γ = SemTzero
  SemT (suc n) Γ = sucn.SemTsucn (SemT n) (Sem n) Γ

  Sem : (n : ℕ) → (Γ : Set) → SemT n Γ → Set
  Sem zero Γ T = Semzero T
  Sem (suc n) Γ T = sucn.Semsucn _ _ Γ T

Ctx = Set
cons : ∀{n} → (Γ : Ctx) → SemT n Γ → Ctx
cons Γ T = Σ Γ (λ γ → Sem _ Γ T)

nil : Ctx
nil = ⊤

forget1ren : ∀{n Γ} → {T : SemT n Γ} → Sub Γ (cons Γ T)
forget1ren (γ , t) = γ

test : Sem 1 nil (Π (λ ren → U ) (λ ren _ → U))
test = λ T → T idRen

test2 : Sem 1 (cons nil U) U
test2 = λ (_ , T) → T tt


subSemT : ∀{n Γ₁ Γ₂} → Sub Γ₁ Γ₂ → SemT n Γ₁ → SemT n Γ₂
subSemT {suc n} ren U = U
subSemT {suc n} ren (Π A B)
  = Π (λ ren₁ → A (ren ∘ ren₁)) (λ ren₁ → B (ren ∘ ren₁))
subSemT {suc n} ren (cumu T) = cumu (subSemT ren T)
subSemT {suc n} ren (ne e) = ne (λ γ₂ → subSemT ren (e (ren γ₂)))

-- toNothing : ∀{} → Γ → SemT n Γ → SemT n ⊤
-- toSomething : ∀{} → (Γ → SemT n ⊤) → SemT n Γ
-- toSomething' : ∀{} → SemT n Γ → (Γ → SemT n ⊤)
-- subSemTMore : ∀{n Γ₁ Γ₂} → (Γ₂ → Γ₁) → SemT n Γ₁ → SemT n Γ₂
-- toSomethingMore : ∀{} → (Γ₂ → SemT n Γ₁) → (Γ₂ → Γ₁) → SemT n Γ₂
-- toSomethingMore' : ∀{} → (Γ₂ → Γ₁) → SemT n Γ₂ → (Γ₂ → SemT n Γ₁)

-- won't work, because I need nApp.
Svar : ∀{n Γ} → {A : SemT (suc n) Γ}
  → Sem (suc n) (cons Γ A) (subSemT (forget1ren {suc n} {_} {A}) A) -- (λ γ → (A (proj₁ γ)))
Svar = {!   !} -- ne ?

append1sub : ∀{n Γ₁ Γ₂} → (A : SemT n Γ₁) → (sub : Sub Γ₁ Γ₂)
  → (Γ₂ → Sem n Γ₁ A) → Sub (cons Γ₁ A) Γ₂
append1sub A sub a γ = sub γ , a γ

-- append1sub : ∀{n Γ₁ Γ₂} → (A : SemT n Γ₁) → (sub : Sub Γ₁ Γ₂) → Sem n Γ₂ (subSemT sub A) → Sub (cons Γ₁ A) Γ₂
-- append1sub A sub a γ = sub γ , {! a  !}

SΠ : ∀{n Γ} → (A : SemT (suc n) Γ) → SemT (suc n) (cons Γ A) → SemT (suc n) Γ
-- SΠ A B = λ γ → Π (A γ) ((λ a → B (γ , a)))
SΠ A B = Π (λ sub → subSemT sub A) (λ sub a → subSemT (append1sub A sub {! toSomething sub ? !} ) B)

-- renSem : ∀{n Γ₁ Γ₂} → (ren : Sub Γ₁ Γ₂) → (T : SemT n Γ₁)
--   → Sem n Γ₁ T → Sem n Γ₂ (subSemT ren T)
-- renSem {suc n} ren U T = subSemT ren T
-- renSem {suc n} ren (Π A B) e = renSem ren {! B forget1ren ()  !} (e ?)
-- renSem {suc n} ren (cumu T) e = {!   !}
-- renSem {suc n} ren (ne T) e = {!   !}

{-

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

SU : ∀{n Γ} → Type (suc n) Γ
SU = λ _ → U


Slambda : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (SΠ A B)
Slambda e = λ γ → λ a → e (γ , a)

Sapp : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term Γ (SΠ A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
Sapp e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)


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
-}
