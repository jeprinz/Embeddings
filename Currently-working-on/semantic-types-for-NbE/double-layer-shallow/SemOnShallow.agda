{-# OPTIONS --cumulativity #-}

module SemOnShallow where

open import Data.Unit
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- arbitrarily pick some type levels to work with.
i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

Ctx : Set j
Type : Ctx → Set j
Var : (Γ : Ctx) → Type Γ → Set i
Exp : (Γ : Ctx) → Type Γ → Set i

Ctx = Set i
Type Γ = Γ → Set i
Type₀ = λ (Γ : Ctx) → Γ → Set₀
Type₁ = λ (Γ : Ctx) → Γ → Set₁
Type₂ = λ (Γ : Ctx) → Γ → Set₂
Var Γ T = (γ : Γ) → T γ
Exp Γ T = (γ : Γ) → T γ

∅ : Ctx
∅ = ⊤
cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ {i} {i} Γ T

Π : ∀{Γ} → (A : Type Γ) → Type (cons Γ A) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

Π₀ : ∀{Γ} → (A : Type₀ Γ) → Type₀ (cons Γ A) → Type₀ Γ
Π₀ A B = λ γ → (a : A γ) → B (γ , a)

Π₁ : ∀{Γ} → (A : Type₁ Γ) → Type₁ (cons Γ A) → Type₁ Γ
Π₁ A B = λ γ → (a : A γ) → B (γ , a)

Π₂ : ∀{Γ} → (A : Type₂ Γ) → Type₂ (cons Γ A) → Type₂ Γ
Π₂ A B = λ γ → (a : A γ) → B (γ , a)

U₀ : ∀{Γ} → Type₁ Γ
U₀ γ = Set₀

U₁ : ∀{Γ} → Type₂ Γ
U₁ γ = Set₁

weakenT : ∀{Γ T} → Type Γ → Type (cons Γ T)
weakenT T (γ , _) = T γ

same : ∀{Γ T} → Var (cons Γ T) (weakenT T)
same = λ (γ , t) → t
next : ∀{Γ T A} → Var Γ A → Var (cons Γ T) (weakenT A)
next x = λ (γ , t) → x γ

var : ∀{Γ T} → (icx : Var Γ T) → Exp Γ T
var x = x

lambda : ∀{Γ A B} → Exp (cons Γ A) B → Exp Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app : ∀{Γ A B} → Exp Γ (Π A B) → (a : Exp Γ A) → Exp Γ (λ γ → B (γ , a γ))
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

-- Ren : Ctx → Ctx → Set j
-- Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ {! T  !}

Sub : Ctx → Ctx → Set j
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₃
f ∘ g = λ γ → f (g γ)

-- append1ren : ∀{Γ₁ Γ₂} → {T : GSemT Γ₂} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
append1ren : ∀{Γ₁ Γ₂} → {T : Type Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
append1ren sub (γ₂ , t) = sub γ₂

append1sub : ∀{Γ₁ Γ₂}
  → Sub Γ₁ Γ₂ → {T : Type Γ₁} → Exp Γ₁ T → Sub (cons Γ₁ T) Γ₂
append1sub sub e = λ γ → sub γ , e (sub γ)

idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

weaken1Ren : ∀{Γ T} → Sub Γ (cons Γ T)
weaken1Ren (γ , _) = γ

subType : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
subType sub T = λ γ₂ → T (sub γ₂)

subExp : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Exp Γ₁ T → Exp Γ₂ (subType sub T)
subExp sub e = λ γ₂ → e (sub γ₂)

data SemT₀ : Ctx → Set j where

mutual
  data SemT₁ : Ctx → Set j where
    SU : ∀{Γ} → SemT₁ Γ
    SΠ : ∀{Γ} → (A : ∀{Γ'} → Sub Γ Γ' → SemT₁ Γ') -- of course, only really needs Ren, but this is shallow.
      → (∀{Γ'} → (ren : Sub Γ Γ') → Sem₁ Γ' (A ren) → SemT₁ Γ') → SemT₁ Γ
    ne : ∀{Γ} → Type₁ Γ {-Ne Γ U-} → SemT₁ Γ -- for now, merely any value.
    -- TODO: should the above be Type₁ or Type₀?

  Sem₁ : (Γ : Ctx) → SemT₁ Γ → Set j
  Sem₁ Γ SU = SemT₀ Γ
  Sem₁ Γ (SΠ A B) = ∀{Γ'} → (ren : Sub Γ Γ') → (a : Sem₁ Γ' (A ren)) → Sem₁ Γ' (B ren a)
  Sem₁ Γ (ne e) = Exp Γ e -- Nf Γ (ne e)

DType₁ : Ctx → Set j
DType₁ Γ = ∀{Γ'} → Sub Γ Γ' → SemT₁ Γ'
DExp₁ : (Γ : Ctx) → DType₁ Γ → Set j
DExp₁ Γ T = ∀{Γ'} → (sub : Sub Γ Γ') → Sem₁ Γ' (T sub)
-- Sem values which can be subbed to any amount!

Dcons₁ : (Γ : Ctx) → DType₁ Γ → Ctx

DΠ₁ : ∀{Γ} → (A : DType₁ Γ) → DType₁ (Dcons₁ Γ A) → DType₁ Γ

-- DVar Γ T = (γ : Γ) → T γ

-- Dlambda : ∀{Γ} → {A : DType₁ Γ} → {B : DType₁ (cons Γ {!   !} )}
  -- → DExp₁ (cons Γ {!   !} ) B → DExp₁ Γ (SΠ {!  A  !} {!   !} )
-- Dlambda e = {!   !}

-- Sapp : ∀{Γ A B} → Exp Γ (Π A B) → (a : Exp Γ A) → Exp Γ (λ γ → B (γ , a γ))
-- Sapp e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

reifyT₁ : ∀{Γ} → SemT₁ Γ → Type Γ
reifyT₁ SU = U₀
reifyT₁ (SΠ A B) = Π (reifyT₁ (A idSub)) (reifyT₁ (((B weaken1Ren) {!   !})))
reifyT₁ (ne T) = {!   !}

nApp₁ : ∀{Γ} → {T : SemT₁ Γ}
  → {-Ne-} Exp Γ (reifyT₁ T) → Sem₁ Γ T
nApp₁ {_} {SU} e = {! ne e  !}
nApp₁ {_} {SΠ A B} e = λ ren a → {!   !}
nApp₁ {_} {ne T} e = e

reify₁ : ∀{Γ T} → Sem₁ Γ T → Exp Γ (reifyT₁ T)
reify₁ e = {!   !}

Dcons₁ Γ T = cons Γ (reifyT₁ (T idSub))
DΠ₁ A B sub = SΠ (λ ren → A (sub ∘ ren)) (λ ren a → B (append1sub sub {!  subExp (sub ∘ ren) (reify₁ a)  !} ∘ ren))
