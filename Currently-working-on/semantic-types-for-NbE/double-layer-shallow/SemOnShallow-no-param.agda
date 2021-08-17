{-# OPTIONS --cumulativity #-}

module SemOnShallow-no-param where

open import Data.Unit
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Bool

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

append1ren : ∀{Γ₁ Γ₂} → {T : Type Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
append1ren sub (γ₂ , t) = sub γ₂


append1sub : ∀{Γ₁ Γ₂}
  → Sub Γ₁ Γ₂ → {T : Type Γ₁} → Exp Γ₁ T → Sub (cons Γ₁ T) Γ₂
append1sub sub e = λ γ → sub γ , e (sub γ)

idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₃
f ∘ g = λ γ → f (g γ)

weaken1Ren : ∀{Γ T} → Sub Γ (cons Γ T)
weaken1Ren (γ , _) = γ

subType : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
subType sub T = λ γ₂ → T (sub γ₂)

subExp : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → {T : Type Γ₁}
  → Exp Γ₁ T → Exp Γ₂ (subType sub T)
subExp sub e = λ γ₂ → e (sub γ₂)

forget1ren : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → (T : Type Γ₁)
  → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
forget1ren sub T (γ , t) = sub γ , t

data SemT₀ : Set j where

SType : Ctx → Set j
data SemT₁ : Set j -- where
Sem₁ : SemT₁ → Set j
SType Γ = Γ → SemT₁

reifyT : SemT₁ → Set j
reify : ∀{T} → Sem₁ T → (reifyT T)

data SemT₁ where
  SU : SemT₁
  SΠ : (A : SemT₁) → (B : reifyT A → SemT₁) → SemT₁
  -- ne : ∀{Γ} → Type₁ Γ {-Ne Γ U-} → SemT₁ Γ -- for now, merely any value.
  ne : Set₁ → SemT₁ -- maybe SU case is captured in this one?

Sem₁ SU = SemT₀
Sem₁ (SΠ A B) = (a : reifyT A) → Sem₁ (B a)
Sem₁ (ne T) = T

reifyT SU = {!   !}
reifyT (SΠ A B) = (a : reifyT A) → reifyT (B a)
reifyT (ne T) = T

reify {SΠ A B} e = λ a → reify (e a)
-- reify {SBool} b = b
reify {ne T} e = {!   !}

-- test1 : Sem₁ (SΠ SBool (λ _ → SBool))
-- test1 = λ b → b
