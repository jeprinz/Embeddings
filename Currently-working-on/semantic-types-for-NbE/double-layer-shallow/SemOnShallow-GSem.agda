{-# OPTIONS --cumulativity #-}

module SemOnShallow-GSem where

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

data SemT₀ : Ctx → Set j where

GSemT₁ : Ctx → Set j

Dcons₁ : (Γ : Ctx) → GSemT₁ Γ → Ctx
data SemT₁ : Ctx → Set j -- where
Sem₁ : (Γ : Ctx) → SemT₁ Γ → Set j
Dcons2 : (Γ : Ctx) → SemT₁ Γ → Ctx
GSemT₁ Γ = ∀{Γ'} → Sub Γ Γ' → SemT₁ Γ'

data SemT₁ where
  SU : ∀{Γ} → SemT₁ Γ
  SΠ : ∀{Γ} → (A : GSemT₁ Γ) → (B : GSemT₁ (Dcons₁ Γ A)) → SemT₁ Γ
  SΠ2 : ∀{Γ} → (A : GSemT₁ Γ)
    → (B : ∀{Γ'} → (ren : Sub Γ Γ') → Sem₁ Γ' (A ren) → SemT₁ Γ')
    → SemT₁ Γ
  ne : ∀{Γ} → Type₁ Γ {-Ne Γ U-} → SemT₁ Γ -- for now, merely any value.
  -- TODO: should the above be Type₁ or Type₀?

reifyT₁ : ∀{Γ} → SemT₁ Γ → Type Γ


GSem₁ : (Γ : Ctx) → GSemT₁ Γ → Set j
GSem₁ Γ T = ∀{Γ'} → (sub : Sub Γ Γ') → Sem₁ Γ' (T sub)
Dcons₁ Γ T = cons Γ (reifyT₁ (T idSub))
Dcons2 Γ T = cons Γ (reifyT₁ T)

reify₁ : ∀{Γ T} → Sem₁ Γ T → Exp Γ (reifyT₁ T) -- TODO: should reify input GSem instead of Sem? No, then can't pattern match on type?

Sem₁ Γ SU = SemT₀ Γ
Sem₁ Γ (SΠ A B) = (a : GSem₁ Γ A) → Sem₁ Γ (B (append1sub idSub (reify₁ (a idSub))))
Sem₁ Γ (SΠ2 A B) = (a : GSem₁ Γ A) → Sem₁ Γ (B idSub (a idSub))
Sem₁ Γ (ne e) = Exp Γ e -- Nf Γ (ne e)

subGSemT₁ : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → GSemT₁ Γ₁ → GSemT₁ Γ₂
subGSemT₁ sub T sub₁ = T (sub ∘ sub₁)

forget1renD : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → (T : GSemT₁ Γ₁)
  → Sub (Dcons₁ Γ₁ T) (Dcons₁ Γ₂ (subGSemT₁ sub T))
forget1renD sub T (γ , t) = sub γ , {! t  !}

GΠ : ∀{Γ} → (A : GSemT₁ Γ) → (B : GSemT₁ (Dcons₁ Γ A)) → GSemT₁ Γ
GΠ A B sub = SΠ (subGSemT₁ sub A) (subGSemT₁ (forget1renD sub A) B)
-- try for a bit more. but if this doesn't work, then time to admit that my mental models
-- arent working. Maybe I should try to learn the category theory people's models,
-- for example. The point is that whatever goes wrong here, my mental model wasn't
-- able to predict or forsee it.

-- Slambda : ∀{Γ} → {A : GSemT₁ Γ} → {B : GSemT₁ (cons Γ {!   !} )}
--   → GSem₁ (cons Γ {!   !} ) B → GSem₁ Γ (SΠ {!  A  !} {!   !} )
-- -- lambda e = λ γ a → e (γ , a)
-- Slambda e = {!   !}

-- Sapp : ∀{Γ A B} → Exp Γ (Π A B) → (a : Exp Γ A) → Exp Γ (λ γ → B (γ , a γ))
-- Sapp e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

GΠ2 : ∀{Γ} → (A : GSemT₁ Γ) → (B : GSemT₁ (Dcons₁ Γ A)) → GSemT₁ Γ
GΠ2 A B sub = SΠ2 (subGSemT₁ sub A) (λ ren a → B (append1sub (sub ∘ ren) {! a  !}))


{-
  Sem₁ Γ SU = SemT₀ Γ
  Sem₁ Γ (SΠ A B) = ∀{Γ'} → (ren : Sub Γ Γ') → (a : Sem₁ Γ' (A ren)) → Sem₁ Γ' (B ren a)
  Sem₁ Γ (ne e) = Exp Γ e -- Nf Γ (ne e)

-- SVar Γ T = (γ : Γ) → T γ


-- If I can't define Type : (Γ : Ctx) → Set and Exp : (Γ : Ctx) → Type Γ → Set,
-- then none of this can really work.
-}

{-

IDEA: this seems to run into issues of substitutions not passing
through reify.

So, why not define e.g. SΠ A B
as what is currently (reify (SΠ A B))

so that no need for reify?

-}
