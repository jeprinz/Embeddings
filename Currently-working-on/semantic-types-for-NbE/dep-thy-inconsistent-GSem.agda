open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

{-

Overall, the problem to be solved seems to be that I need a representation of SemT which simultaneously
makes renaming and substitution facts work out definitionally, but on which I can pattern match
to distinguish between Π and U cases.

It is very possible that no such SemT exists.

-}

data Ctx : Set

data SemT : Ctx → Set -- where
GSemT : Ctx → Set
data Var : (Γ : Ctx) → GSemT Γ → Set -- should this be GSemT????
data Ne : (Γ : Ctx) → SemT Γ → Set -- where
data Nf : (Γ : Ctx) → SemT Γ → Set -- where

data Ren : Ctx → Ctx → Set
-- Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ {! T  !}


GSemT Γ = ∀{Γ'} → Ren Γ Γ' → SemT Γ'

Sem : ∀{Γ} → SemT Γ → Set
GSem : ∀{Γ} → GSemT Γ → Set

{-# NO_POSITIVITY_CHECK #-}
data SemT where
  U : ∀{Γ} → SemT Γ
  -- Π : ∀{Γ} → (A : GSemT Γ) → (GSem A → SemT Γ) → SemT Γ
  Π : ∀{Γ} → (A : GSemT Γ) → (∀{Γ'} → (ren : Ren Γ Γ') → Sem (A ren) → SemT Γ') → SemT Γ
  ne : ∀{Γ} → Ne Γ U → SemT Γ

-- With this version of Π,
-- Exp
--    Lambda : ∀{Γ A B} → Exp (Γ , A) (B idRen (var same)) → Exp Γ (Π A B)


Sem {Γ} U = SemT Γ
-- Sem {Γ} (Π A B) = (a : GSem A) → Sem (B a)
Sem {Γ} (Π A B) = ∀{Γ'} → (ren : Ren Γ Γ') → (a : Sem (A ren)) → Sem (B ren a)
Sem {Γ} (ne e) = Nf Γ (ne e)

data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → GSemT Γ → Ctx

_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃

renSemT : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂) → GSemT Γ₁ → GSemT Γ₂
renSemT ren T = λ ren₂ → T (ren ∘ ren₂)

applyRen : ∀{Γ₁ Γ₂} → {T : GSemT Γ₁} → (ren : Ren Γ₁ Γ₂) → Var Γ₁ T → Var Γ₂ (renSemT ren T)
idRen : ∀{Γ} → Ren Γ Γ
-- TODO: rename this
append1ren : ∀{Γ₁ Γ₂} → {T : GSemT Γ₂} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
data Ren where
  ∅ : ∀{Γ} → Ren ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂)
    → {T : GSemT Γ₁}
    → Var Γ₂ (renSemT ren T)
    → Ren (Γ₁ , T) Γ₂

forget1ren : ∀{Γ₁ Γ₂} → {T : GSemT Γ₁} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂
forget1ren (cons ren x) = ren

data Var where
  same : ∀{Γ} → {T : GSemT Γ} → Var (Γ , T) (renSemT (append1ren idRen) T)
  next : ∀{Γ} → {T A : GSemT Γ}
    → Var Γ A → Var (Γ , T) (renSemT (append1ren idRen) A)

-- If renaming were a function, this would definitionally hold
assoc : ∀{Γ₁ Γ₂ Γ₃ Γ₄} → (ren₁ : Ren Γ₁ Γ₂) → (ren₂ : Ren Γ₂ Γ₃)
  → (ren₃ : Ren Γ₃ Γ₄)
  → ren₁ ∘ (ren₂ ∘ ren₃) ≡ (ren₁ ∘ ren₂) ∘ ren₃
assoc = {!   !}

-- appendLemma : ∀{Γ} → 

weaken1Ren : ∀{Γ} → {T : GSemT Γ} → Ren Γ (Γ , T)
weaken1Ren {∅} {T} = ∅
weaken1Ren {Γ , A} {T} = cons (append1ren weaken1Ren) {! next same  !}

idRen {∅} = ∅
idRen {Γ , T} = cons (append1ren idRen) same

append1ren ∅ = ∅
append1ren (cons ren x) = cons (append1ren ren) {! next x  !}
-- If Ren was implemented with functions and ∘ was function composition, the
-- above would simply work out.

{-

renSemT ren U = U
renSemT ren (Π A B) = Π (λ ren₂ → A (ren ∘ ren₂)) (λ a → {! B a  !} )
renSemT ren (ne e) = {!   !}
applyRen (cons ren x₁) same = {! x₁  !}
applyRen (cons ren x₁) (next x) = {!   !}



data Ne where
data Nf where
  U : ∀{Γ} → Nf Γ U
{-

BIG TODO: are Var, Nf, Ne, parametrized by GSemT, or SemT?
-- Var must be parametrized by GSemT, because how else can next constructor of Var work?
    -- unless going to define weakening in there...
-- Also, Should Ctx hold GSemT or SemT???????
-- If Nf/Ne are parametrized by SemT, then so should Ctx? Would solve some problems?

-}
-}
