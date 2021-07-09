open import Data.Unit
open import Data.Product

data Ctx : Set

data SemT : Ctx → Set -- where
GSemT : Ctx → Set
data Var : (Γ : Ctx) → SemT Γ → Set -- should this be GSemT????
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
  Π : ∀{Γ} → (A : GSemT Γ) → (GSem A → SemT Γ) → SemT Γ
  ne : ∀{Γ} → Ne Γ U → SemT Γ


Sem {Γ} U = SemT Γ
Sem (Π A B) = (a : GSem A) → Sem (B a)
Sem {Γ} (ne e) = Nf Γ (ne e)

GSem {Γ} A = ∀{Γ'} → (ren : Ren Γ Γ') → Sem {Γ'} (A ren)

data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → SemT Γ → Ctx

-- _∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
-- data Ren where
--   ∅ : Ren ∅ ∅
--   append : ∀{Γ₁ Γ₂} → Ren Γ₁ Γ₂ → {T : GSemT Γ₂} → Ren Γ₁ (Γ₂ , T)
--   lift : ∀{Γ₁ Γ₂} → (wea : Ren Γ₁ Γ₂)
--     → {T : GSemT Γ₁} → Ren (Γ₁ , T) (Γ₂ , λ wea₂ → T (wea ∘ wea₂))
renSemT : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂) → SemT Γ₁ → SemT Γ₂
applyRen : ∀{Γ₁ Γ₂} → {T : SemT Γ₁} → (ren : Ren Γ₁ Γ₂) → Var Γ₁ T → Var Γ₂ (renSemT ren T)
idRen : ∀{Γ} → Ren Γ Γ
append1ren : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
data Ren where
  ∅ : ∀{Γ} → Ren ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂)
    → {T : SemT Γ₁}
    -- → Var Γ₂ (λ r → T (ren ∘ r))
    → Var Γ₂ (renSemT ren T)
    → Ren (Γ₁ , T) Γ₂

-- forget1ren : ∀{Γ} →
weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)
weaken1Ren {∅} {T} = ∅
weaken1Ren {Γ , A} {T} = cons {!   !} {!   !}

-- idRen2 : ∀{Γ} → Ren Γ Γ
-- idRen2 same = same
-- idRen2 (next x) = next (idRen2 x)

idRen {∅} = ∅
idRen {Γ , T} = cons {! next   !} {!   !} -- even if can fill in first hole, second hole wont work...

data Var where
  -- same : ∀{Γ} → {T : SemT Γ} → Var (Γ , T) (renSemT (append1ren idRen) T)
  -- same : ∀{Γ} → {T : GSemT Γ} → Var (Γ , T idRen) (T (append1ren idRen))
  -- next : ∀{Γ} → {T A : GSemT Γ}
    -- → Var Γ A → Var (Γ , T) (λ r → A (forget1ren ∘ r))
  next : ∀{Γ} → {T A : SemT Γ}
    → Var Γ A → Var (Γ , T) (renSemT (append1ren idRen) A)

append1ren ∅ = ∅
append1ren (cons ren x) = cons (append1ren ren) {! next x  !}

applyRen = {!   !}
renSemT = {!   !}



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
