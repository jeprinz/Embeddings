open import Data.Unit
open import Data.Product

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
  Π : ∀{Γ} → (A : GSemT Γ) → (GSem A → SemT Γ) → SemT Γ
  ne : ∀{Γ} → Ne Γ U → SemT Γ


Sem {Γ} U = SemT Γ
Sem (Π A B) = (a : GSem A) → Sem (B a)
Sem {Γ} (ne e) = Nf Γ (ne e)

GSem {Γ} A = ∀{Γ'} → (ren : Ren Γ Γ') → Sem {Γ'} (A ren)

data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → GSemT Γ → Ctx

-- data Weakening where
--   same : ∀{Γ} → Weakening Γ Γ
--   append : ∀{Γ₁ Γ₂} → Weakening Γ₁ Γ₂ → {T : GSemT Γ₂} → Weakening Γ₁ (Γ₂ , T)
--   lift : ∀{Γ₁ Γ₂} → (wea : Weakening Γ₁ Γ₂)
--     → {T : GSemT Γ₁} → Weakening (Γ₁ , T) (Γ₂ , λ wea₂ → T (wea ∘ wea₂))

_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
applyRen : ∀{Γ₁ Γ₂} → {T : GSemT Γ₁} → (ren : Ren Γ₁ Γ₂) → Var Γ₁ T → Var Γ₂ (λ r → T (ren ∘ r))
data Ren where
  ∅ : ∀{Γ} → Ren ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂)
    → {T : GSemT Γ₁}
    -- → Var Γ₂ (λ r → T (ren ∘ r))
    → Var Γ₂ (λ r → T {!   !} )
    → Ren (Γ₁ , T) Γ₂

∅ ∘ ren₂ = ∅
(cons ren x) ∘ ren₂ = cons (ren ∘ ren₂) {! applyRen ren₂ x  !}

-- Ren2 : Ctx → Ctx → Set
-- Ren2 ∅ Γ₂ = ⊤
-- Ren2 (Γ₁ , T) Γ₂ = Σ (Ren2 Γ₁ Γ₂) (λ ren → Var Γ₂ {! (λ r → T (ren ∘ r))  !})

-- forget1ren : ∀{Γ} → {T : GSemT Γ} → Ren Γ (Γ , T)
--
data Var where
--   same : ∀{Γ} → {T : GSemT Γ} → Var (Γ , T) λ r → T (forget1ren ∘ r)
--   next : ∀{Γ} → {T A : GSemT Γ}
--     → Var Γ A → Var (Γ , T) (λ r → A (forget1ren ∘ r))
--
applyRen ∅ ()
-- applyRen (cons ren y) same = {! y  !}
-- applyRen (cons ren y) (next x) = {!   !} -- applyRen ren x
--
--
-- forget1ren {∅} = ∅
-- forget1ren {Γ , T} = cons {! forget1ren   !} (next same)

  -- same : ∀{Γ} → {T : GSemT Γ} → Var (Γ , T) {!   !}
data Ne where
data Nf where
  U : ∀{Γ} → Nf Γ U

{-

BIG TODO: are Var, Nf, Ne, parametrized by GSemT, or SemT?
-- Var must be parametrized by GSemT, because how else can next constructor of Var work?
    -- unless going to define weakening in there...

-}
