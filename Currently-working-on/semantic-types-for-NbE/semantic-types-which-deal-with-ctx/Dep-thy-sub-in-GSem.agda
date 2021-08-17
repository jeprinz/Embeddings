{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
-- I'm using rewrite to deal with idSub for now. Some day, I'll hopefully figure out
-- how to make idSub be the identity function.


open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Ctx : Set

data SemT : Ctx → Set -- where
GSemT : Ctx → Set
data Var : (Γ : Ctx) → GSemT Γ → Set -- where -- maybe GSemT instead?
data Ne : (Γ : Ctx) → GSemT Γ → Set -- where
data Nf : (Γ : Ctx) → GSemT Γ → Set -- where
data Type : (Γ : Ctx) → Set -- where --??????

data Sub : Ctx → Ctx → Set

GSemT Γ = ∀{Γ'} → Sub Γ Γ' → SemT Γ'

Sem : ∀{Γ} → SemT Γ → Set
GSem : ∀{Γ} → GSemT Γ → Set

-- SCtx = Set
-- data Ctx' : SCtx → Set where
--   ∅ : Ctx' ⊤
--   _,_ : ∀{SΓ} → (Γ : Ctx' SΓ) → (T : GSemT Γ) → Ctx ?

data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → GSemT Γ → Ctx

ctxType : Ctx → Set
ctxType ∅ = ⊤
ctxType (Γ , T) = {! ctxType  !}

_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₃
evalNf : ∀{Γ₁ Γ₂} → {T : GSemT Γ₁} → (sub : Sub Γ₁ Γ₂) → Nf Γ₁ T → Sem (T sub)
evalNe : ∀{Γ₁ Γ₂} → {T : GSemT Γ₁} → (sub : Sub Γ₁ Γ₂) → Ne Γ₁ T → Sem (T sub)
append1sub : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → {T : GSemT Γ₁}
    → GSem (λ sub₂ → T (sub ∘ sub₂)) → Sub (Γ₁ , T) Γ₂
idSub : ∀{Γ} → Sub Γ Γ

-- TODO: TODO: TODO: If Sub is going to work like this, needs to be like a shallow embedding. e.g,
-- Sub Γ₁ Γ₂ = Γ₂ → Γ₁
postulate -- the idea is that with a functional representation of substitutions, these are definitionally true.
  idLemma : ∀{Γ₁ Γ₂} → {sub : Sub Γ₁ Γ₂} → idSub ∘ sub ≡ sub


{-# REWRITE idLemma #-}

{-# NO_POSITIVITY_CHECK #-}
data SemT where
  U : ∀{Γ} → SemT Γ
  Π : ∀{Γ} → (A : GSemT Γ)
    -- → SemT (Γ , A) -- TODO: what goes here?
    → GSemT (Γ , A) -- this?
    → SemT Γ
  ne : ∀{Γ} → Ne Γ (λ _ → U) → SemT Γ



Sem {Γ} U = SemT Γ
Sem {Γ} (Π A B) = (a : GSem A) → Sem (B (append1sub idSub a)) -- (a : GSem A) → Sem (B a)
Sem {Γ} (ne e) = Nf Γ (λ sub → evalNe sub e)

GSem {Γ} T = ∀{Γ'} → (sub : Sub Γ Γ') → Sem (T sub)

----- Build a shallow embedding from GSemT and GSem!
subGSemT : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → GSemT Γ₁ → GSemT Γ₂
subGSemT sub T = λ sub₂ → T (sub ∘ sub₂)
weaken1Sub : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂)
  → (T : GSemT Γ₁) → Sub (Γ₁ , T) (Γ₂ , subGSemT sub T)

SΠ : ∀{Γ} → (A : GSemT Γ) → (B : GSemT (Γ , A)) → GSemT Γ
SΠ A B = λ sub → Π (subGSemT sub A) (λ sub₂ → B (weaken1Sub sub _ ∘ sub₂) )
-- SΠ A B = λ sub → Π (subGSemT sub A) (B (weaken1Sub sub _))

SU : ∀{Γ} → GSemT Γ
SU = λ _ → U

Slambda : ∀{Γ} → {A : GSemT Γ} → {B : GSemT (Γ , A)} → GSem B → GSem (SΠ A B)
Slambda e = λ sub a → {! e (append1sub sub a)  !}





data Ne where
  var : ∀{Γ} → {T : GSemT Γ} → Var Γ T → Ne Γ T
  app : ∀{Γ} → {A : GSemT Γ} → {B : GSemT (Γ , A)}
    → Ne Γ (SΠ A B)
    → (a : Nf Γ A)
    → Ne Γ (subGSemT (append1sub idSub λ sub → evalNf (idSub ∘ sub) a) B) -- TODO: the fact I need idSub ∘ sub instead of just sub shows an issue...
data Nf where
  lambda : ∀{Γ} → {A : GSemT Γ} → {B : GSemT (Γ , A)}
    → Nf (Γ , A) B → Nf Γ (SΠ A B)
--   fromType : ∀{Γ} → Type Γ → Nf Γ U
  -- ne : ∀{Γ e} → Ne Γ (ne e) → Nf Γ (ne e) -- keeps things in expanded eta form, and prevents duplication with fromType. Need to think how cumu constructor of SemT would come in if that existed.
  ne : ∀{Γ} → {e : Ne Γ SU} → Ne Γ (λ sub → {! ne e  !}) → Nf Γ {!   !} -- keeps things in expanded eta form, and prevents duplication with fromType. Need to think how cumu constructor of SemT would come in if that existed.

evalNe sub (var x) = {! x  !}
evalNe sub (app e₁ e₂) = {! evalNe sub e₁  !}
