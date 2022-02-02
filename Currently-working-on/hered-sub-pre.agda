open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect)
open import Data.List
open import Data.Unit
open import Data.Maybe

data Type : Set where
  _⇒_ : Type → Type → Type
  base : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data _pre_ : Ctx → Ctx → Set where
  same : ∀{Γ} → Γ pre Γ
  next : ∀{Γ₁ Γ₂ T} → Γ₁ pre Γ₂ → Γ₁ pre (Γ₂ , T)

-- data Var : Ctx → Type → Set where
  -- var : ∀{Γ' Γ T} → (Γ' , T) pre Γ → Var Γ T

transpre : ∀{Γ₁ Γ₂ Γ₃} → Γ₁ pre Γ₂ → Γ₂ pre Γ₃ → Γ₁ pre Γ₃
transpre pre₁ same = pre₁
transpre pre₁ (next pre₂) = next (transpre pre₁ pre₂)

-- unTransPre : ∀{Γ₁ Γ₂ Γ₃} → Γ₂ pre Γ₃ → Γ₁ pre Γ₂ → Γ₁ pre Γ₃

subCtx : ∀{Γ' Γ T} → (Γ' , T) pre Γ → Ctx
subCtx (same {Γ , T}) = Γ
subCtx (next {_} {_} {T} pre) = subCtx pre , T

varSub : ∀{Γ A B Γ' Γ''} → (x : (Γ' , A) pre Γ)
  → (Γ'' , B) pre Γ → ((Γ' ≡ Γ'') × (B ≡ A)) ⊎ (Σ Ctx (λ Γ''' → (Γ''' , B) pre (subCtx x)))
varSub same same = inj₁ (refl , refl)
varSub same (next y) = inj₂ (_ , y) -- TODO: why is this different than InCtx version?
varSub (next x) same = inj₂ (_ , same)
varSub (next x) (next y) with varSub x y
... | inj₁ p = inj₁ p
... | inj₂ (Γ''' , x') = inj₂ (Γ''' , next x')

data Nf : Ctx → Type → Set -- where

data Args : Ctx → Type → (output : Type) → Set where
  none : ∀{Γ} → Args Γ base base -- TODO: should be only for base?
  one : ∀{Γ A B out} → Args Γ B out → Nf Γ A → Args Γ (A ⇒ B) out

-- data Ne : Ctx → Type → Set where
--   var : ∀{Γ' T Γ} → (Γ' , T) pre Γ → Ne Γ T
--   app : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
--   ⋆ : ∀{Γ} → Ne Γ base
--   -- varapp : ∀{Γ' Γ T out} → (args : Args Γ T out)
--     -- → (x : (Γ' , T) pre Γ)
--     -- → Ne Γ out

data Nf where
  lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
  -- ne : ∀{Γ} → Ne Γ base → Nf Γ base
  ⋆ : ∀{Γ} → Nf Γ base
  varapp : ∀{Γ' Γ T out}
    → (x : (Γ' , T) pre Γ)
    → (args : Args Γ T out)
    → Nf Γ out

mutual
  weakenNf : ∀{Γ₁ Γ₂ T} → Γ₁ pre Γ₂ → Nf Γ₁ T → Nf Γ₂ T
  weakenNf pr (lambda e) = lambda (weakenNf {! pr  !} e)
  weakenNf pr ⋆ = ⋆
  weakenNf pr (varapp x args) = varapp (transpre x pr) (weakenArgs pr args)

  weakenArgs : ∀{Γ₁ Γ₂ T out} → Γ₁ pre Γ₂ → Args Γ₁ T out → Args Γ₂ T out

-- joinCounts : ∀{T} → (count₁ : ArgCount T) → (count₂ : ArgCount (output count₁))
--   → ArgCount T
-- joinCounts none count₂ = count₂
-- joinCounts (one count₁) count₂ = one (joinCounts count₁ count₂)
--
-- joinInputs : ∀{T Γ} → (count₁ : ArgCount T) → (count₂ : ArgCount (output count₁))
--   → inputs count₁ Γ → inputs count₂ Γ → inputs (joinCounts count₁ count₂) Γ
-- joinInputs none count₂ tt args₂ = args₂
-- joinInputs (one count₁) count₂ (e , args₁) args₂
--   = e , joinInputs count₁ count₂ args₁ args₂
--
-- joinOutputs : ∀{T} → (count₁ : ArgCount T) → (count₂ : ArgCount (output count₁))
--   → output (joinCounts count₁ count₂) ≡ output count₂
-- joinOutputs none count₂ = refl
-- joinOutputs (one count₁) count₂ = joinOutputs count₁ count₂
mutual
  subv : ∀{Γ' Γ T T'} → (x : (Γ' , T) pre Γ)
    → (toSub : Nf Γ' T) → Nf Γ T' → Nf (subCtx x) T'
  subv x toSub (lambda e) = lambda (subv (next x) toSub e)
  subv x toSub ⋆ = ⋆
  subv x toSub (varapp y args) with varSub x y
  ... | inj₁ (p , refl) = appv {!  weakenNf (transpre (next same) x) toSub  !} (subArgs x toSub args)
  ... | inj₂ (Γ''' , x') = varapp x' (subArgs x toSub args)
  appv : ∀{Γ T out} → (e : Nf Γ T) → Args Γ T out → Nf Γ out
  appv e none = e
  appv (varapp x args₁) args₂ = {!   !}
  appv (lambda e) (one args x) = appv (subv same x e) args

  subArgs : ∀{Γ' Γ T T' out} → (x : (Γ' , T) pre Γ)
    → (toSub : Nf Γ' T) → Args Γ T' out → Args (subCtx x) T' out
  subArgs x toSub none = none
  subArgs x toSub (one args e) = one (subArgs x toSub args) (subv x toSub e)
{-


mutual
  subv : ∀{Γ T} → ∀{T'} → (icx : InCtx Γ T)
    → (toSub : Nf (subCtx icx) T) → Nf Γ T' → Nf (subCtx icx) T'
  subv icx toSub (lambda v) = lambda (subv (next icx) (weakenV same _ toSub) v)
  subv icx toSub (fromU z) = fromU z
  subv icx toSub (fromU (s x)) = fromU (s (subv icx toSub x))
  subv icx toSub (fromU (varapp count x args)) with varSub icx x
  ... | inj₁ refl = appv toSub count (subInputs icx toSub count args)
  ... | inj₂ x' = fromU (varapp count x' (subInputs icx toSub count args))
  appv : ∀{Γ T} → (e : Nf Γ T)
    → (count : ArgCount T) → inputs count Γ → Nf Γ (output count)
  appv (lambda e) none tt = lambda e
  appv {_} {A ⇒ B} (lambda e) (one count) (a , inputs)
    = appv {_} {B} (subv {_} {A} same a e) count inputs
  appv (fromU z) none tt = fromU z
  appv (fromU (s x)) none tt = fromU (s x)
  appv (fromU (varapp count₁ icx args₁)) count₂ args₂
    = fromU (subst (λ T → Ne _ T) (joinOutputs count₁ count₂)
        (varapp (joinCounts count₁ count₂) icx (joinInputs _ _ args₁ args₂)))

  subInputs : ∀{Γ T} → ∀{T'} → (icx : InCtx Γ T)
    → (toSub : Nf (subCtx icx) T) → (count : ArgCount T')
    → inputs count Γ → inputs count (subCtx icx)
  subInputs icx toSub none tt = tt
  subInputs icx toSub (one count) (e , inputs)
    = subv icx toSub e , subInputs icx toSub count inputs

id : Nf ∅ (Nat ⇒ Nat)
id = lambda (fromU (varapp none same tt ))

uno : Nf ∅ Nat
uno = fromU (s (fromU z))

idOne : Nf ∅ Nat
idOne = appv id (one none) (uno , tt)

test : idOne ≡ uno
test = refl
-}
