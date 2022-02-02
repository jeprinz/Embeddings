open import Data.Nat
{-

What is really so hard about extrinsic anyway?
Can I translate my paper proof of consistency to Agda?
In the paper proof, I never need to prove commutativity of anything
I think?

Things which can be intrinsic to a term:
Context? (at least it's length) (proving normalization terminates doesn't actually require knowing the types in the context...)
Spine? only really needed on types...
Level

Term should be annotated - have type annotations on lambda inputs
  (or just on every term)


----------------------------------------------------
Does my simple proof work on dep thy, not just sys F?
Π (a : A) B

-}

data Context : Set -- where
data Var : Context → ℕ → Set -- where
data Type : Context → ℕ → Set -- where
data Ne : Context → ℕ → Set -- where
data Nf : Context → ℕ → Set -- where
data Context where
  ∅ : Context
  _,_ : ∀{n} → (Γ : Context) → Type Γ n → Context
data Var where
  same : ∀{Γ n} → {T : Type Γ n} → Var (Γ , T) n
  next : ∀{Γ n m} → {T : Type Γ m} → Var Γ n → Var (Γ , T) n
data Type where
  U : ∀{Γ n} → Type Γ (suc n)
  Π : ∀{Γ n} → (A : Type Γ n) → Type (Γ , A) n → Type Γ n
  fromNe : ∀{Γ n} → Ne Γ n → Type Γ n
  Lift : ∀{Γ n} → Type Γ n → Type Γ (suc n)
data Ne where
  var : ∀{Γ n} → Var Γ n → Ne Γ n
  app : ∀{Γ n} → Ne Γ n → Nf Γ n → Ne Γ n
  lower : ∀{Γ n} → Ne Γ (suc n) → Ne Γ n
data Nf where
  fromNe : ∀{Γ n} → Ne Γ n → Nf Γ n -- only when of type Ne, so as not to duplicate fromType(fromNe e). Also keeps things expanded η !!!
  fromType : ∀{Γ n} → Type Γ n → Nf Γ n
  lambda : ∀{Γ n} → {A : Type Γ n} → Nf (Γ , A) n → Nf Γ n -- should there be two different levels here?
  lift : ∀{Γ n} → Nf Γ n → Nf Γ (suc n)

Ren : Context → Context → Set
Ren Γ₁ Γ₂ = ∀{n} → Var Γ₁ n → Var Γ₂ n

-- Define eval as relation on preterms, then later as function
-- on WF-terms!!!

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

appendRen : ∀{Γ₁ Γ₂ n} → {T : Type Γ₂ n} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
appendRen ren x = next (ren x)

renType : ∀{n Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Type Γ₁ n → Type Γ₂ n
renNe : ∀{n Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Ne Γ₁ n → Ne Γ₂ n
renNf : ∀{n Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Nf Γ₁ n → Nf Γ₂ n

liftRen : ∀{Γ₁ Γ₂ n} → {T : Type Γ₁ n} → (ren : Ren Γ₁ Γ₂)
  → Ren (Γ₁ , T) (Γ₂ , renType ren T)
liftRen ren same = same
liftRen ren (next x) = next (ren x)

renType ren U = U
renType ren (Π A B) = Π (renType ren A) (renType (liftRen ren) B)
renType ren (fromNe e) = fromNe (renNe ren e)
renType ren (Lift T) = Lift (renType ren T)

renNe ren (var x) = var (ren x)
renNe ren (app e₁ e₂) = app (renNe ren e₁) (renNf ren e₂)
renNe ren (lower e) = lower (renNe ren e)

renNf ren (fromNe e) = fromNe (renNe ren e)
renNf ren (fromType T) = fromType (renType ren T)
renNf ren (lambda e) = lambda (renNf (liftRen ren) e)
renNf ren (lift e) = lift (renNf ren e)

data WFVar : ∀{n} → (Γ : Context) → Type Γ n → Var Γ n → Set where -- \ni
  same : ∀{Γ n} → {T : Type Γ n}
    → WFVar (Γ , T) (renType (appendRen idRen) T) same -- but T needs to be weakened!
  next : ∀{Γ n m} → {T : Type Γ n} → {A : Type Γ m} → {x : Var Γ n}
    → WFVar Γ T x
    → WFVar (Γ , A) (renType (appendRen idRen) T) (next x) -- but T needs to be weakened!

WFRen : ∀{Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Set
WFRen {Γ₁} {Γ₂} ren = ∀{n} → (T : Type Γ₁ n) → {x : Var Γ₁ n}
  → WFVar Γ₁ T x → WFVar Γ₂ (renType ren T) (ren x)

data SemTzero : Context → Set where
    fromNe : ∀{Γ} → Ne Γ 1  → SemTzero Γ
ESemzero : (Γ : Context) →  SemTzero Γ → Set
ESemzero Γ (fromNe e) = Nf Γ 1 -- TODO: should be Ne? should be 1?

module Esucn (n : ℕ)
  (SemTn : Context → Set)
  (Semn : (Γ : Context) → SemTn Γ → Set)
  where
  mutual
    data ESemTsucn : Context → Set where
      U : {Γ : Context} → ESemTsucn Γ
      fromNe : ∀{Γ} → Ne Γ (suc (suc n)) → ESemTsucn Γ -- why 2 sucs?
      Lift : {Γ : Context} → SemTn Γ → ESemTsucn Γ
      Π : {Γ : Context}
        → (A : ∀{Γ'} → Ren Γ Γ' → ESemTsucn Γ')
        → (B : ∀{Γ'} → (eren : Ren Γ Γ')
            → Semsucn Γ' (A eren) → ESemTsucn Γ')
        → ESemTsucn Γ

    Semsucn : (Γ : Context) → ESemTsucn Γ → Set
    Semsucn Γ U = SemTn Γ
    Semsucn Γ (fromNe e) = Ne Γ (suc n) -- NOTE: if Ne is parametrized specifically by Ne in SHALLOW embedding, then that will help here later...
    Semsucn Γ (Lift T) = Semn Γ T
    Semsucn Γ (Π A B)
      = ∀{Γ'} → (eren : Ren Γ Γ')
        → (a : Semsucn Γ' (A eren))
        → Semsucn Γ' (B eren a)
open Esucn

mutual
  SemT : ℕ → (Γ : Context) → Set
  SemT zero = SemTzero
  SemT (suc n) = ESemTsucn n (SemT n) (Sem {n})

  Sem : ∀{n} → (Γ : Context) → SemT n Γ → Set
  Sem {zero} = ESemzero
  Sem {suc n}   = Semsucn n (SemT n) (Sem {n})

Sub : Context → Context → Set
-- Sub Γ₁ Γ₂ = ∀{n} → Var Γ₁ n → Nf Γ₂ n
Sub Γ₁ Γ₂ = ∀{n} → Var Γ₁ n → Sem Γ₂ n

{-

TODO:
1) define evalT/eval with termination checking off for preterms
2) define reifyT/reify, hopefully without needing termination check off
3) redefine 1 as a relation so that no cheating is needed
4) see how far I can get with defining TYPED versions of the above as FUNCTIONS

-}

-- evalT : ∀{Γ n} → Type Γ n → SemT n Γ
-- evalT {Γ} {zero} T = {!   !}
-- evalT {Γ} {suc n} U = U
-- evalT {Γ} {suc n} (Π A B) = Π (λ ren → evalT (renType ren A)) (λ ren a → {! renType ren B  !})
-- evalT {Γ} {suc n} (fromNe x) = {!   !}
-- evalT {Γ} {suc n} (Lift T) = {!   !}

-- idRenWF : ∀{Γ} → WFRen (idRen {Γ})
-- idRenWF {Γ} U x = x
-- idRenWF {Γ} (Π A B) x = {!   !}
-- idRenWF {Γ} (fromNe x₁) x = {!   !}
-- idRenWF {Γ} (Lift T) x = {! idRenWF T   !}


mutual
  data WFType : ∀{n} → (Γ : Context) → Type Γ n → Set where
    U : ∀{n Γ} → WFType Γ (U {Γ} {n})
    Π : ∀{Γ n} → {A : Type Γ n} → {B : Type (Γ , A) n}
      → WFType Γ A → WFType (Γ , A) B → WFType Γ (Π A B)
    -- fromNe : ∀{Γ n} → Ne Γ n → Type Γ n
    -- Lift : ∀{Γ n} → Type Γ n → Type Γ (suc n)

  data WFContext : Context → Set where
    ∅ : WFContext ∅
    _,_ : ∀{Γ n} → {T : Type Γ n}
      → WFContext Γ → WFType Γ T → WFContext (Γ , T)

  data WFNeutral : ∀{n} → (Γ : Context) → (T : Type Γ n) → Ne Γ n → Set where
    var : ∀{Γ n T} → {x : Var Γ n}
      → WFVar Γ T x → WFNeutral Γ T (var x)
    app : ∀{Γ n} → {A : Type Γ n} → {B : Type (Γ , A) n}
      → ∀{e₁ e₂}
      → WFNeutral Γ (Π A B) e₁
      → WFNormal Γ A e₂
      → WFNeutral Γ {! B !} (app e₁ e₂) -- either syntactic reduction as relation, OR NBE from working99percent-what-is...
    lower : ∀{Γ n T e} → WFNeutral {suc n} Γ (Lift T) e
      → WFNeutral {n} Γ T (lower e)

  data WFNormal : ∀{n} → (Γ : Context) → (T : Type Γ n) → Nf Γ n → Set where
    -- fromNe : ∀{Γ n} → Ne Γ n → Nf Γ n -- only when of type Ne, so as not to duplicate fromType(fromNe e)
    -- fromType : ∀{Γ n} → Type Γ n → Nf Γ n
    lambda : ∀{Γ n} → {A : Type Γ n} → {B : Type (Γ , A) n} → {e : Nf (Γ , A) n}
      → WFNormal (Γ , A) B e → WFNormal Γ (Π A B) (lambda e)
    lift : ∀{Γ n T e} → WFNormal {n} Γ T e
      → WFNormal {suc n} Γ (Lift T) (lift e)
