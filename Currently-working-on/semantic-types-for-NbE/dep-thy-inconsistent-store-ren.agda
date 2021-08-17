open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

{-

Idea of approach is to store pairs (Renaming , type), and
update the renaming most of the time, and only update the type when absolutely necessary.
These pairs are called GGSemT. They have a GSemT, but I think this needs to be
reworked with the standard NbE approach and use SemT directly, and then renNf
and renSem.

Contexts are lists of GGSemTs.

The idea is that commutativity can be proven on ONLY renamings (and if renamings)
are functions, then its just definitionally true. Nf, Sem, Ne are all still parametrized
by SemT. So for example, the lambda constructor of Nf,
  lambda : ∀{A B} → Exp (Γ , (idRen , A)) B → Exp Γ (Π A B)            NOTE - correspondence of A needing to be GSemT in both spaces (as opposed to SemT)
    TODO: No, B doesn't fit above, it is in different context in two places.
  var : ∀{A} → Exp (Γ , (ren , A)) (A ren)

TODO: is this really better than the "all-GSem" version, where Var is parametrized
by GSem? Surely that should have the same property that it "would work if
∘ was associative"
-}

data Ctx : Set

data SemT : Ctx → Set -- where
GSemT : Ctx → Set
data Ne : (Γ : Ctx) → SemT Γ → Set -- where
data Nf : (Γ : Ctx) → SemT Γ → Set -- where

data Ren : Ctx → Ctx → Set -- where

GSemT Γ = ∀{Γ'} → Ren Γ Γ' → SemT Γ'

GGSemT : Ctx → Set
GGSemT Γ = Σ Ctx (λ Γpre → (Ren Γpre Γ) × GSemT Γpre)

-- data Var : (Γpre Γ : Ctx) → Ren Γpre Γ → GSemT Γpre → Set -- where
data Var : (Γ : Ctx) → GGSemT Γ → Set -- where
-- putting a Ren here is like storing an amount to weaken by in Racket implementation.

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
  _,_ : (Γ : Ctx) → GGSemT Γ → Ctx -- this holds GSemT's rather than SemTs because Subs have GSems, not Sems.?

_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
renSemT : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂) → SemT Γ₁ → SemT Γ₂
-- applyRen : ∀{Γ₁ Γ₂} → {T : SemT Γ₁} → (ren : Ren Γ₁ Γ₂) → Var Γ₁ T → Var Γ₂ (renSemT ren T)
applyRen : ∀{Γ₁ Γ₂ Γpre preren} → {T : GSemT Γpre}
  → (ren : Ren Γ₁ Γ₂) → Var Γ₁ (Γpre , preren , T) → Var Γ₂ (Γpre , (preren ∘ ren) , T)
idRen : ∀{Γ} → Ren Γ Γ
append1ren : ∀{Γ₁ Γ₂} → {T : GGSemT Γ₂} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
data Ren where
  ∅ : ∀{Γ} → Ren ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂)
    → {(Γpre , preren , T) : GGSemT Γ₁}
    → Var Γ₂ (Γpre , (preren ∘ ren) , T)
    → Ren (Γ₁ , (Γpre , preren , T)) Γ₂
  -- cons2 : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂)
    -- → {T : GSemT Γ₁}
    -- → Var Γ₁ Γ₂ ren T
    -- → Ren (Γ₁ , T) Γ₂

Ron : Ctx → Ctx → Set
Ron Γ₁ Γ₂ = {(Γpre , ren , T) : GGSemT Γ₁}
  → Var Γ₁ (Γpre , ren , T) → Var Γ₂ (Γpre , (ren ∘ {!   !}) , T)

-- weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)
-- weaken1Ren {∅} {T} = ∅
-- weaken1Ren {Γ , A} {T} = cons (append1ren weaken1Ren) {!   !}

-- data Var : (Γ : Ctx) → GGSemT Γ → Set -- where
data Var where
  same : ∀{Γ} → {(Γpre , ren , T) : GGSemT Γ}
    → Var (Γ , (Γpre , ren , T)) (Γpre , append1ren ren , T)
  next : ∀{Γ} → {(Γpre , ren , A) T : GGSemT Γ}
    → Var Γ (Γpre , ren , A) → Var (Γ , T) (Γpre , append1ren ren , A)
  -- same : ∀{Γ} → {T : SemT Γ} → Var (Γ , T) (renSemT (append1ren idRen) T)
  -- next : ∀{Γ} → {T A : SemT Γ}
    -- → Var Γ A → Var (Γ , T) (renSemT (append1ren idRen) A)

assoc : ∀{Γ₁ Γ₂ Γ₃ Γ₄}
  → (ren₁ : Ren Γ₁ Γ₂) → (ren₂ : Ren Γ₂ Γ₃) → (ren₃ : Ren Γ₃ Γ₄)
  → (ren₁ ∘ ren₂) ∘ ren₃ ≡ ren₁ ∘ (ren₂ ∘ ren₃)

∅ ∘ ren₂ = ∅
cons ren₁ x ∘ ren₂ = cons (ren₁ ∘ ren₂)
  (subst (λ ren → Var _ (_ , ren , _)) (assoc _ _ _) (applyRen ren₂ x))

assoc ∅ ren₂ ren₃ = refl
assoc (cons ren₁ x) ren₂ ren₃ with assoc ren₁ ren₂ ren₃
... | res = {! res  !}

append1ren ∅ = ∅
append1ren (cons ren x) = cons (append1ren ren) {! next x  !}

-- NOTE: what would be necessary above is:
-- THIS WORKS IF REN IS FUNCTION!!!!! Also, if prove ∘ commutes, then
-- can express append1ren in terms of weaken1Ren and ∘.
lemma : ∀{Γ₁ Γ₂ Γ₃} → {T : GGSemT Γ₃}
  → (ren₁ : Ren Γ₁ Γ₂) → (ren₂ : Ren Γ₂ Γ₃)
  → append1ren {Γ₁} {Γ₃} {T} (ren₁ ∘ ren₂) ≡ ren₁ ∘ (append1ren ren₂)
lemma ren₁ ren₂ = {!   !}
{-

idRen {∅} = ∅
idRen {Γ , T} = cons (append1ren idRen) same


renSemT ren U = U
renSemT ren (Π A B) = Π (λ ren₂ → A (ren ∘ ren₂)) (λ a → {! B a  !} )
renSemT ren (ne e) = {!   !}
applyRen (cons ren x₁) same = {! x₁  !}
applyRen (cons ren x₁) (next x) = {!   !}



data Ne where
data Nf where
  U : ∀{Γ} → Nf Γ U
-}
