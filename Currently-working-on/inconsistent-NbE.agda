open import Data.Unit
open import Data.Nat
-- open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

{-

Goal: ignore consistency in every way, and just try to make it typecheck.
(e.g, a language where there are no termination/consistency guaruntees, but
there are still guaruntees that IF a term terminates, then it is of the right
type.)

-}

data Context : Set -- where
data SemT : Context → Set -- where
Sem : (Γ : Context) → SemT Γ → Set
data Type : (Γ : Context) → Set -- where
data Nf : (Γ : Context) → Type Γ → Set -- where
data Ne : (Γ : Context) → Type Γ → Set -- where
data Term : (Γ : Context) → Type Γ → Set -- where
data Var : (Γ : Context) → Type Γ → Set -- where
data Ren : Context → Context → Set -- where
data Sub : Context → Context → Set -- where

{-# NO_POSITIVITY_CHECK #-}
data Context where
  ∅ : Context
  _,_ : (Γ : Context) → Type Γ → Context

renSemT : ∀{Γ Γ'} → Ren Γ Γ' → SemT Γ → SemT Γ'
renType : ∀{Γ Γ'} → Ren Γ Γ' → Type Γ → Type Γ'
renSem : ∀{Γ Γ' T} → (ren : Ren Γ Γ') → Sem Γ T → Sem Γ' (renSemT ren T)
renVar : ∀{Γ Γ' T} → (ren : Ren Γ Γ')
  → Var Γ T → Var Γ' (renType ren T)
idRen : ∀{Γ} → Ren Γ Γ
weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)

subSemT : ∀{Γ Γ'} → Sub Γ Γ' → SemT Γ → SemT Γ'

data Type where
  U : ∀{Γ} → Type Γ
  Π : ∀{Γ} → (A : Type Γ) → Type (Γ , A) → Type Γ
  fromNe : ∀{Γ} → Ne Γ U → Type Γ

data SemT where
  U : ∀{Γ} → SemT Γ
  Π : ∀{Γ} → (A : ∀{Γ'} → Ren Γ Γ' → SemT Γ')
    → (B : ∀{Γ'} → (ren : Ren Γ Γ') → Sem Γ' (A ren) → SemT Γ')
    → SemT Γ
  Π' : ∀{Γ} → (A : SemT Γ)
    → (B : ∀{Γ'} → (ren : Ren Γ Γ') → Sem Γ' (renSemT ren A) → SemT Γ')
    → SemT Γ
  fromNe : ∀{Γ} → Ne Γ U → SemT Γ

-- TODO: type of reflect???? this can't be right.
-- reflect : ∀{Γ e} → Ne Γ (fromNe e) → Sem Γ (fromNe e)
{-# TERMINATING #-}
reifyT : ∀{Γ} → SemT Γ → Type Γ
reify : ∀{Γ T} → Sem Γ T → Nf Γ (reifyT T)
reflect : ∀{Γ T} → Ne Γ (reifyT T) → Sem Γ T
evalT : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → SemT Γ₂
eval : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Term Γ₁ T → Sem Γ₂ (evalT sub T)

-- Sem : (Γ : Context) → SemT Γ → Set
Sem Γ U = SemT Γ
Sem Γ (Π A B) = ∀{Γ'} → (ren : Ren Γ Γ')
      → (a : Sem Γ' (A ren)) → Sem Γ' (B ren a)
Sem Γ (Π' A B) = ∀{Γ'} → (ren : Ren Γ Γ')
      → (a : Sem Γ A) → Sem Γ' (B ren (renSem ren a))
Sem Γ (fromNe e) = Ne Γ (fromNe e) -- TODO: should this be Nf?

data Var where
  same : ∀{Γ T} → Var (Γ , T) (renType weaken1Ren T)
  next : ∀{Γ T A} → Var Γ A → Var (Γ , T) (renType weaken1Ren A)

data Nf where
data Ne where
  var : ∀{Γ T} → Var Γ T → Ne Γ T
  -- app : ∀{Γ A B} → Ne Γ (Π A B) → (a : Ne Γ A)
  --   → Ne Γ {!   !}

subVar : ∀{Γ Γ' T} → (sub : Sub Γ Γ')
  → Var Γ T → Sem Γ' (evalT sub T)

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
append1sub : ∀{Γ₁ Γ₂ A} → (sub : Sub Γ₁ Γ₂)
  → Sem Γ₂ (evalT sub A) → Sub (Γ₁ , A) Γ₂
idSub : ∀{Γ} → Sub Γ Γ

-- TODO: what why this function?
fromNf : ∀{Γ} → Nf Γ U → Type Γ

reifyT U = U
reifyT (Π A B) = Π (reifyT (A idRen))
  (reifyT (B weaken1Ren (reflect (var {! same  !}))))
reifyT (Π' A B) = Π (reifyT A)
  (reifyT (B weaken1Ren (reflect (var {! same  !}))))
reifyT (fromNe x) = fromNe x

data Term where
  var : ∀{Γ T} → Var Γ T → Term Γ T
  lambda : ∀{Γ A B}
    → Term (Γ , A) B → Term Γ (Π A B)
  app : ∀{Γ A B} → Term Γ (Π A B) → (a : Term Γ A)
    → Term Γ (fromNf (reify (evalT (append1sub idSub (eval idSub a)) B)))
    -- TODO: the million dollar question: will the nonsense in the above line
    -- require equality proofs later on? If not, then this technique probably
    -- has something to it. If so, then probably not.
    -- TODO: the thing that Term and Sem are paremetrized by must already
    -- have all the good properties of an embedding, like Aug Shal for example.
    -- look at param-by-sem version again!

data Ren where -- intuitively, think of this as corresponding to racket implementation where it is a list
  ∅ : ∀{Γ} → Ren ∅ Γ
  _,_ : ∀{Γ₁ Γ₂ T}
    → (ren : Ren Γ₁ Γ₂)
    → Var Γ₂ (renType ren T)
    → Ren (Γ₁ , T) Γ₂
-- data Sub where
--   ∅ : ∀{Γ} → Sub ∅ Γ
--   _,_ : ∀{Γ₁ Γ₂ T}
--     → (sub : Sub Γ₁ Γ₂)
--     → Sem Γ₂ (subSemT sub T)
--     → Sub (Γ₁ , T) Γ₂

-- leave ren and sub stuff as holes, and just see if rest works..

-- reify : ∀{Γ T} → Sem Γ T → Nf Γ T
-- eval : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Term Γ₁ T → Sem Γ₂ (subSemT sub T)
-- reifyT : ∀{Γ} → SemT Γ → Type Γ
-- evalT : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → SemT Γ₂
evalT sub U = U
evalT sub (Π A B)
  = Π (λ ren → evalT (transSR sub ren) A)
      (λ ren a → evalT (append1sub (transSR sub ren) a) B)
evalT sub (fromNe e) = {!   !}

eval sub (var x) = subVar sub x
eval sub (lambda e) = λ ren a → eval ((append1sub (transSR sub ren) a)) e
eval sub (app e₁ e₂) = {! (eval sub e₁) idRen ?  !}

-- we need that (weaken (reify T)) = reify (weaken T)
-- proper subtyping should somehow just inherently deal with this?
-- subtyping via self types?

-- reflect : ∀{Γ T} → Ne Γ (reifyT T) → Sem Γ T
reflect {Γ} {U} e = fromNe e
reflect {Γ} {Π A B} e = λ ren a → reflect {! app  !}
  -- nApp {_} {A ⇒ B} e = λ ren g → nApp  (app (renNe ren e) (reify g))
reflect {Γ} {Π' A B} e = {!   !}
reflect {Γ} {fromNe T} e = e
