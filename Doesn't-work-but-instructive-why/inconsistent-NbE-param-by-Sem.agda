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

What goes wrong: renaming and substitution laws as per usual. Also, see line
111 where I wrote "HERE" in a comment. It is unclear to me what goes there!

IDEA: maybe make the "B" in "Π A B" be of type
SemT Γ (Π A U)
instead of
SemT (Γ , A) U
and then I can use application instead of substitution?
wait no... that already is how it is?

-}

data Context : Set -- where
data SemT : Context → Set -- where
Sem : (Γ : Context) → SemT Γ → Set
data Term : (Γ : Context) → SemT Γ → Set -- where
data Nf : (Γ : Context) → SemT Γ → Set -- where
data Ne : (Γ : Context) → SemT Γ → Set -- where
data Var : (Γ : Context) → SemT Γ → Set -- where
data Ren : Context → Context → Set -- where
data Sub : Context → Context → Set -- where

{-# NO_POSITIVITY_CHECK #-}
data Context where
  ∅ : Context
  _,_ : (Γ : Context) → SemT Γ → Context

renSemT : ∀{Γ Γ'} → Ren Γ Γ' → SemT Γ → SemT Γ'
renSem : ∀{Γ Γ' T} → (ren : Ren Γ Γ') → Sem Γ T → Sem Γ' (renSemT ren T)
renVar : ∀{Γ Γ' T} → (ren : Ren Γ Γ')
  → Var Γ T → Var Γ' (renSemT ren T)
idRen : ∀{Γ} → Ren Γ Γ
weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)

subSemT : ∀{Γ Γ'} → Sub Γ Γ' → SemT Γ → SemT Γ'

reflect : ∀{Γ T} → Ne Γ T → Sem Γ T
reify : ∀{Γ T} → Sem Γ T → Nf Γ T
eval : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Term Γ₁ T → Sem Γ₂ (subSemT sub T)

data SemT where
  U : ∀{Γ} → SemT Γ
  Π : ∀{Γ} → (A : ∀{Γ'} → Ren Γ Γ' → SemT Γ')
    → (B : ∀{Γ'} → (ren : Ren Γ Γ') → Sem Γ' (A ren) → SemT Γ')
    → SemT Γ
  Π' : ∀{Γ} → (A : SemT Γ)
    → (B : ∀{Γ'} → (ren : Ren Γ Γ') → Sem Γ' (renSemT ren A) → SemT Γ')
    → SemT Γ
  fromNe : ∀{Γ} → Ne Γ U → SemT Γ

{-
What I really want is that if Γ < Γ', then
SemT Γ ⊆ SemT Γ'
So that
Π : (A : SemT Γ) → (Sem Γ A → SemT Γ) → SemT Γ

-}

-- Sem : (Γ : Context) → SemT Γ → Set
Sem Γ U = SemT Γ
Sem Γ (Π A B) = ∀{Γ'} → (ren : Ren Γ Γ')
      → (a : Sem Γ' (A ren)) → Sem Γ' (B ren a)
Sem Γ (Π' A B) = ∀{Γ'} → (ren : Ren Γ Γ')
      → (a : Sem Γ A) → Sem Γ' (B ren (renSem ren a))
Sem Γ (fromNe e) = Nf Γ (fromNe e)

data Var where
  same : ∀{Γ T} → Var (Γ , T) (renSemT weaken1Ren T)
  next : ∀{Γ T A} → Var Γ A → Var (Γ , T) (renSemT weaken1Ren A)

data Nf where
data Ne where
  var : ∀{Γ T} → Var Γ T → Ne Γ T

data Term where
  var : ∀{Γ T} → Var Γ T → Term Γ T
  lambda : ∀{Γ} → {A : ∀{Γ'} → Ren Γ Γ' → SemT Γ'}
    → {B : ∀{Γ'} → (ren : Ren Γ Γ') → Sem Γ' (A ren) → SemT Γ'}
    → Term (Γ , A idRen) (B weaken1Ren (reflect {! Ne.var same  !} ) )
    → Term Γ (Π A B)
  lambda' : ∀{Γ} → {A : SemT Γ}
    → {B : ∀{Γ'} → (ren : Ren Γ Γ') → Sem Γ' (renSemT ren A) → SemT Γ'}
    → Term (Γ , A) (B weaken1Ren (reflect (Ne.var same)))
    → Term Γ (Π' A B)

data Ren where -- intuitively, think of this as corresponding to racket implementation where it is a list
  ∅ : ∀{Γ} → Ren ∅ Γ
  _,_ : ∀{Γ₁ Γ₂ T}
    → (ren : Ren Γ₁ Γ₂)
    → Var Γ₂ (renSemT ren T)
    → Ren (Γ₁ , T) Γ₂
data Sub where
  ∅ : ∀{Γ} → Sub ∅ Γ
  _,_ : ∀{Γ₁ Γ₂ T}
    → (sub : Sub Γ₁ Γ₂)
    → Sem Γ₂ (subSemT sub T)
    → Sub (Γ₁ , T) Γ₂

subVar : ∀{Γ Γ' T} → (sub : Sub Γ Γ')
  → Var Γ T → Sem Γ' (subSemT sub T)

subSemT sub U = U
subSemT sub (Π A B) = {!   !}
subSemT sub (Π' A B) = Π' (subSemT sub A) (λ ren a → {!   !}) -- HERE - what even on paper would I want this to mean here?
subSemT sub (fromNe e) = {!   !}

-- leave ren and sub stuff as holes, and just see if rest works..

-- reflect : ∀{Γ T} → Ne Γ T → Sem Γ T
-- reify : ∀{Γ T} → Sem Γ T → Nf Γ T
-- eval : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Term Γ₁ T → Sem Γ₂ (subSemT sub T)
eval sub (var x) = subVar sub x
eval sub (lambda e) = {!   !}
eval sub (lambda' e) = {!   !}
