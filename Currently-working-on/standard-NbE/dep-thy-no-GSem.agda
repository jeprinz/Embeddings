open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Ctx : Set
data Type : Ctx → Set -- where
data SemT : Ctx → Set -- where
data Var : (Γ : Ctx) → Type Γ → Set -- should this be GSemT????
data Ne : (Γ : Ctx) → Type Γ → Set -- where
data Nf : (Γ : Ctx) → Type Γ → Set -- where
data Exp : (Γ : Ctx) → Type Γ → Set -- where


data Ren : Ctx → Ctx → Set
_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃

Sem : ∀{Γ} → SemT Γ → Set

data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → Type Γ → Ctx

data Type where
  U : ∀{Γ} → Type Γ
  Π : ∀{Γ} → (A : Type Γ) → Type (Γ , A) → Type Γ
  ne : ∀{Γ} → Ne Γ U → Type Γ


{-# NO_POSITIVITY_CHECK #-}
data SemT where
  U : ∀{Γ} → SemT Γ
  Π : ∀{Γ} → (A : ∀{Γ'} → Ren Γ Γ' → SemT Γ') -- TODO: its unclear to me if this is the correct generalization of no-GSem NbE for STLC.
    → (∀{Γ'} → (ren : Ren Γ Γ') → Sem (A ren) → SemT Γ') → SemT Γ
  ne : ∀{Γ} → Ne Γ U → SemT Γ

Sem {Γ} U = SemT Γ
Sem {Γ} (Π A B) = ∀{Γ'} → (ren : Ren Γ Γ') → (a : Sem (A ren)) → Sem (B ren a)
Sem {Γ} (ne e) = Nf Γ (ne e)

renSemT : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂) → SemT Γ₁ → SemT Γ₂
renSemT ren U = U
renSemT ren (Π A B) = Π (λ ren₂ → A (ren ∘ ren₂)) (λ ren₂ → B (ren ∘ ren₂))
renSemT ren (ne e) = {!   !}

renSem : ∀{Γ₁ Γ₂ T} → (ren : Ren Γ₁ Γ₂) → Sem T → Sem (renSemT ren T)
renSem ren e = {!   !}

renType : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂) → Type Γ₁ → Type Γ₂

data Ren where
  ∅ : ∀{Γ} → Ren ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂)
    → {T : Type Γ₁}
    → Var Γ₂ (renType ren T)
    → Ren (Γ₁ , T) Γ₂

applyRen : ∀{Γ₁ Γ₂} → {T : Type Γ₁} → (ren : Ren Γ₁ Γ₂) → Var Γ₁ T → Var Γ₂ (renType ren T)
idRen : ∀{Γ} → Ren Γ Γ
append1ren : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
-- TODO: fix names of these renamings things
forget1ren : ∀{Γ₁ Γ₂ T} → (ren : Ren Γ₁ Γ₂) → Ren (Γ₁ , T) (Γ₂ , renType ren T)
forget1ren' : ∀{Γ₁ Γ₂ T} → Ren (Γ₁ , T) Γ₂ → Ren Γ₁ Γ₂

weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)

renType ren U = U
renType ren (Π A B) = Π (renType ren A) (renType (forget1ren ren) B)
renType ren (ne x) = {!   !}

data Var where
  same : ∀{Γ} → {T : Type Γ} → Var (Γ , T) (renType weaken1Ren T)
  next : ∀{Γ} → {T A : Type Γ}
    → Var Γ A → Var (Γ , T) (renType weaken1Ren A)

weaken1Ren {∅} {T} = ∅
weaken1Ren {Γ , A} {T} = cons (append1ren weaken1Ren) {! next same  !}

idRen {∅} = ∅
idRen {Γ , T} = cons weaken1Ren same

append1ren ∅ = ∅
append1ren (cons ren x) = cons (append1ren ren) {! next x  !}

applyRen (cons ren x₁) same = {! renType weaken1Ren T  !}
applyRen (cons ren x₁) (next x) = {!   !}

data Sub : Ctx → Ctx → Set -- where

-- NOTE: Subs should outputs Sems
evalT : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → SemT Γ₂
applySub : ∀{Γ₁ Γ₂} → {T : Type Γ₁} → (sub : Sub Γ₁ Γ₂) → Var Γ₁ T → Sem (evalT sub T) -- sort of like an induction principle for subs

data Sub where
  ∅ : ∀{Γ} → Sub ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂)
    → {T : Type Γ₁}
    → Sem (evalT sub T)
    → Sub (Γ₁ , T) Γ₂

idSub : ∀{Γ} → Sub Γ Γ
idSub {∅} = ∅
idSub {Γ , T} = {! cons  !}

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR ∅ ren = ∅
transSR (cons sub x) ren = cons (transSR sub ren) {! renSem ren x  !} -- TODO: is this a simple lemma or a dealbreaker? PROBLEM
-- evalT (transSR sub ren) T ≡ renSemT ren (evalT sub T)

reifyT : ∀{Γ} → SemT Γ → Type Γ
evalNe : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Ne Γ₁ T → Sem (evalT sub T)
evalNf : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Nf Γ₁ T → Sem (evalT sub T)
eval : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Exp Γ₁ T → Sem (evalT sub T)
reify : ∀{Γ} → (T : SemT Γ) → Sem T → Nf Γ (reifyT T)


-- lemma1 : ∀{Γ T} → T ≡ subType {Γ} idSub T

data Ne where
  var : ∀{Γ T} → Var Γ T → Ne Γ T
  app : ∀{Γ A B} → Ne Γ (Π A B) → (x : Nf Γ A)
    → Ne Γ (reifyT (evalT (cons idSub (evalNf idSub x)) B))
data Nf where
  lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (Π A B)
  fromType : ∀{Γ} → Type Γ → Nf Γ U
  -- ne : ∀{Γ T} → Ne Γ T → Nf Γ T -- would have some duplication with fromType!
  ne : ∀{Γ e} → Ne Γ (ne e) → Nf Γ (ne e) -- keeps things in expanded eta form, and prevents duplication with fromType. Need to think how cumu constructor of SemT would come in if that existed.

evalT sub U = U
evalT sub (Π A B) = Π (λ ren → evalT (transSR sub ren) A)
  (λ ren a → evalT (cons (transSR sub ren) a) B)
evalT sub (ne e) = evalNe sub e

-- TOOD: maybe Ne in particular should be parametrized by Sem?
-- TODO? the type of this is wierd, because Ne and Sem use different kinds of types.
nApp : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Ne Γ₁ T → Sem (evalT sub T)

reifyT U = U
reifyT {Γ} (Π A B) = Π (reifyT (A idRen)) (reifyT (B (weaken1Ren {Γ} {reifyT (A idRen)}) {!   !} )) -- nApp is just ne constructor of SemT. TODO: was the Π case in SemT and Sem correct?
-- reifyT {Γ} (Π A B) = Π (reifyT (A idRen)) (reifyT {! B (append1ren idRen)   !})
reifyT (ne e) = ne e

-- nApp {_} {_} {U} e = {!   !}
-- nApp {_} {A ⇒ B} e = λ ren g → nApp (app (renNe ren e) (reify g))
-- nApp {_} {_} {Π A B} e = λ ren a → nApp (app {! renNe ren e  !} {!   !})
-- nApp {_} {_} {ne T} e = {! e  !}

data Exp where
  var : ∀{Γ T} → Var Γ T → Exp Γ T
  app : ∀{Γ A B} → Exp Γ (Π A B) → (x : Exp Γ A)
    → Exp Γ (reifyT (evalT (cons idSub (eval idSub x)) B))
  lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (Π A B)
  fromType : ∀{Γ} → Type Γ → Exp Γ U
  U : ∀{Γ} → Exp Γ U
  Π : ∀{Γ} → (A : Exp Γ U) → Exp (Γ , reifyT (eval idSub A)) U → Exp Γ U

idSubEx : Sub ((∅ , U) , U) ((∅ , U) , U)
idSubEx = cons (cons ∅ (ne (var same))) (ne (var same))

evalNf sub (lambda e) = λ ren a → evalNf (cons (transSR sub ren) a) e
evalNf sub (fromType T) = evalT sub T
evalNf sub (ne e) = evalNe sub e

evalNe sub (var x) = applySub sub x
-- evalNe sub (app e₁ e₂) = {! (evalNe sub e₁) idRen (evalNf (transSR sub idRen) e₂)  !} -- PROBLEM - this appears to require reifyT (eval ? B) ≡ ?B.
evalNe sub (app e₁ e₂) = {! (evalNe idSub e₁)  !}
-- Maybe can get away with defining renaming in terms of Sub and (transSR idSub ren), and then I don't have to prove it? Otherwise, seems to be a fundamental issue.

reify U e = fromType (reifyT e)
reify (Π A B) e = lambda {! reify  !}
reify (ne T) e = e

-- THE BIG QUESTION IS:
-- Can this file be finished merely with simple lemmas about Ren and Sub
-- like (renType idRen T ≡ T), or will
-- it require crazy lemmas, something like
-- reifyT (evalT idSub T) ≡ T
-- See: wherever I wrote "PROBLEM"

testLemma : ∀{Γ₁ Γ₂ T} → {ren : Ren Γ₁ Γ₂}
  → reifyT (evalT (transSR idSub ren) T) ≡ renType ren T
testLemma {_} {_} {U} = refl
testLemma {_} {_} {Π A B} = {! cong₂ SemT.Π !}
testLemma {_} {_} {ne x} = {!   !}
