open import Data.Unit
open import Data.Product

data Ctx : Set

data SemT : Ctx → Set -- where
data Var : (Γ : Ctx) → SemT Γ → Set -- should this be GSemT????
data Ne : (Γ : Ctx) → SemT Γ → Set -- where
data Nf : (Γ : Ctx) → SemT Γ → Set -- where

data Ren : Ctx → Ctx → Set
-- Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ {! T  !}
_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃

Sem : ∀{Γ} → SemT Γ → Set

{-# NO_POSITIVITY_CHECK #-}
data SemT where
  U : ∀{Γ} → SemT Γ
  Π : ∀{Γ} → (A : ∀{Γ'} → Ren Γ Γ' → SemT Γ')
    → (∀{Γ'} → (ren : Ren Γ Γ') → Sem (A ren) → SemT Γ') → SemT Γ
  ne : ∀{Γ} → Ne Γ U → SemT Γ

Sem {Γ} U = SemT Γ
Sem {Γ} (Π A B) = ∀{Γ'} → (ren : Ren Γ Γ') → (a : Sem (A ren)) → Sem (B ren a)
Sem {Γ} (ne e) = Nf Γ (ne e)

renSemT : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂) → SemT Γ₁ → SemT Γ₂
renSemT ren U = U
renSemT ren (Π A B) = Π (λ ren₂ → A (ren ∘ ren₂)) (λ ren₂ → B (ren ∘ ren₂))
renSemT ren (ne e) = {!   !}

data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → SemT Γ → Ctx

data Ren where
  ∅ : ∀{Γ} → Ren ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (ren : Ren Γ₁ Γ₂)
    → {T : SemT Γ₁}
    → Var Γ₂ (renSemT ren T)
    → Ren (Γ₁ , T) Γ₂

applyRen : ∀{Γ₁ Γ₂} → {T : SemT Γ₁} → (ren : Ren Γ₁ Γ₂) → Var Γ₁ T → Var Γ₂ (renSemT ren T)
idRen : ∀{Γ} → Ren Γ Γ
-- TODO: rename this
append1ren : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)

weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)
weaken1Ren {∅} {T} = ∅
weaken1Ren {Γ , A} {T} = cons (append1ren weaken1Ren) {!   !}

data Var where
  same : ∀{Γ} → {T : SemT Γ} → Var (Γ , T) (renSemT (append1ren idRen) T)
  next : ∀{Γ} → {T A : SemT Γ}
    → Var Γ A → Var (Γ , T) (renSemT (append1ren idRen) A)

idRen {∅} = ∅
idRen {Γ , T} = cons (append1ren idRen) same

append1ren ∅ = ∅
append1ren (cons ren x) = cons (append1ren ren) {! next x  !}

data Sub : Ctx → Ctx → Set -- where
data Type : Ctx → Set -- where

-- NOTE: Subs should outputs Sems
evalT : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → SemT Γ₂
-- TODO TODO TODO!!!! How exactly will SemT get substituted in output here?
-- applySub : ∀{Γ₁ Γ₂} → {T : SemT Γ₁} → (sub : Sub Γ₁ Γ₂) → Var Γ₁ T → Sem (evalT sub T) -- sort of like an induction principle for subs

idSub : ∀{Γ} → Sub Γ Γ

data Type where
  U : ∀{Γ} → Type Γ
  Π : ∀{Γ} → (A : Type Γ) → Type (Γ , evalT idSub A) → Type Γ
  ne : ∀{Γ} → Ne Γ U → Type Γ

data Ne where
  var : ∀{Γ T} → Var Γ T → Ne Γ T
  app : ∀{Γ A B} → Ne Γ (Π A B) → (x : Nf Γ A)
    → Ne Γ ?
data Nf where
  lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (Π {! A  !} {! B  !} )
  fromType : ∀{Γ} → Type Γ → Nf Γ U
  ne : ∀{Γ e} → Ne Γ (ne e) → Nf Γ (ne e) -- keeps things in expanded eta form, and prevents duplication with fromType. Need to think how cumu constructor of SemT would come in if that existed.

{-
data Sub where
  ∅ : ∀{Γ} → Sub ∅ Γ
  cons : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂)
    → {T : Type Γ₁}
    → Sem (evalT sub T)
    → Sub (Γ₁ , T) Γ₂

idSub {∅} = ∅
idSub {Γ , T} = {! cons  !}

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR ∅ ren = ∅
transSR (cons sub x) ren = cons (transSR sub ren) {! renSem ren x  !} -- TODO: is this a simple lemma or a dealbreaker? PROBLEM
-- evalT (transSR sub ren) T ≡ renSemT ren (evalT sub T)

reifyT : ∀{Γ} → SemT Γ → Type Γ
evalNe : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Ne Γ₁ T → Sem (evalT sub T)
evalNf : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Nf Γ₁ T → Sem (evalT sub T)
reify : ∀{Γ} → (T : SemT Γ) → Sem T → Nf Γ (reifyT T)


-- lemma1 : ∀{Γ T} → T ≡ subType {Γ} idSub T

reifyT U = U
reifyT {Γ} (Π A B) = Π (reifyT (A idRen)) (reifyT (B (weaken1Ren {Γ} {reifyT (A idRen)}) {! var same  !} )) -- nApp is just ne constructor of SemT. TODO: was the Π case in SemT and Sem correct?
reifyT (ne e) = ne e

evalT sub U = U
evalT sub (Π A B) = Π (λ ren → evalT (transSR sub ren) A)
  (λ ren a → evalT (cons (transSR sub ren) a) B)
-- evalT sub (ne e) = ne {! reify _ (evalNe sub e)  !}
evalT sub (ne e) with reify _ (evalNe sub e)
... | (fromType T) = {! evalT idSub T  !} -- PROBLEM - what even would go here, even if I could cheese the proofs?


idSubEx : Sub ((∅ , U) , U) ((∅ , U) , U)
idSubEx = cons (cons ∅ (ne (var same))) (ne (var same))

evalNf sub (lambda e) = λ ren a → evalNf (cons (transSR sub ren) a) e
evalNf sub (fromType T) = evalT sub T
evalNf sub (ne e) = evalNe sub e

evalNe sub (var x) = applySub sub x
evalNe sub (app e₁ e₂) = {! (evalNe sub e₁) idRen (evalNf (transSR sub idRen) e₂)  !} -- PROBLEM - this appears to require reifyT (eval ? B) ≡ ?B.
-- Maybe can get away with defining renaming in terms of Sub and (transSR idSub ren), and then I don't have to prove it? Otherwise, seems to be a fundamental issue.

reify U e = fromType (reifyT e)
reify (Π A B) e = lambda {! reify  !}
reify (ne x) e = {! e  !}
-}
