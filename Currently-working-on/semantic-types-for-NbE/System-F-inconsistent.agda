module System-F-inconsistent where

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-

NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE


The idea of this file was to have Exp parametrized by SemT, a semantic domain
sort of way of storing types. The hope was that this would eliminate the need
for proving difficult lemmas about substitution and renaming. Unfortunately,
it didn't.

Maybe there is no way that this can be done. However, one more thing to try is
to make SemT have stuff in context inputted as function. So for example,

T : U ⊢ T : U    would become

ST = λ tren X → X :
∀{Δ'} → TRen ∅ Δ' → SemT Δ' → SemT Δ'

Then, can do either:
ST idRen X
ST weaken1renT (var same)

Hopefully, this would remove the need for substitutions, because instead can work
in terms of these function inputs corresponding to the context.

BUT! its very unclear how this would work. reify and nApp require being able to
pattern match on the types.

Sort of a wierd issue is the difference between (note type contexts can be written as a ℕ which is the number of types in it)
SemT 3
VS
∀{Δ'} → TRen 2 Δ' → SemT Δ' → SemT Δ'
VS
∀{Δ'} → TRen 1 Δ' → SemT Δ' → SemT Δ' → SemT Δ'
VS
∀{Δ'} → TRen ∅ Δ' → SemT Δ' → SemT Δ' → SemT Δ' → SemT Δ'

All of these sort of represent the same thing, but from least to most general
Given an element of one of those, can get an element of each of the above ones.

But then, might as well just have ∅, which brings us back to Core.agda, which can't
do reification.

NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE

-}

data TCtx : Set -- where
data TVar : TCtx → Set -- where
data SemT : TCtx → Set -- where
data Ctx : TCtx → Set -- where
data Var : ∀{Δ} → Ctx Δ → SemT Δ → Set -- where
data Nf : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where
data Ne : (Δ : TCtx) → Ctx Δ → SemT Δ → Set -- where

TRen : TCtx → TCtx → Set
-- Ren : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set -- TODO: maybe this?
Ren : ∀{Δ} → Ctx Δ → Ctx Δ → Set

TRen Δ₁ Δ₂ = TVar Δ₁ → TVar Δ₂
Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ T

TSub : TCtx → TCtx → Set
TSub Δ₁ Δ₂ = TVar Δ₁ → SemT Δ₂

-- BRen : (Δ₁ Δ₂ : TCtx) → Ctx Δ₁ → Ctx Δ₂ → Set
-- BRen Δ₁ Δ₂ Γ₁ Γ₂ =

renTCtx : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂

-- Wait! I think that it should be possible to not have positivity check merely by
-- doing predicative system F. Because of separate Δ and Γ.
{-# NO_POSITIVITY_CHECK #-}
data SemT where
    all : ∀{Δ} → (∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ') → SemT Δ
    var : ∀{Δ} → TVar Δ → SemT Δ
    _⇒_ : ∀{Δ} → SemT Δ → SemT Δ → SemT Δ

Sem : (Δ : TCtx) → SemT Δ → Ctx Δ → Set
Sem Δ (all T) Γ = ∀{Δ'} → (tren : TRen Δ Δ') → (a : SemT Δ') -- how does this relate to TRen in all constructor???
  → Sem Δ' (T tren a) (renTCtx tren Γ)
Sem Δ (A ⇒ B) Γ = ∀{Γ'} → Ren Γ Γ' → Sem Δ A Γ' → Sem Δ B Γ' -- maybe need Δ renaming as well????
Sem Δ (var X) Γ = Nf Δ Γ (var X)

Sub : ∀{Δ} → Ctx Δ → Ctx Δ → Set
Sub Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Sem _ T Γ₂

data TCtx where
  ∅ : TCtx
  S : TCtx → TCtx

data TVar where
  same : ∀{Δ} → TVar Δ
  next : ∀{Δ} → TVar Δ → TVar (S Δ)

idSubT : ∀{Δ} → TSub Δ Δ
idSubT x = var x

idRenT : ∀{Δ} → TRen Δ Δ
idRenT x = x

idRen : ∀{Δ} → {Γ : Ctx Δ} → Ren Γ Γ
idRen x = x

forget1renT : ∀{Δ₁ Δ₂} → TRen (S Δ₁) Δ₂ → TRen Δ₁ Δ₂
forget1renT ren x = ren (next x)

weaken1renT : ∀{Δ} → TRen Δ (S Δ)
weaken1renT x = next x

append1Tsub : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → SemT Δ₂ → TSub (S Δ₁) Δ₂
append1Tsub sub T same = T
append1Tsub sub T (next x) = sub x


renSemT : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → SemT Δ₁ → SemT Δ₂
renSemT tren (all T) = all (λ tren₂ X → T (tren₂ ∘ tren) X) -- huh? no recursion here?
renSemT tren (var x) = var (tren x)
renSemT tren (A ⇒ B) = (renSemT tren A) ⇒ (renSemT tren B)

renSem : ∀{Δ T} → {Γ₁ Γ₂ : Ctx Δ} → Ren Γ₁ Γ₂
  → Sem Δ T Γ₁ → Sem Δ T Γ₂
renSem {_} {all x} ren e = λ tren a → renSem {!   !} (e tren a)
renSem {_} {A ⇒ B} ren e = λ ren₁ a → e (ren₁ ∘ ren) a
renSem {_} {var x} ren e = {! e  !} -- define renNf and renNe for this!!!

transTSR : ∀{Δ₁ Δ₂ Δ₃} → TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
transTSR sub ren x = renSemT ren (sub x)


data Ctx where
  ∅ : ∀{Δ} → Ctx Δ
  _,_ : ∀{Δ} → (Γ : Ctx Δ) → SemT Δ → Ctx Δ

-- renTCtx : ∀{Δ₁ Δ₂} → TRen Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
renTCtx ren ∅ = ∅
renTCtx ren (Γ , T) = renTCtx ren Γ , renSemT ren T

data Var where
  same : ∀{Δ Γ T} → Var {Δ} (Γ , T) T
  next : ∀{Δ Γ T A} → Var {Δ} Γ T → Var (Γ , A) T

-- the equivalent of this would be part of Exp in dep thy version.
-- should be inputted by App constructor.
-- How does this appear in Lambda constructor? Need inference to work...
data Type : TCtx → Set where
  _⇒_ : ∀{Δ} → Type Δ → Type Δ → Type Δ
  all : ∀{Δ} → Type (S Δ) → Type Δ
  var : ∀{Δ} → TVar Δ → Type Δ

evalT : ∀{Δ₁ Δ₂} → Type Δ₁ → TSub Δ₁ Δ₂ → SemT Δ₂
evalT (A ⇒ B) sub = evalT A sub ⇒ evalT B sub
evalT (all T) sub = all (λ tren X → evalT T (append1Tsub (transTSR sub tren) X))
evalT (var x) sub = sub x

reifyT : ∀{Δ} → SemT Δ → Type Δ
reifyT (all T) = all (reifyT (T weaken1renT (var same)))
reifyT (var x) = var x
reifyT (A ⇒ B) = reifyT A ⇒ reifyT B

data Ne where
  var : ∀{Δ Γ T} → Var {Δ} Γ T → Ne Δ Γ T
  app : ∀{Δ Γ A B} → Ne Δ Γ (A ⇒ B) → Nf Δ Γ A → Ne Δ Γ B
  App : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Ne Δ Γ (all T) → (A : Type Δ) → Ne Δ Γ (T idRenT (evalT A idSubT))

data Nf where
  lambda : ∀{Δ Γ A B} → Nf Δ (Γ , A) B → Nf Δ Γ (A ⇒ B)
  Lambda : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Nf (S Δ) (renTCtx weaken1renT Γ) (T weaken1renT (var same))
    → Nf Δ Γ (all T)
  -- ne : ∀{Δ Γ T} → Ne Δ Γ T → Nf Δ Γ T
  ne : ∀{Δ Γ x} → Ne Δ Γ (var x) → Nf Δ Γ (var x) -- restrict to eta-expanded forms

-- what if Exp was parametrized by a Type instead of a SemT????

data Exp : (Δ : TCtx) → Ctx Δ → SemT Δ → Set where
  var : ∀{Δ Γ T} → Var {Δ} Γ T → Exp Δ Γ T
  app : ∀{Δ Γ A B} → Exp Δ Γ (A ⇒ B) → Exp Δ Γ A → Exp Δ Γ B
  lambda : ∀{Δ Γ A B} → Exp Δ (Γ , A) B → Exp Δ Γ (A ⇒ B)
  App : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Exp Δ Γ (all T) → (A : Type Δ) → Exp Δ Γ (T idRenT (evalT A idSubT))
  Lambda : ∀{Δ Γ} → {T : ∀{Δ'} → TRen Δ Δ' → SemT Δ' → SemT Δ'}
    → Exp (S Δ) (renTCtx weaken1renT Γ) (T weaken1renT (var same))
    → Exp Δ Γ (all T)

renidSemT≡ : ∀{Δ} → {T : SemT Δ} → renSemT idRenT T ≡ T
renidSemT≡ {_} {all T} = refl
renidSemT≡ {_} {var x} = refl
renidSemT≡ {_} {A ⇒ B} = cong₂ _⇒_ renidSemT≡ renidSemT≡

renidCtx≡ : ∀{Δ} → {Γ : Ctx Δ} → renTCtx idRenT Γ ≡ Γ
renidCtx≡ {_} {∅} = refl
renidCtx≡ {_} {Γ , T} = cong₂ _,_ renidCtx≡ renidSemT≡

{-

TODO: I highly suspect that due to the separate contexts in system F, it will be
necessary put also TSub in type of eval in addition to just Sub, or maybe make it so
Sub and Ren have TSub and TRen in them.

See case of Sem where I need to rename context!

-}

append1sub : ∀{Δ A} → {Γ₁ Γ₂ : Ctx Δ} → Sub Γ₁ Γ₂ → Sem Δ A Γ₂ → Sub (Γ₁ , A) Γ₂
append1sub sub e same = e
append1sub sub e (next x) = sub x

transSR : ∀{Δ} → {Γ₁ Γ₂ Γ₃ : Ctx Δ} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
-- transSR sub ren x = renSem ren (sub x)
transSR sub ren x = {! sub x  !}

subSemT : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → SemT Δ₁ → SemT Δ₂
-- subSemT sub (all T) = all (λ tren X → subSemT {!   !} (T {!   !} X))
-- subSemT sub (var x) = sub x
-- subSemT sub (A ⇒ B) = subSemT sub A ⇒ subSemT sub B
subSemT tsub T = evalT (reifyT T) tsub

subCtx : ∀{Δ₁ Δ₂} → TSub Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂
subCtx tsub ∅ = ∅
subCtx tsub (Γ , T) = subCtx tsub Γ , subSemT tsub T

-- subVar : ∀{Δ₁ Δ₂ T} → {Γ : } → TSub Δ₁ Δ₂ → Var Δ₁ T → Var Δ₂ ?
-- subVar tsub same = same
-- subVar tsub (next x) = {!   !}
subVar : ∀{Δ₁ Δ₂ T} → {Γ : Ctx Δ₁} → (tsub : TSub Δ₁ Δ₂)
  → Var Γ T → Var (subCtx tsub Γ) (subSemT tsub T)
subVar tsub same = same
subVar tsub (next x) = next (subVar tsub x)

mutual
  -- nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
  -- nApp {_} {A ⇒ B} e = λ ren g → nApp (app (renNe ren e) (reify g))
  -- nApp {_} {base} e = ne e
  nApp : ∀{Δ Γ T} → Ne Δ Γ T → Sem Δ T Γ
  nApp {_} {_} {all T} e = λ tren a → nApp (App {! e  !} (reifyT a))
  nApp {_} {_} {var x} e = ne e
  nApp {_} {_} {A ⇒ B} e = λ ren a → nApp (app {! renNe ren e  !} (reify a))

  -- reify : ∀{Γ T} → Sem Γ T → Nf Γ T
  -- reify {Γ} {A ⇒ B} g = lambda (reify (g (forget1ren idRen) (nApp (var same))))
  -- reify {Γ} {base} g = g
  reify : ∀{Δ Γ T} → Sem Δ T Γ → Nf Δ Γ T
  reify {_} {_} {all T} e = Lambda (reify (e weaken1renT {! T weaken1renT (var same)  !} ))
  reify {_} {_} {var x} e = e
  reify {_} {_} {A ⇒ B} e = lambda (reify (e {! forget1ren idRen  !} (nApp (var same))))

-- eval3 : ∀{Δ₁ Δ₂} → {Γ : Ctx Δ₁} → {T : SemT Δ₁}
--   → Exp Δ₁ Γ T → (tsub : TSub Δ₁ Δ₂)
--   → Sem Δ₂ (subSemT tsub T) (subCtx tsub Γ)
-- eval3 (var x) tsub = {! subVar tsub x  !}
-- eval3 (app e e₁) tsub = {!   !}
-- eval3 (lambda e) tsub = {!   !}
-- eval3 (App e A) tsub = {!   !}
-- eval3 (Lambda e) tsub = λ tren a → {!   !}

-- eval : ∀{Δ} → {Γ₁ Γ₂ : Ctx Δ} → {T : SemT Δ}
--   → Exp Δ Γ₁ T → Sub Γ₁ Γ₂ → Sem Δ T Γ₂
-- eval (var x) sub = sub x
-- eval (app e₁ e₂) sub = (eval e₁ sub) idRen (eval e₂ sub)
-- eval (lambda e) sub = λ ren a → eval e (append1sub (transSR sub ren) a)
-- eval (App {Δ} {Γ₁} {T} e A) sub
--   = let a = ((eval e sub) idRenT (evalT A idSubT))
--     in subst (λ Γ₂ → Sem Δ (T idRenT (evalT A idSubT)) Γ₂) renidCtx≡ a
-- eval (Lambda e) sub = λ tren a → {! eval e ?  !}

eval2 : ∀{Δ₁ Δ₂} → {Γ₁ : Ctx Δ₁} → {Γ₂ : Ctx Δ₂} → {T : SemT Δ₁}
  → (tsub : TSub Δ₁ Δ₂) → Sub (subCtx tsub Γ₁) Γ₂
  → Exp Δ₁ Γ₁ T → Sem Δ₂ (subSemT tsub T) Γ₂
eval2 tsub sub (var x) = sub (subVar tsub x)
eval2 tsub sub (app e₁ e₂) = (eval2 tsub sub e₁) idRen (eval2 tsub sub e₂)
eval2 tsub sub (lambda e) = λ ren a → eval2 tsub ((append1sub (transSR sub ren) a)) e
eval2 tsub sub (App {Δ} {Γ₁} {T} e A)
  = let a = (eval2 tsub sub e) idRenT (evalT A tsub)
    in {! a  !}
eval2 tsub sub (Lambda e)
  = λ tren a → eval2 (append1Tsub (transTSR tsub tren) a) {! sub  !} e

-- TODO: am i running into the same old problems of sub and ren commuting and stuff?
-- what is / should have been / isn't different from the syntactic type approach?

{-

QUESTION: so why wouldn't syntactic types work here again? Am I kidding myself,
or was there a reason?

-}

{-

NOTE: what have I done / am doing here compared to this paper:
https://iohk.io/en/research/library/papers/system-f-in-agdafor-fun-and-profit/

They manage to define what they call "algorithmic syntax", which essentially means that
β reduction sequences don't have to be manually specified but instead are computed
algorithmically, like a programming language should. They do it via first defining
non algorithmic syntax, and then doing normalization by evaluation on the types.
They do not have to idea that I have of parametrizing Exp by SemT.

They also don't get normalziation for terms. Hopefully I will. Still, I think its
important to keep in mind that their approach exists and works.

My current understanding of how that paper works is that they do NbE for types,
and Exp is still parametrized by syntactic types. However, that is still enough
to get a DEFINITION of system F. But, they are unable to then get NbE for TERMS.
I believe that this is because to get NbE for terms one needs to do what I'm doing
in this file, and have terms parametrized by SEMANTIC types.



STILL: QUESTION: what is their semantic domain for types!!!???!?!? does it contain
part of the trick I've discovered here? I don't think they have an equivalent of
SemT. Is it unecessary?

Also, that paper deals with a langauge which is actually inconsistent. So normalization
wouldn't even make sense. But then, is it known how to do it for e.g. System F?

-}
