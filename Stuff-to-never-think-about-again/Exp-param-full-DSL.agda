{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --without-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Bool

{-

A shallow embedding which instead of giving agda type and values, gives
FREE THEOREMS and PROOFS OF FREE THEOREMS.

There exists a known way to use shallow embeddings to build parametricity free
theorems and proofs. See for example:

https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.LightweightFreeTheorems
https://bitbucket.org/akaposi/shallow/src/master/Agda/Param.agda

However, a limitation of this approach is that every term for which you want
parametricity must be written twice: once normally (either directly in agda or
in a shallow embedding) and once in the parametricity embedding.

In this file, I use my Exp type to build a DSL which simultaneously constructs
a type and free theored for that type, and also simultaneously constructs a
term and proof of free theorem for that term. This removes all code duplication.

The previous is working, but I hope to push this idea further and get
parametricity as a constructor in the DSL. This constructor would make the DSL
feel like using a langauge which has parametricity built in.

-}


-- Standard shallow embedding:

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
k = lsuc j

Ctx : Set j
Ctx = Set i
Type : Ctx → Set j
Type Γ = Γ → Set i
Term : (Γ : Ctx) → Type Γ → Set j
Term Γ T = (γ : Γ) → T γ

-- Context constructors
nil : Ctx
nil = ⊤

cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ {i} {i} Γ T

-- Type constructors
U₀ : ∀{Γ} → Type Γ
U₀ = λ γ → Set₀

U₁ : ∀{Γ} → Type Γ
U₁ = λ γ → Set₁

Π : ∀{Γ} → (A : Type Γ) → (B : Type (cons Γ A)) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

weakenT : {Γ : Ctx} → {A : Type Γ} → Type Γ → Type (cons Γ A)
weakenT T = λ γ → T (proj₁ γ)

sub : {Γ : Ctx} → {A : Type Γ} → Type (cons Γ A)
  → Term Γ A → Type Γ
sub T e = λ γ → T (γ , e γ)

-- Term constructors

lambda : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app  : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term Γ (Π A B) → (x : Term Γ A) → Term Γ (sub B x)
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

weaken : {Γ : Ctx} → {A T : Type Γ}
  → Term Γ T → Term (cons Γ A) (weakenT T)
weaken e = λ γ → e (proj₁ γ)

var : {Γ : Ctx} → {T : Type Γ}
  → Term (cons Γ T) (weakenT T)
var = proj₂

-- typeToTerm₀ : ∀{Γ} → Type₀ Γ → Term₁ Γ U₀
-- typeToTerm₀ T = T
--------------------------------------------------------------------------------

-- PARAMETRICITY EMBEDDING:
-- (Modified from papers linked at top of file)

PCtx : Ctx → Ctx → Set j
PCtx Γ₁ Γ₂ = Γ₁ → Γ₂ → Set i

PType : {Γ₁ Γ₂ : Ctx} → PCtx Γ₁ Γ₂ → (T₁ : Type Γ₁) → (T₂ : Type Γ₂) → Set j
PType {Γ₁} {Γ₂} Γ T₁ T₂ = {γ₁ : Γ₁} → {γ₂ : Γ₂} → Γ γ₁ γ₂ → T₁ γ₁ → T₂ γ₂ → Set i

PTerm : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → PType Γ T₁ T₂
  → Term Γ₁ T₁ → Term Γ₂ T₂ → Set j
PTerm {Γ₁} {Γ₂} Γ T e₁ e₂ = {γ₁ : Γ₁} → {γ₂ : Γ₂} → (γ : Γ γ₁ γ₂)
  → T {γ₁} {γ₂} γ (e₁ γ₁) (e₂ γ₂)

-- -- Context constructors
Pnil : PCtx nil nil
Pnil tt tt = ⊤

Pcons : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → PType Γ T₁ T₂
  → PCtx (cons Γ₁ T₁) (cons Γ₂ T₂)
Pcons Γ T (γ₁ , t₁) (γ₂ , t₂) = Σ {i} {i} (Γ γ₁ γ₂) (λ γ → T γ t₁ t₂)

-- Type constructors

-- Note that it would be desirable to have the Γ argument implicit, but it doesn't work.
PU₀ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → PType Γ U₀ U₀
PU₀ Γ γ A B = A → B → Set₁

PU₁ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → PType Γ U₁ U₁
PU₁ Γ γ A B = A → B → Set₂

-- Note that it would be desirable to have the Γ argument implicit, but it doesn't work.
PΠ : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ B₁ B₂}
  → (A : PType Γ A₁ A₂) → (B : PType (Pcons Γ A) B₁ B₂) → PType Γ (Π A₁ B₁) (Π A₂ B₂)
PΠ {Γ₁} {Γ₂} Γ {A₁} {A₂} A B {γ₁} {γ₂} γ f₁ f₂
  = {a₁ : A₁ γ₁} → {a₂ : A₂ γ₂} → (aR : A γ a₁ a₂) → B (γ , aR) (f₁ a₁) (f₂ a₂)

-- note that it would be desirable to have Γ and A be implicit, but Agda can't infer things without them later on.
PweakenT : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂} → (A : PType Γ A₁ A₂)
  → PType Γ T₁ T₂ → PType (Pcons Γ A) (weakenT T₁) (weakenT T₂)
PweakenT Γ A T = λ γ → T (proj₁ γ)

-- note that it would be desirable to have Γ and A be implicit, but Agda can't infer things without them later on.
Psub : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂ e₁ e₂} → (A : PType Γ A₁ A₂)
  → PType (Pcons Γ A) T₁ T₂ → PTerm Γ A e₁ e₂ → PType Γ (sub T₁ e₁) (sub T₂ e₂)
Psub Γ A T e = λ γ → T (γ , e γ)
-- Term constructors

Plambda : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂} → (A : PType Γ A₁ A₂)
  → ∀{B₁ B₂} → (B : PType (Pcons Γ A) B₁ B₂)
  → ∀{e₁ e₂} → PTerm (Pcons Γ A) B e₁ e₂ → PTerm Γ (PΠ Γ A B) (lambda e₁) (lambda e₂)
Plambda Γ A B e = λ γ a → e (γ , a)

Papp : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂} → {A : PType Γ A₁ A₂}
  → ∀{B₁ B₂} → (B : PType (Pcons Γ A) B₁ B₂)
  → ∀{e₁ e₂ e₁' e₂'} → PTerm Γ (PΠ Γ A B) e₁ e₂ → (x : PTerm Γ A e₁' e₂')
  → PTerm Γ (Psub Γ A B x) (app e₁ e₁') (app e₂ e₂')
Papp Γ B e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

Pweaken : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{A₁ A₂ T₁ T₂} → (A : PType Γ A₁ A₂)
  → (T : PType Γ T₁ T₂) → ∀{e₁ e₂}
  → PTerm Γ T e₁ e₂ → PTerm (Pcons Γ A) (PweakenT Γ A T) (weaken e₁) (weaken e₂)
Pweaken Γ A T e = λ γ → e (proj₁ γ)

Pvar : ∀{Γ₁ Γ₂} → (Γ : PCtx Γ₁ Γ₂) → ∀{T₁ T₂} → (T : PType Γ T₁ T₂)
  → PTerm (Pcons Γ T) (PweakenT Γ T T) var var
Pvar Γ T = proj₂

--------------------------------------------------------------------------------

-- My combined embedding using the Exp type:

PTypeToType∅ : {T : Type nil}
  → PType Pnil T T → Type nil
PTypeToType∅ {T} PT = λ tt → (x y : T tt) → PT tt x y

-- PCtxToCtx : {Γ : Ctx} → PCtx Γ Γ → Ctx
-- PCtxToCtx

PTypeToType : {Γ : Ctx} → {PΓ : PCtx Γ Γ} → {T : Type Γ}
  → PType PΓ T T → Type Γ
PTypeToType PT = λ γ → {! (Pγ : )  !}



-- Represents the data carried by an element of Exp
data Model : Set j where
  -- Have a term and Parametricity term
  termPterm :
    ∀{aΓ PΓ} → (T : Type aΓ)
    → (PT : PType PΓ T T) → (a : Term aΓ T) → (PTerm PΓ PT a a)
    → Model
  -- just have a term
  term : ∀{aΓ} → (T : Type aΓ) → (a : Term aΓ T) → Model
  -- have a term, and expect input to have parametricity term
  -- for return result of parametricity constructor
  param : ∀{aΓ} → (T : Type aΓ) → (a : Term aΓ T) → Model
  error : Model

-- need to figure out how to deal with Context, either switch to version where no Context, or
-- make CtxModel : Set j, and then Model : CtxModel → Set j

{-

The end result that I want is
parametricity (Π₀ U .....) t

where t is just a term of the given type, and then result of expression is
Exp Γ (term (FREE THEOREM)) ...

m₁, m₂ : Model
app : Exp m₁ → Exp m₂ → Exp appCompute m₁ m₂

appCompute can't really be written the way I want though...

Instead, one Exp for each Model?
So, parametricity is in param model Exp, and the app constrcuctor in the param model Exp
takes a type from termPterm model Exp, and argument from termPterm model Exp

-}


data Context : (aΓ : Ctx) → PCtx aΓ aΓ → Set j where
  ∅ : Context nil Pnil
  -- _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ {i} {i} aΓ T)
  Econs : ∀{aΓ PΓ} → (ctx : Context aΓ PΓ) → (T : Type aΓ)
    → (PT : PType PΓ T T)
    → Context (cons aΓ T) (Pcons PΓ PT)

data InCtx : ∀{aΓ PΓ} → (Γ : Context aΓ PΓ) → (T : Type aΓ)
  → (PT : PType PΓ T T) → (a : Term aΓ T) → (PTerm PΓ PT a a)
  → Set j where
  same : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {T : Type aΓ} → {PT : PType PΓ T T}
    → InCtx (Econs Γ T PT) (weakenT T) (PweakenT PΓ PT PT) var (Pvar PΓ PT)
  next : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {A T : Type aΓ}
    → {PA : PType PΓ A A} → {PT : PType PΓ T T}
    → {a : Term aΓ T} → {Pa : PTerm PΓ PT a a}
    → InCtx Γ T PT a Pa
    → InCtx (Econs Γ A PA) (weakenT T) (PweakenT PΓ PA PT)
        (weaken a) (Pweaken PΓ PA PT Pa)

data Exp : ∀{aΓ PΓ} → (Γ : Context aΓ PΓ)
  → (T : Type aΓ) → (PT : PType PΓ T T)
  → (a : Term aΓ T) → PTerm PΓ PT a a  → Set j where
  ELambda : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {A : Type aΓ} → {B : Type (cons aΓ A)}
    → {PA : PType PΓ A A} → {PB : PType (Pcons PΓ PA) B B}
    → {a : Term (cons aΓ A) B} → {Pa : PTerm (Pcons PΓ PA) PB a a}
    → Exp (Econs Γ A PA) B PB a Pa
    → Exp Γ (Π A B) (PΠ PΓ PA PB) (lambda a) (Plambda PΓ PA PB Pa)
  EVar : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ} → {T : Type aΓ} → {a : Term aΓ T}
    → {PT : PType PΓ T T} → {Pa : PTerm PΓ PT a a}
    → InCtx Γ T PT a Pa → Exp Γ T PT a Pa
  EApp : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → {A : Type aΓ} → {B : Type (cons aΓ A)}
    → {PA : PType PΓ A A} → {PB : PType (Pcons PΓ PA) B B}
    → {x : Term aΓ (Π A B)} → {Px : PTerm PΓ (PΠ PΓ PA PB) x x}
    → {y : Term aΓ A} → {Py : PTerm PΓ PA y y}
    → Exp Γ (Π A B) (PΠ PΓ PA PB) x Px
    → Exp Γ A PA y Py
    → Exp Γ (sub B y) (Psub PΓ PA PB Py) (app x y) (Papp PΓ PB Px Py)
    -- TODO: make terms for U₀ instead of having λ γ → Set₀, same for P thing
    -- same for Π
  EΠ₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → {a : Term aΓ U₀} → {Pa : PTerm PΓ (PU₀ PΓ) a a}
    → (A : Exp Γ U₀ (PU₀ PΓ) a Pa)
    → {b : Term (cons aΓ a) U₀} → {Pb : PTerm (Pcons PΓ Pa) (PU₀ (Pcons PΓ Pa)) b b}
    → (B : Exp (Econs Γ a Pa) U₀ (PU₀ (Pcons PΓ Pa)) b Pb)
    → Exp Γ U₀ (PU₀ PΓ) (λ γ → (x : a γ) → b (γ , x))
      (λ {γ₁} {γ₂} γ f₁ f₂
        → {a₁ : a γ₁} → {a₂ : a γ₂} → (aR : Pa γ a₁ a₂) → Pb (γ , aR) (f₁ a₁) (f₂ a₂))
  EΠ₁ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → {a : Term aΓ U₁} → {Pa : PTerm PΓ (PU₁ PΓ) a a}
    → (A : Exp Γ U₁ (PU₁ PΓ) a Pa)
    → {b : Term (cons aΓ a) U₁} → {Pb : PTerm (Pcons PΓ Pa) (PU₁ (Pcons PΓ Pa)) b b}
    → (B : Exp (Econs Γ a Pa) U₁ (PU₁ (Pcons PΓ Pa)) b Pb)
    → Exp Γ U₁ (PU₁ PΓ) (λ γ → (x : a γ) → b (γ , x))
      (λ {γ₁} {γ₂} γ f₁ f₂
        → {a₁ : a γ₁} → {a₂ : a γ₂} → (aR : Pa γ a₁ a₂) → Pb (γ , aR) (f₁ a₁) (f₂ a₂))
  EU₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → Exp {aΓ} Γ U₁ (PU₁ PΓ) (λ γ → Set₀) (λ γ A B → A → B → Set₁) -- U₀ PU₀
  cumu₀ : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    → {a : Term aΓ U₀} → {Pa : PTerm PΓ (PU₀ PΓ) a a}
    → Exp Γ U₀ (PU₀ PΓ) a Pa
    → Exp Γ U₁ (PU₁ PΓ) a Pa
  -- parametricity : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
    -- → {T : Type aΓ} → {PT : PType PΓ T T} → {a : Term aΓ T} → {Pa : PTerm PΓ PT a a}
    -- → Exp Γ T PT a Pa → Exp Γ {! PT  !} {!   !} {!   !} {!   !}
  parametricity∅₀ : {t : Term nil U₀} → {Pt : PTerm Pnil (PU₀ Pnil) t t}
    → Exp ∅ U₀ (PU₀ Pnil) t Pt
    → Exp ∅ (PTypeToType∅ Pt) {!   !} {! Pt  !} {!   !}

-- Exp' : ∀{aΓ PΓ} → (Γ : Context aΓ PΓ)
--   → {t : Term aΓ U₁} → {Pt : PTerm PΓ (PU₁ PΓ) t t}
--   → Exp Γ U₁ (PU₁ PΓ) t Pt
--   → Set j
-- Exp' Γ {t} {Pt} e = Exp Γ t Pt _ _

extract : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
  → {T : Type aΓ} → {PT : PType PΓ T T}
  → {t : Term aΓ T} → {Pt : PTerm PΓ PT t t}
  → Exp Γ T PT t Pt
  → Term aΓ T
extract {_} {_} {_} {_} {_} {t} e = t

Pextract : ∀{aΓ PΓ} → {Γ : Context aΓ PΓ}
  → {T : Type aΓ} → {PT : PType PΓ T T}
  → {t : Term aΓ T} → {Pt : PTerm PΓ PT t t}
  → Exp Γ T PT t Pt
  → PTerm PΓ PT t t
Pextract {_} {_} {_} {_} {_} {_} {Pt} e = Pt

exT : Exp ∅ U₁ (PU₁ Pnil) _ _ -- (λ γ → (X : Set) → X → X) _
-- exT = EΠ₁ EU₀ (EΠ₁ {! cumu₀ (EVar same)  !} {!   !} )
exT = EΠ₁ EU₀ (EΠ₁ (cumu₀ (EVar same)) (cumu₀ (EVar (next same))))

exTerm : Exp ∅ (extract exT) (Pextract exT) _ _
exTerm = ELambda (ELambda (EVar same))

Γ : Context (cons nil U₀) (Pcons Pnil (PU₀ Pnil))
Γ = Econs ∅ U₀ (PU₀ Pnil)

exT2 : Exp Γ U₁ (PU₁ (Pcons Pnil (PU₀ Pnil))) _ _
exT2 = cumu₀ (EΠ₀ (EVar same) (EVar (next same)))

exTerm2 : Exp Γ (extract exT2) (Pextract exT2) _ _
exTerm2 = ELambda (EVar same)

a = {! Pextract exTerm2  !}
