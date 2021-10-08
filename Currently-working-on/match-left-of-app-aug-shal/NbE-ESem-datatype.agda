{-# OPTIONS --without-K #-}

open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function

{-

Just checking if actually NbE has been possible with augmented shallow embeddings
this whole time...

-}

--------------------- Type codes (could use just shallow embedding) ------------

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

module sucn (SemTn : Set) (Semn : SemTn → Set) where
  mutual
    data SemTsucn : Set where
        U : SemTsucn
        Π : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        cumu : SemTn → SemTsucn

    Semsucn : SemTsucn → Set
    Semsucn U = SemTn
    Semsucn (Π A B) = (a : Semsucn A) → Semsucn (B a)
    Semsucn (cumu T) = Semn T

open sucn

mutual
  SemT : ℕ → Set
  SemT zero = SemTzero
  SemT (suc n) = sucn.SemTsucn (SemT n) (Sem n)

  Sem : (n : ℕ) → SemT n → Set
  Sem zero T = Semzero T
  Sem (suc n) T = sucn.Semsucn _ _ T

type⊥ : ∀{n} → SemT (2 + n)
type⊥ = Π U λ X → cumu X

------------------------  "Shallow" embedding   --------------------------------

Ctx = Set
Type : ℕ → Ctx → Set
Type n Γ = Γ → SemT n
Term : ∀{n} → (Γ : Ctx) → Type n Γ → Set
Term Γ T = (γ : Γ) → Sem _ (T γ)
nil : Ctx
nil = ⊤
cons : ∀{n} → (Γ : Ctx) → Type n Γ → Ctx
cons Γ T = Σ Γ (λ γ → Sem _ (T γ))

SU : ∀{n Γ} → Type (suc n) Γ
SU = λ _ → U

SΠ : ∀{n Γ} → (A : Type (suc n) Γ) → Type (suc n) (cons Γ A) → Type (suc n) Γ
SΠ A B = λ γ → Π (A γ) ((λ a → B (γ , a)))

Slambda : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (SΠ A B)
Slambda e = λ γ → λ a → e (γ , a)

Sapp : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term Γ (SΠ A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
Sapp e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

Svar : ∀{n Γ} → {A : Type (suc n) Γ} → Term (cons Γ A) (λ γ → (A (proj₁ γ)))
Svar = proj₂

Sweaken : ∀{n Γ} → {T A : Type n Γ} → Term Γ T → Term (cons Γ A) (λ γ → (T (proj₁ γ)))
Sweaken e = λ γ → e (proj₁ γ)

ScumuT : ∀{n Γ} → (T : Type n Γ) → Type (suc n) Γ
ScumuT T = λ γ → cumu (T γ)

Scumu : ∀{n Γ} → {T : Type n Γ} → Term Γ T → Term Γ (ScumuT T)
Scumu e = e

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

append1ren : ∀{n Γ₁ Γ₂} → {T : Type n Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
append1ren sub (γ₂ , t) = sub γ₂

append1sub : ∀{n Γ₁ Γ₂} → {T : Type n Γ₁} → Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
append1sub sub e γ₂ = sub γ₂ , e (sub γ₂)

idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

weaken1Ren : ∀{Γ n T} → Sub Γ (cons {n} Γ T)
weaken1Ren = proj₁

subType : ∀{Γ₁ Γ₂ n} → Sub Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
subType sub T = λ γ₂ → T (sub γ₂)

forget1ren : ∀{Γ₁ Γ₂ n} → (sub : Sub Γ₁ Γ₂) → (T : Type n Γ₁)
  → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
forget1ren sub T (γ , t) = sub γ , t

subExp : ∀{Γ₁ Γ₂ n T} → (sub : Sub Γ₁ Γ₂) → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
subExp sub e = λ γ₂ → e (sub γ₂)

append1sub' : ∀{n Γ₁ Γ₂} → (T : Type n Γ₁) → (sub : Sub Γ₁ Γ₂)
  → Term Γ₂ (subType sub T) → Sub (cons Γ₁ T) Γ₂
append1sub' T sub e γ₂ = sub γ₂ , e γ₂

-------------------- Augmented "shallow" embedding -----------------------------

data Context : Ctx → Set₁ where
  ∅ : Context nil
  _,_ : ∀{n SΓ} → (ctx : Context SΓ) → (T : Type n SΓ) → Context (cons SΓ T)

data Var : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Type n SΓ} → {Γ : Context SΓ}
    → Var {n} (Γ , T) (λ γ → T (proj₁ γ)) proj₂
  next : ∀{n m SΓ Γ A a} → {T : Type n SΓ} → Var {m} {SΓ} Γ A a
    → Var (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

data Exp : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
    → {B : Type (suc n) (cons SΓ A)} → ∀{a}
    → Exp (Γ , A) B a → Exp Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
  Evar : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → {a : Term SΓ T}
    → (icx : Var Γ T a) → Exp {n} {SΓ} Γ T a
  Eapp : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
      → {B : Type (suc n) (cons SΓ A)} → ∀{a₁ a₂}
      → Exp {suc n} Γ (SΠ A B) a₁ → (x : Exp {suc n} Γ A a₂)
      → Exp {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sapp {n} {SΓ} {A} {B} a₁ a₂)
  EΠ : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {a₁ : Term SΓ (SU {suc n})}
    → {a₂ : Type (suc n) (cons SΓ a₁)} → (A : Exp Γ (SU {suc n}) a₁)
    → (B : Exp (Γ , a₁) (SU {suc n}) a₂)
    → Exp Γ (SU {suc n}) (SΠ {n} a₁ a₂)
  EU : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → Exp {suc (suc n)} {SΓ} Γ SU SU
  -- TODO: shouldn't have to be 2+n there. Something funky with way I've defined things above!
  -- Eweaken : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ}
    -- → {A : Type n SΓ} → ∀{a}
    -- → Exp Γ T a → Exp (Γ , A) (λ γ → (T (proj₁ γ))) (Sweaken {_} {_} {T} {A} a)
  EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
    → Exp Γ T a → Exp Γ (ScumuT T) (Scumu {n} {_} {T} a)
  Ecumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
    → Exp Γ (SU {n}) a → Exp Γ (SU {suc n}) (ScumuT a)

  -- Renamings and Substitutions on Exp

ERen : ∀{sΓ₁ sΓ₂} → Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
ERen sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Var Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)

EidRen : ∀{sΓ Γ} → ERen {sΓ} idSub Γ Γ
EidRen x = x

Eforget1ren : ∀{n sΓ₁ sΓ₂ T} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → ERen sub Γ₁ Γ₂ → ERen (forget1ren {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , subType sub T)
Eforget1ren ren same = same
Eforget1ren ren (next x) = next (ren x)

Eweaken1Ren : ∀{sΓ Γ n T} → ERen {sΓ} (weaken1Ren {sΓ} {n} {T}) Γ (Γ , T)
Eweaken1Ren = next

renExp : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → ERen sub Γ₁ Γ₂ → Exp {n} Γ₁ T t → Exp Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)
renExp ren (Elambda e) = Elambda (renExp (Eforget1ren ren) e)
renExp ren (Evar x) = Evar (ren x)
renExp ren (Eapp e₁ e₂) = Eapp (renExp ren e₁) (renExp ren e₂)
renExp ren (EΠ A B) = EΠ (renExp ren A) (renExp (Eforget1ren ren) B)
renExp ren EU = EU
renExp ren (Ecumu e) = Ecumu (renExp ren e)
renExp ren (EcumuValue e) = EcumuValue (renExp ren e)

ESub : ∀{sΓ₁ sΓ₂} → Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
ESub sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Exp Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)

EidSub : ∀{sΓ Γ} → ESub {sΓ} idSub Γ Γ
EidSub x = Evar x

Eforget1sub : ∀{n sΓ₁ sΓ₂ T} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → ESub sub Γ₁ Γ₂ → ESub (forget1ren {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , subType sub T)
Eforget1sub sub same = Evar same
Eforget1sub sub (next x) = renExp Eweaken1Ren (sub x)

-- Eappend1sub : ∀{sΓ₁ sΓ₂ n Γ₁ Γ₂ sub} → {T : Type n sΓ₁} → {t : Term sΓ₁ T}
--   → ESub {sΓ₁} {sΓ₂} sub Γ₁ Γ₂
--   → Exp Γ₁ T t → ESub (append1sub {_} {_} {_} {T} sub t) (Γ₁ , T) Γ₂
-- Eappend1sub sub e same = EsubExp sub e
-- Eappend1sub sub e (next x) = sub x

------------------- Normal form augmented "shallow" embedding ------------------

mutual
  data Ne : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
    → Term SΓ T → Set₁ where
    Evar : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → {a : Term SΓ T}
      → (icx : Var Γ T a) → Ne {n} {SΓ} Γ T a
    Eapp : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
        → {B : Type (suc n) (cons SΓ A)} → ∀{a₁ a₂}
        → Ne {suc n} Γ (SΠ A B) a₁ → (x : Nf {suc n} Γ A a₂)
        → Ne {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sapp {n} {SΓ} {A} {B} a₁ a₂)
    EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
      → Ne Γ T a → Ne Γ (ScumuT T) (Scumu {n} {_} {T} a)

  data Nf : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
    → Term SΓ T → Set₁ where
    Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
      → {B : Type (suc n) (cons SΓ A)} → ∀{a}
      → Nf (Γ , A) B a → Nf Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
    -- EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
    --   → Exp Γ T a → Exp Γ (ScumuT T) (Scumu {n} {_} {T} a)
    -- NOTE: does EcumuValue go in Nf, Ne, or both?
    fromNe : ∀{n SΓ Γ T t} → Ne {n} {SΓ} Γ T t → Nf Γ T t
    -- only when of type (Ne e)... need to have Shallow embedding
    -- split into Ne, Nf, Type. Instead of just Type, Term.
    fromType : ∀{n SΓ Γ T} → EType {n} {SΓ} Γ T → Nf {suc n} Γ SU T


  data EType : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
    → Set₁ where
    EΠ : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {a₁ : Term SΓ (SU {suc n})}
      → {a₂ : Type (suc n) (cons SΓ a₁)} → (A : EType Γ a₁)
      → (B : EType (Γ , a₁) a₂)
      → EType Γ (SΠ {n} a₁ a₂)
    EU : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → EType {suc (suc n)} {SΓ} Γ SU
    Ecumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
      → EType {n} Γ a → EType Γ (ScumuT a)
    fromNe : ∀{n SΓ Γ T} → Ne {suc n} {SΓ} Γ SU T → EType Γ T

------------------ Semantic domain, parametrized by shallow --------------------
data ESemTzero : {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type 0 SΓ) → Set₁ where
data ESemzero : ∀{SΓ} → (Γ : Context SΓ) → (T : Type 0 SΓ) → Term SΓ T → Set₁ where

module Esucn (n : ℕ)
  (ESemTn : {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ) → Set₁)
  (ESemn : ∀{SΓ} → (Γ : Context SΓ) → (T : Type n SΓ) → Term SΓ T → Set₁)
  where
  mutual
    data ESemTsucn : {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type (suc n) SΓ)
      → Set₁ where
      EU : {SΓ : Ctx} → {Γ : Context SΓ} → ESemTsucn {SΓ} Γ SU
      fromNe : ∀{SΓ Γ T} → Ne {suc (suc n)} {SΓ} Γ SU T → ESemTsucn Γ T -- why 2 sucs?
      Ecumu : {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
        → ESemTn Γ a → ESemTsucn Γ (ScumuT a)
      EΠ : {SΓ : Ctx} → {Γ : Context SΓ}
        → {a₁ : Term SΓ (SU {suc n})}
        → {a₂ : Type (suc n) (cons SΓ a₁)}
        → (A : ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → ERen ren Γ Γ' → ESemTsucn Γ' (subType ren a₁))
        → (B : ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → (eren : ERen ren Γ Γ') → ∀{a}
            → ESemsucn Γ' (subType ren a₁) a -- (A eren)
            → ESemTsucn Γ' (subType (append1sub' a₁ ren a) a₂))
        → ESemTsucn Γ (SΠ {n} a₁ a₂)

    -- ESemsucn : ∀{SΓ} → (Γ : Context SΓ) → (T : Type (suc n) SΓ)
    --   → Term SΓ T → ESemTsucn Γ T → Set₁
    -- ESemsucn Γ ST St EU = ESemTn Γ St
    -- ESemsucn Γ ST St (fromNe e) = Nf Γ ST St -- NOTE: if Ne is parametrized specifically by Ne in SHALLOW embedding, then that will help here later...
    -- ESemsucn Γ ST St (Ecumu T) = ESemn Γ _ St T
    -- ESemsucn {SΓ} Γ ST St (EΠ {_} {_} {SA} {SB} A B)
    --   = ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → (eren : ERen ren Γ Γ') → ∀{Sa}
    --     → (a : ESemsucn Γ' _ Sa (A eren))
    --       → ESemsucn Γ' _ (λ γ → St (ren γ) (Sa γ)) (B eren a)

    -- Why does ESem have to be parametrized be ESemT?
    -- Instead of matching in SemT and then that determines the type of the Sem, just match on the Sem itself and get the value from it.
    data ESemsucn : ∀{SΓ} → (Γ : Context SΓ) → (T : Type (suc n) SΓ)
      → Term SΓ T → Set₁ where
      -- each constructor is a case based on ESemT
      EU : ∀{SΓ St} → {Γ : Context SΓ} → ESemTn Γ St → ESemsucn Γ SU St
      fromNe : ∀{SΓ Γ ST St} → Nf {_} {SΓ} Γ ST St → ESemsucn Γ ST St  -- TODO: do I need Ne arg from ESemT? ST should be Ne.
      Ecumu : ∀{SΓ Γ ST St} → ESemn {SΓ} Γ ST St
        → ESemsucn Γ (ScumuT ST) (Scumu {_} {_} {ST} St)
      EΠ : ∀{SΓ} → {Γ : Context SΓ}
        → {a₁ : Term SΓ (SU {suc n})}
        → {a₂ : Type (suc n) (cons SΓ a₁)}
        → {St : Term SΓ (SΠ a₁ a₂)}
        → (∀{SΓ' Γ'} → (ren : Sub SΓ SΓ') → (Sa : Term SΓ' (subType ren a₁))
            -- → ESemsucn Γ' (subType ren a₁) Sa -- TODO: Do I even need this?????
            → ESemsucn Γ' (subType (append1sub' a₁ ren Sa) a₂) (λ γ → St (ren γ) (Sa γ)))
        → ESemsucn Γ (SΠ a₁ a₂) St
open Esucn

mutual
  ESemT : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ) → Set₁
  ESemT {zero} = ESemTzero
  ESemT {suc n} = ESemTsucn n (ESemT {n}) (ESem {n})

  ESem : ∀{n SΓ} → (Γ : Context SΓ) → (T : Type n SΓ) → Term SΓ T → Set₁
  ESem {zero} = ESemzero
  ESem {suc n} = ESemsucn n (ESemT {n}) (ESem {n})

eval : ∀{n SΓ₁ SΓ₂ Γ₁ Γ₂ ST St}
  → Exp {n} {SΓ₁} Γ₁ ST St
  → (sub : Sub SΓ₁ SΓ₂)
  → ESem Γ₂ (subType sub ST) (subExp {_} {_} {_} {ST} sub St)
eval (Elambda {_} {_} {_} {A} e) sub = EΠ (λ ren Sa {-a-} → eval e (append1sub' A (sub ∘ ren) Sa))
eval (Evar icx) sub  = {! sub icx  !}
eval (Eapp e₁ e₂) sub  = {! (eval e₁ sub)  !} -- I Think this case shows why this makes no sense!
eval (EΠ e e₁) sub  = {!   !}
eval EU sub  = {! ESemTsucn.EU  !}
eval (EcumuValue e) sub  = {!   !}
eval (Ecumu e) sub  = {!   !}

{-

mutual
  reifyT : ∀{n SΓ Γ ST} → (T : ESemT {n} {SΓ} Γ ST) → EType Γ ST
  reifyT T = {!   !}

  nApp : ∀{n SΓ Γ ST St} → (T : ESemT Γ ST) → Ne {suc n} {SΓ} Γ ST St → ESem Γ ST St T
  nApp EU e = {! fromNe  !}
  nApp (fromNe x) e = fromNe e -- something something with η-expanded form, the other cases shouldn't be able to be defined like this...
  nApp (Ecumu T) e = {! nApp T e  !}
  nApp (EΠ A B) e
    = {!   !}
    -- = λ eren t → nApp {!   !} (Eapp {! e  !} {! reify t  !})
    --  = λ eren a → nApp {! B Eweaken1Ren (nApp (A Eweaken1Ren) ? )  !} {!   !}
  -- FROM STLC:
  -- nApp {_} {A ⇒ B} e = λ ren g → nApp (app (renNe ren e) (reify g))

  reify : ∀{n SΓ Γ ST St} → (T : ESemT {suc n} {SΓ} Γ ST) → ESem Γ ST St T
    → Nf Γ ST St
  reify EU t = fromType (reifyT t)
  reify (fromNe x) t = t
  reify (Ecumu T) t = {! EcumuValue (reify T t)  !}
  reify (EΠ A B) t
    = Elambda (reify (B Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same)))
                      (t Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same))))

evalT : ∀{n SΓ₁ SΓ₂ Γ₁ Γ₂ ST}
  → (sub : Sub SΓ₁ SΓ₂)
  → EType {suc n} {SΓ₁} Γ₁ ST
  → ESemT Γ₂ (subType sub ST)
evalT sub (EΠ {_} {_} {_} {a₁} A B) = EΠ (λ {_} {_} {ren} eren → evalT (sub ∘ ren) A)
  (λ {_} {_} {ren} eren {Sa} a → evalT (append1sub' a₁ (sub ∘ ren) Sa) B)
evalT sub EU = EU
evalT sub (Ecumu T) = {!   !} -- Ecumu (evalT sub T)
evalT sub (fromNe e) = fromNe {!  evalNe sub SU e !}

-- NOTE: remember, one possibility is that ESem should actually be datatype and not
-- parametrized by ESemT. Not sure if that actually makes any sense or not.


{-
TODO
1) Rename these to nAppsucn and reifysucn because they work on suc n???
2) Define renaming on Nf, Ne, EType, OR otherwise switch to GSem implementation

-}
-}
