{-# OPTIONS --without-K #-}

open import Data.Unit
open import Data.Nat
-- open import Data.Maybe
-- open import Data.Empty
open import Data.Product
-- open import Data.Sum
-- open import Relation.Binary.PropositionalEquality
-- open import Agda.Primitive
-- open import Function
-- open import Level hiding (suc)

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
    unCumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
      → Ne Γ (ScumuT T) (Scumu {n} {_} {T} a) → Ne Γ T a

  data Nf : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
    → Term SΓ T → Set₁ where
    Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
      → {B : Type (suc n) (cons SΓ A)} → ∀{a}
      → Nf (Γ , A) B a → Nf Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
    EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
      → Nf Γ T a → Nf Γ (ScumuT T) (Scumu {n} {_} {T} a)
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
    EU : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → EType {suc n} {SΓ} Γ SU
    Ecumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
      → EType {n} Γ a → EType Γ (ScumuT a)
    fromNe : ∀{n SΓ Γ T} → Ne {suc n} {SΓ} Γ SU T → EType Γ T

mutual
  renNe : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → ERen sub Γ₁ Γ₂ → Ne {n} Γ₁ T t → Ne Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)
  renNe ren (Evar x) = Evar (ren x)
  renNe ren (Eapp e₁ e₂) = Eapp (renNe ren e₁) (renNf ren e₂)
  renNe ren (EcumuValue e) = EcumuValue (renNe ren e)
  renNe ren (unCumu e) = unCumu (renNe ren e)

  renNf : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → ERen sub Γ₁ Γ₂ → Nf {n} Γ₁ T t → Nf Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)
  renNf ren (Elambda e) = Elambda (renNf (Eforget1ren ren) e)
  renNf ren (EcumuValue e) = EcumuValue (renNf ren e)
  renNf ren (fromNe e) = fromNe (renNe ren e)
  renNf ren (fromType T) = fromType (renEType ren T)

  renEType : ∀{n sΓ₁ sΓ₂ T} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → ERen sub Γ₁ Γ₂ → EType {n} Γ₁ T → EType Γ₂ (subType sub T)
  renEType ren (EΠ A B) = EΠ (renEType ren A) (renEType (Eforget1ren ren) B)
  renEType ren EU = EU
  renEType ren (Ecumu e) = Ecumu (renEType ren e)
  renEType ren (fromNe e) = fromNe (renNe ren e)

------------------ Semantic domain, parametrized by shallow --------------------
data ESemTzero : {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type 0 SΓ) → Set₁ where
    fromNe : ∀{SΓ Γ T} → Ne {1} {SΓ} Γ (SU {0}) T → ESemTzero Γ T
ESemzero : ∀{SΓ} → (Γ : Context SΓ) → (T : Type 0 SΓ) → Term SΓ T → ESemTzero Γ T → Set₁
ESemzero Γ ST St (fromNe e) = Nf Γ ST St -- TODO: should be Ne?

module Esucn (n : ℕ)
  (ESemTn : {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ) → Set₁)
  (ESemn : ∀{SΓ} → (Γ : Context SΓ) → (T : Type n SΓ) → Term SΓ T → ESemTn Γ T → Set₁)
  where
  mutual
    data ESemTsucn : {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type (suc n) SΓ)
      → Set₁ where
      EU : {SΓ : Ctx} → {Γ : Context SΓ} → ESemTsucn {SΓ} Γ SU
      fromNe : ∀{SΓ Γ T} → Ne {suc (suc n)} {SΓ} Γ (SU {suc n}) T → ESemTsucn Γ T -- why 2 sucs?
      Ecumu : {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
        → ESemTn Γ a → ESemTsucn Γ (ScumuT a)
      EΠ : {SΓ : Ctx} → {Γ : Context SΓ}
        → {a₁ : Term SΓ (SU {suc n})}
        → {a₂ : Type (suc n) (cons SΓ a₁)}
        → (A : ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → ERen ren Γ Γ' → ESemTsucn Γ' (subType ren a₁))
        → (B : ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → (eren : ERen ren Γ Γ') → ∀{a}
            → ESemsucn Γ' (subType ren a₁) a (A eren)
            → ESemTsucn Γ' (subType (append1sub' a₁ ren a) a₂))
        → ESemTsucn Γ (SΠ {n} a₁ a₂)

    ESemsucn : ∀{SΓ} → (Γ : Context SΓ) → (T : Type (suc n) SΓ)
      → Term SΓ T → ESemTsucn Γ T → Set₁
    ESemsucn Γ ST St EU = ESemTn Γ St
    ESemsucn Γ ST St (fromNe e) = Nf Γ ST St -- NOTE: if Ne is parametrized specifically by Ne in SHALLOW embedding, then that will help here later...
    ESemsucn Γ ST St (Ecumu T) = ESemn Γ _ St T
    ESemsucn {SΓ} Γ ST St (EΠ {_} {_} {SA} {SB} A B)
      = ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → (eren : ERen ren Γ Γ') → ∀{Sa}
        → (a : ESemsucn Γ' _ Sa (A eren))
          -- → ESem Γ' _ (Sapp {_} {_} {subType ren SA} {subType (forget1ren ren SA) SB} (subExp ren St) Sa) (B eren a)
          → ESemsucn Γ' _ (λ γ → St (ren γ) (Sa γ)) (B eren a)

    -- Why does ESem have to be parametrized be ESemT?
    data ESemsucn' : ∀{SΓ} → (Γ : Context SΓ) → (T : Type (suc n) SΓ)
      → Term SΓ T → ESemTsucn Γ T → Set₁ where
open Esucn

mutual
  ESemT : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ) → Set₁
  ESemT {zero} = ESemTzero
  ESemT {suc n} = ESemTsucn n (ESemT {n}) (ESem {n})

  ESem : ∀{n SΓ} → (Γ : Context SΓ) → (T : Type n SΓ) → Term SΓ T → ESemT Γ T → Set₁
  ESem {zero} = ESemzero
  ESem {suc n} = ESemsucn n (ESemT {n}) (ESem {n})

mutual
  {-
  Why don't these functions pass Agda's termination checker?
  There is a lexicographic ordering in the functions on the arguments "n" and "T".
  Either n decreases, or n stays the same and T decreases.
  -}

  reifyT : ∀{n SΓ Γ ST} → (T : ESemT {n} {SΓ} Γ ST) → EType Γ ST
  reifyT {zero} (fromNe e) = fromNe e
  reifyT {suc n} EU = EU
  reifyT {suc n} (fromNe x) = fromNe x
  reifyT {suc n} (Ecumu T) = Ecumu (reifyT {n} T)
  reifyT {suc n} (EΠ A B) = EΠ (reifyT {suc n} (A EidRen))
    (reifyT {suc n} (B Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same))))

  nApp : ∀{n SΓ Γ ST St} → (T : ESemT Γ ST) → Ne {n} {SΓ} Γ ST St → ESem Γ ST St T
  nApp {zero} (fromNe T) e = fromNe e
  -- nApp {suc n} EU e = {! ESemTsucn.fromNe ?  !} -- issue is some type level stuff.... need to eliminate all suc(suc n), should only need (suc n)
  nApp {suc zero} EU e = fromNe e
  nApp {suc (suc n)} EU e = fromNe e
  nApp {suc n} (fromNe x) e = fromNe e -- something something with η-expanded form, the other cases shouldn't be able to be defined like this...
  nApp {suc n} (Ecumu T) e = nApp {n} T (unCumu e) -- something about the way that cumu is stored in Nf/Ne, should be unique normal forms!
  nApp {suc n} (EΠ A B) e
    = λ eren t → nApp (B eren t) (Eapp (renNe eren e) (reify (A eren) t))

  reify : ∀{n SΓ Γ ST St} → (T : ESemT {n} {SΓ} Γ ST) → ESem Γ ST St T
    → Nf Γ ST St
  reify {zero} (fromNe T) e = e
  reify {suc n} EU t = fromType (reifyT {n} t)
  reify {suc n} (fromNe x) t = t
  reify {suc n} (Ecumu T) t = EcumuValue (reify {n} T t)
  reify {suc n} (EΠ A B) t
    = Elambda (reify (B Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same)))
                      (t Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same))))
{-
TODO
1) Rename these to nAppsucn and reifysucn because they work on suc n???
2) Define renaming on Nf, Ne, EType, OR otherwise switch to GSem implementation

-}

-- eval : ∀{n SΓ Γ ST St} → (T : ESemT {n} {SΓ} Γ ST)
--   → Exp Γ ST St → ESem Γ ST St T
-- eval {zero} T e = {!   !}
-- eval {suc n} T (Elambda e) = {! T  !}
-- eval {suc n} T (Evar icx) = {!   !}
-- eval {suc n} T (Eapp e e₁) = {!   !}
-- eval {suc .(suc _)} T (EΠ e e₁) = {!   !}
-- eval {suc .(suc _)} T EU = {!   !}
-- eval {suc n} T (EcumuValue e) = {!   !}
-- eval {suc .(suc _)} T (Ecumu e) = {!   !}

test : ∀{n SΓ Γ ST St} →  Exp {n} {SΓ} Γ ST St → Exp Γ ST St → ℕ
test {.(suc _)} {SΓ} (Elambda e₁) e₂ = {! e₂  !}
test {n} {SΓ} (Evar icx) e₂ = {!   !}
test {.(suc _)} {SΓ} (Eapp e₁ e₃) e₂ = {!   !}
test {.(suc (suc _))} {SΓ} (EΠ e₁ e₃) e₂ = {!   !}
test {.(suc (suc _))} {SΓ} EU e₂ = {!   !}
test {.(suc _)} {SΓ} (EcumuValue e₁) e₂ = {!   !}
test {.(suc (suc _))} {SΓ} (Ecumu e₁) e₂ = {!   !}
