{-# OPTIONS --without-K #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function

--------------------------------------------------------------------------------
-- Definition of typecodes.

data TypeCode₀ : Set where
⟦_⟧₀ : TypeCode₀ → Set
⟦_⟧₀ ()

module Universe {TypeCode : Set} {⟦_⟧ : TypeCode → Set} where
  mutual
    data TypeCodeₙ₊₁ : Set where
        `U : TypeCodeₙ₊₁
        `Π : (A : TypeCodeₙ₊₁) → (⟦_⟧ₙ₊₁ A → TypeCodeₙ₊₁) → TypeCodeₙ₊₁
        `lift : TypeCode → TypeCodeₙ₊₁

    ⟦_⟧ₙ₊₁ : TypeCodeₙ₊₁ → Set
    ⟦ `U ⟧ₙ₊₁ = TypeCode
    ⟦ `Π A B ⟧ₙ₊₁ = (a : ⟦ A ⟧ₙ₊₁) → ⟦ B a ⟧ₙ₊₁
    ⟦ `lift T ⟧ₙ₊₁ = ⟦ T ⟧

open Universe

mutual
  TypeCode : ℕ → Set
  TypeCode zero = TypeCode₀
  TypeCode (suc n) = TypeCodeₙ₊₁ {TypeCode n} {⟦_⟧}

  ⟦_⟧ : {n : ℕ} → TypeCode n → Set
  ⟦_⟧ {zero} T = ⟦ T ⟧₀
  ⟦_⟧ {suc n} T = ⟦ T ⟧ₙ₊₁

------------------------  "Shallow" embedding   --------------------------------
module S where

  Ctx = Set
  Type : ℕ → Ctx → Set
  Type n Γ = Γ → TypeCode n
  Term : ∀{n} → (Γ : Ctx) → Type n Γ → Set
  Term Γ T = (γ : Γ) → ⟦ T γ ⟧
  Var : ∀{n} → (Γ : Ctx) → Type n Γ → Set
  Var Γ T = (γ : Γ) → ⟦ T γ ⟧
  nil : Ctx
  nil = ⊤
  cons : ∀{n} → (Γ : Ctx) → Type n Γ → Ctx
  cons Γ T = Σ Γ (λ γ → ⟦ T γ ⟧)

  U : ∀{n Γ} → Type (suc n) Γ
  U = λ _ → `U

  Π : ∀{n Γ} → (A : Type (suc n) Γ) → Type (suc n) (cons Γ A) → Type (suc n) Γ
  Π A B = λ γ → `Π (A γ) ((λ a → B (γ , a)))

  lambda : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
    → Term (cons Γ A) B → Term Γ (Π A B)
  lambda e = λ γ → λ a → e (γ , a)

  app : ∀{n Γ} → (A : Type (suc n) Γ) → (B : Type (suc n) (cons Γ A))
    → Term Γ (Π A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
  app A B e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

  weakenT : ∀{n m Γ} → (T : Type m Γ) → Type n Γ → Type n (cons Γ T)
  weakenT T A (γ , _) = A γ

  same : ∀{n Γ} → (T : Type n Γ) → Var {n} (cons Γ T) (weakenT T T)
  same T = λ (γ , t) → t
  next : ∀{n m Γ} → (A : Type n Γ) → (T : Type m Γ)
    → Var {n} Γ A → Var {n} (cons Γ T) (weakenT T A)
  next A T x = λ (γ , t) → x γ

  weaken : ∀{n Γ} → {T A : Type n Γ} → Term Γ T
    → Term (cons Γ A) (weakenT A T)
  weaken e = λ γ → e (proj₁ γ)

  Lift : ∀{n Γ} → (T : Type n Γ) → Type (suc n) Γ
  Lift T = λ γ → `lift (T γ)

  lift : ∀{n Γ} → (T : Type n Γ) → Term Γ T → Term Γ (Lift T)
  lift T e = e

  lower : ∀{n Γ} → (T : Type n Γ) → Term Γ (Lift T) → Term Γ T
  lower T e = e

  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = Γ₂ → Γ₁

  extend : ∀{n Γ₁ Γ₂} → (T : Type n Γ₁)
    → Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
  extend T sub e γ₂ = sub γ₂ , e (sub γ₂)

  idSub : ∀{Γ} → Sub Γ Γ
  idSub γ = γ

  weaken1Ren : ∀{Γ n T} → Sub Γ (cons {n} Γ T)
  weaken1Ren = proj₁

  subType : ∀{Γ₁ Γ₂ n} → Sub Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
  subType sub T = λ γ₂ → T (sub γ₂)

  liftSub : ∀{Γ₁ Γ₂ n} → (sub : Sub Γ₁ Γ₂) → (T : Type n Γ₁)
    → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
  liftSub sub T (γ , t) = sub γ , t

  subTerm : ∀{Γ₁ Γ₂ n} → (T : Type n Γ₁) → (sub : Sub Γ₁ Γ₂)
    → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
  subTerm T sub e = λ γ₂ → e (sub γ₂)

-------------------- Augmented "shallow" embedding -----------------------------
data Context : S.Ctx → Set₁ -- where
data Term : ∀{n} → {SΓ : S.Ctx} → (Γ : Context SΓ) → (T : S.Type n SΓ)
  → S.Term SΓ T → Set₁ -- where

data Context where
  ∅ : Context S.nil
  _,_ : ∀{n SΓ} → (Γ : Context SΓ) → {sT : S.Type n SΓ}
    → (T : Term Γ (S.U {n}) sT) → Context (S.cons SΓ sT)

data Var : ∀{n} → {SΓ : S.Ctx} → (Γ : Context SΓ) → (T : S.Type n SΓ)
  → S.Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {sT : S.Type n SΓ} → {Γ : Context SΓ}
    → {T : Term Γ S.U sT}
    → Var {n} (Γ , T) (S.weakenT sT sT) (S.same sT)
  next : ∀{n m SΓ Γ sA a} → {sT : S.Type n SΓ}
    → {T : Term Γ S.U sT}
    → Var {m} {SΓ} Γ sA a
    → Var (Γ , T) (S.weakenT sT sA) (S.next sA sT a)

data Term where
  lambda : ∀{n SΓ} → {Γ : Context SΓ} → {sA : S.Type (suc n) SΓ}
    → {sB : S.Type (suc n) (S.cons SΓ sA)} → ∀{a}
    → (A : Term Γ S.U sA)
    → Term (Γ , A) sB a → Term Γ (S.Π sA sB) (S.lambda {n} {SΓ} {sA} {sB} a)
  var : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → {T : S.Type n SΓ}
    → {a : S.Term SΓ T} → (icx : Var Γ T a) → Term {n} {SΓ} Γ T a
  app : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → {A : S.Type (suc n) SΓ}
      → {B : S.Type (suc n) (S.cons SΓ A)} → ∀{a₁ a₂}
      → Term {suc n} Γ (S.Π A B) a₁ → (x : Term {suc n} Γ A a₂)
      → Term {suc n} Γ (λ γ → B (γ , a₂ γ)) (S.app A B a₁ a₂)
  Π : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → {a₁ : S.Term SΓ (S.U {suc n})}
    → {a₂ : S.Type (suc n) (S.cons SΓ a₁)} → (A : Term Γ (S.U {suc n}) a₁)
    → (B : Term (Γ , A) (S.U {suc n}) a₂)
    → Term Γ (S.U {suc n}) (S.Π {n} a₁ a₂)
  U : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → Term {suc (suc n)} {SΓ} Γ S.U S.U
  Lift : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → ∀{a}
    → Term Γ (S.U {n}) a → Term Γ (S.U {suc n}) (S.Lift a)
  lift : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → {T : S.Type n SΓ} → ∀{a}
    → Term Γ T a → Term Γ (S.Lift T) (S.lift T a)
  lower : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → {T : S.Type n SΓ} → ∀{a}
    → Term Γ (S.Lift T) a → Term Γ T (S.lift T a)

typeOfVar : ∀{n sΓ sT s} → {Γ : Context sΓ} → Var {n} Γ sT s
  → Term {suc n} Γ S.U sT -- suc n?
typeOfVar (same {_} {_} {_} {_} {T}) = {! T  !}
typeOfVar (next x) = {! typeOfVar x  !}


-- isPi : ∀{n sΓ Γ sA sB} → Term {suc (suc n)} {sΓ} Γ S.U (S.Π sA sB)
--   → (Σ (Term Γ S.U sA) (λ A → Term (Γ , A) (S.U {suc n}) sB))
-- isPi e = {! e  !}

Eq2 : {l : Level} {P : Set l} {Q : P → Set l}
  → (a₁ a₂ : P) → Q a₁ → Q a₂ → Set l
Eq2 {l} {P} {Q} a₁ a₂ b₁ b₂
  = _≡_ {l} {Σ P Q} (a₁ , b₁) (a₂ , b₂)

-- isPi2 : ∀{n sΓ Γ sT s} → Term {2 + n} {sΓ} Γ sT s
--   → {sA : S.Type (suc n) sΓ} → {sB : S.Type (suc n) (S.cons sΓ sA)}
--   → Eq2 {_} {_} {S.Term sΓ} sT S.U s (S.Π sA sB)
--   → (Σ (Term Γ S.U sA) (λ A → Term (Γ , A) (S.U {suc n}) sB))
-- isPi2 (lambda e e₁) p = {!   !}
-- isPi2 (var icx) p = {!   !}
-- isPi2 (app e e₁) p = {!   !}
-- isPi2 (Π A B) p = {! A  !}
-- isPi2 U p = {!   !}
-- isPi2 (Lift e) p = {!   !}
-- isPi2 (lift e) p = {!   !}
-- isPi2 (lower e) p = {!   !}
--
-- counterExample : Term {2} (∅ , Π U (Lift (var same))) S.U (S.Π S.U S.U)
-- counterExample = {! U  !}

getType : ∀{n sΓ Γ sT s} → Term {n} {sΓ} Γ sT s → Term {suc n} Γ S.U sT -- suc n?
getType (lambda A e) = Π A (getType e)
getType (var x) = typeOfVar x
getType (app e₁ e₂) = {! getType e₁  !}
getType (Π A B) = U
getType U = U
getType (Lift e) = U
getType (lift e) = Lift (getType e)
getType (lower e) = {! getType e  !}

{-

  -- Renamings and Substitutions on Term

Ren : ∀{sΓ₁ sΓ₂} → S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
Ren sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Var Γ₂ (S.subType sub T) (S.subTerm T sub t)

idRen : ∀{sΓ Γ} → Ren {sΓ} S.idSub Γ Γ
idRen x = x

liftRen : ∀{n sΓ₁ sΓ₂ T} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₁ Γ₂ → Ren (S.liftSub {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)
liftRen ren same = same
liftRen ren (next x) = next (ren x)

weaken1Ren : ∀{sΓ Γ n T} → Ren {sΓ} (S.weaken1Ren {sΓ} {n} {T}) Γ (Γ , T)
weaken1Ren = next

renTerm : ∀{n sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₁ Γ₂ → Term {n} Γ₁ T t → Term Γ₂ (S.subType sub T) (S.subTerm T sub t)
renTerm ren (lambda e) = lambda (renTerm (liftRen ren) e)
renTerm ren (var x) = var (ren x)
renTerm ren (app e₁ e₂) = app (renTerm ren e₁) (renTerm ren e₂)
renTerm ren (Π A B) = Π (renTerm ren A) (renTerm (liftRen ren) B)
renTerm ren U = U
renTerm ren (Lift e) = Lift (renTerm ren e)
renTerm ren (lift e) = lift (renTerm ren e)
renTerm ren (lower e) = lower (renTerm ren e)

Sub : ∀{sΓ₁ sΓ₂} → S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
Sub sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Term Γ₂ (S.subType sub T) (S.subTerm T sub t)

idSub : ∀{sΓ Γ} → Sub {sΓ} S.idSub Γ Γ
idSub x = var x

liftSub : ∀{n sΓ₁ sΓ₂ T} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₁ Γ₂ → Sub (S.liftSub {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)
liftSub sub same = var same
liftSub sub (next x) = renTerm weaken1Ren (sub x)

subTerm : ∀{n sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₁ Γ₂ → Term {n} Γ₁ T t → Term Γ₂ (S.subType sub T) (S.subTerm T sub t)
subTerm sub (lambda e) = lambda (subTerm (liftSub sub) e)
subTerm sub (var x) = sub x
subTerm sub (app e₁ e₂) = app (subTerm sub e₁) (subTerm sub e₂)
subTerm sub (Π A B) = Π (subTerm sub A) (subTerm (liftSub sub) B)
subTerm sub U = U
subTerm sub (Lift e) = Lift (subTerm sub e)
subTerm sub (lift e) = lift (subTerm sub e)
subTerm sub (lower e) = lower (subTerm sub e)

extend : ∀{sΓ₁ sΓ₂ n Γ₁ Γ₂ sub} → {T : S.Type n sΓ₁} → {t : S.Term sΓ₁ T}
  → Sub {sΓ₁} {sΓ₂} sub Γ₁ Γ₂
  → Term Γ₁ T t → Sub (S.extend T sub t) (Γ₁ , T) Γ₂
extend sub e same = subTerm sub e
extend sub e (next x) = sub x

--------------------------------------------------------------------------------
-}
