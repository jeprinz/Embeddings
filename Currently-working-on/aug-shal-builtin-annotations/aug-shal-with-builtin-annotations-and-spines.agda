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
  → S.Term SΓ T
  → ℕ
  → Set₁ -- where

data Context where
  ∅ : Context S.nil
  _,_ : ∀{n SΓ x} → (Γ : Context SΓ) → {sT : S.Type n SΓ}
    → (T : Term Γ (S.U {n}) sT x) → Context (S.cons SΓ sT)

data Var : ∀{n} → {SΓ : S.Ctx} → (Γ : Context SΓ) → (T : S.Type n SΓ)
  → S.Term SΓ T → Set₁ where
  same : ∀{n SΓ x} → {sT : S.Type n SΓ} → {Γ : Context SΓ}
    → {T : Term Γ S.U sT x}
    → Var {n} (Γ , T) (S.weakenT sT sT) (S.same sT)
  next : ∀{n m SΓ Γ sA a x} → {sT : S.Type n SΓ}
    → {T : Term Γ S.U sT x}
    → Var {m} {SΓ} Γ sA a
    → Var (Γ , T) (S.weakenT sT sA) (S.next sA sT a)

data Term where
  lambda : ∀{n SΓ x y} → {Γ : Context SΓ} → {sA : S.Type (suc n) SΓ}
    → {sB : S.Type (suc n) (S.cons SΓ sA)} → ∀{a}
    → (A : Term Γ S.U sA x)
    → Term (Γ , A) sB a y → Term Γ (S.Π sA sB) (S.lambda {n} {SΓ} {sA} {sB} a) 0
  var : ∀{n} → {SΓ : S.Ctx} → {Γ : Context SΓ} → {T : S.Type n SΓ}
    → {a : S.Term SΓ T} → (icx : Var Γ T a) → Term {n} {SΓ} Γ T a 1
  app : ∀{n n2} → {SΓ : S.Ctx} → {Γ : Context SΓ} → {A : S.Type (suc n) SΓ}
      → {B : S.Type (suc n) (S.cons SΓ A)} → ∀{a₁ a₂}
      → Term {suc n} Γ (S.Π A B) a₁ 0 → (x : Term {suc n} Γ A a₂ n2)
      → Term {suc n} Γ (λ γ → B (γ , a₂ γ)) (S.app A B a₁ a₂) 2

test : ∀{n sΓ Γ T t} → Term {n} {sΓ} Γ T t 2 → ℕ
test (app e e₁) = {! e  !}
