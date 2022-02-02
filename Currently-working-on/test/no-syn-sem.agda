{-# OPTIONS --without-K #-}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Unit
open import Data.Nat
open import Data.Empty
open import Data.Product
open import Function
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
module Sᵀ where

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

data Context : Sᵀ.Ctx → Set₁ where
  ∅ : Context Sᵀ.nil
  _,_ : ∀{n SΓ} → (ctx : Context SΓ) → (T : Sᵀ.Type n SΓ) → Context (Sᵀ.cons SΓ T)

data Var : ∀{n} → {SΓ : Sᵀ.Ctx} → (Γ : Context SΓ) → (T : Sᵀ.Type n SΓ)
  → Sᵀ.Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Sᵀ.Type n SΓ} → {Γ : Context SΓ}
    → Var {n} (Γ , T) (Sᵀ.weakenT T T) (Sᵀ.same T)
  next : ∀{n m SΓ Γ A a} → {T : Sᵀ.Type n SΓ} → Var {m} {SΓ} Γ A a
    → Var (Γ , T) (Sᵀ.weakenT T A) (Sᵀ.next A T a)

data Term : ∀{n} → {SΓ : Sᵀ.Ctx} → (Γ : Context SΓ) → (T : Sᵀ.Type n SΓ)
  → Sᵀ.Term SΓ T → Set₁ where
  lambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Sᵀ.Type (suc n) SΓ}
    → {B : Sᵀ.Type (suc n) (Sᵀ.cons SΓ A)} → ∀{a}
    → Term (Γ , A) B a → Term Γ (Sᵀ.Π A B) (Sᵀ.lambda {n} {SΓ} {A} {B} a)
  var : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ}
    → {a : Sᵀ.Term SΓ T} → (icx : Var Γ T a) → Term {n} {SΓ} Γ T a
  app : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {A : Sᵀ.Type (suc n) SΓ}
      → {B : Sᵀ.Type (suc n) (Sᵀ.cons SΓ A)} → ∀{a₁ a₂}
      → Term {suc n} Γ (Sᵀ.Π A B) a₁ → (x : Term {suc n} Γ A a₂)
      → Term {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sᵀ.app A B a₁ a₂)
  Π : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {a₁ : Sᵀ.Term SΓ (Sᵀ.U {suc n})}
    → {a₂ : Sᵀ.Type (suc n) (Sᵀ.cons SΓ a₁)} → (A : Term Γ (Sᵀ.U {suc n}) a₁)
    → (B : Term (Γ , a₁) (Sᵀ.U {suc n}) a₂)
    → Term Γ (Sᵀ.U {suc n}) (Sᵀ.Π {n} a₁ a₂)
  U : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → Term {suc (suc n)} {SΓ} Γ Sᵀ.U Sᵀ.U
  Lift : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → ∀{a}
    → Term Γ (Sᵀ.U {n}) a → Term Γ (Sᵀ.U {suc n}) (Sᵀ.Lift a)
  lift : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ} → ∀{a}
    → Term Γ T a → Term Γ (Sᵀ.Lift T) (Sᵀ.lift T a)
  lower : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ} → ∀{a}
    → Term Γ (Sᵀ.Lift T) a → Term Γ T (Sᵀ.lift T a)

s : (X : Set₁) → X → X → X
s = λ X x₁ x₂ → x₁
-- s = λ X x₁ x₂ → x₂

T : Term ∅ (Sᵀ.U {2}) _
T = Π U (Lift (Π (var same) (Π (var (next same))
  (var (next (next same))))))

[_] : ∀{n SΓ Γ T t} → Term {n} {SΓ} Γ T t → Sᵀ.Term SΓ T
[_] {_} {_} {_} {_} {t} _ = t

e : Term ∅ [ T ] _
e = lambda (lift (lambda (lambda
    (s (Term _ _ _) (var same) (var same)))))
-- e = lambda (lift (lambda (lambda (
--     let (t , e) = s (Σ _ (λ t → Term _ _ t)) (_ , var (next same) ) (_ , var same)
--     in e
--     ))))

-- PROBLEM: the value of the var is in it's type. So I can't plug them
-- both in to s with the same type.
-- eval-style would technically fix this.

-- e : Term ∅ (Sᵀ.Π
--   Sᵀ.U
--   (Sᵀ.Π (Sᵀ.Lift λ (_ , X) → X)
--   (Sᵀ.Π {!   !}
--     {!   !}))) _
