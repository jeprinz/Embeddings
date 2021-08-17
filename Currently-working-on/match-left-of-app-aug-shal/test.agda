{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Data.Nat
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Maybe

module test where

module S where

  -- arbitrarily pick some type levels to work with.
  i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
  j = lsuc i -- type level 1+i

  Ctx : Set j
  Type : Ctx → Set j
  Var : (Γ : Ctx) → Type Γ → Set i
  Exp : (Γ : Ctx) → Type Γ → Set i

  Ctx = Set i
  Type Γ = Γ → Set i
  Type₀ = λ (Γ : Ctx) → Γ → Set₀
  Type₁ = λ (Γ : Ctx) → Γ → Set₁
  Type₂ = λ (Γ : Ctx) → Γ → Set₂
  Var Γ T = (γ : Γ) → T γ
  Exp Γ T = (γ : Γ) → T γ

  ∅ : Ctx
  ∅ = ⊤
  cons : (Γ : Ctx) → Type Γ → Ctx
  cons Γ T = Σ {i} {i} Γ T

  Π : ∀{Γ} → (A : Type Γ) → Type (cons Γ A) → Type Γ
  Π A B = λ γ → (a : A γ) → B (γ , a)

  Π₀ : ∀{Γ} → (A : Type₀ Γ) → Type₀ (cons Γ A) → Type₀ Γ
  Π₀ A B = λ γ → (a : A γ) → B (γ , a)

  Π₁ : ∀{Γ} → (A : Type₁ Γ) → Type₁ (cons Γ A) → Type₁ Γ
  Π₁ A B = λ γ → (a : A γ) → B (γ , a)

  Π₂ : ∀{Γ} → (A : Type₂ Γ) → Type₂ (cons Γ A) → Type₂ Γ
  Π₂ A B = λ γ → (a : A γ) → B (γ , a)

  U₀ : ∀{Γ} → Type₁ Γ
  U₀ γ = Set₀

  U₁ : ∀{Γ} → Type₂ Γ
  U₁ γ = Set₁

  weakenT : ∀{Γ T} → Type Γ → Type (cons Γ T)
  weakenT T (γ , _) = T γ

  same : ∀{Γ T} → Var (cons Γ T) (weakenT T)
  same = λ (γ , t) → t
  next : ∀{Γ T A} → Var Γ A → Var (cons Γ T) (weakenT A)
  next x = λ (γ , t) → x γ

  var : ∀{Γ T} → (icx : Var Γ T) → Exp Γ T
  var x = x

  lambda : ∀{Γ A B} → Exp (cons Γ A) B → Exp Γ (Π A B)
  lambda e = λ γ a → e (γ , a)

  app : ∀{Γ A B} → Exp Γ (Π A B) → (a : Exp Γ A) → Exp Γ (λ γ → B (γ , a γ))
  app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

  Sub : Ctx → Ctx → Set j
  Sub Γ₁ Γ₂ = Γ₂ → Γ₁

  append1ren : ∀{Γ₁ Γ₂} → {T : Type Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
  append1ren sub (γ₂ , t) = sub γ₂

  append1sub : ∀{Γ₁ Γ₂} → {T : Type Γ₁} → Sub Γ₁ Γ₂ → Exp Γ₁ T → Sub (cons Γ₁ T) Γ₂
  append1sub sub e γ₂ = sub γ₂ , e (sub γ₂)

  idSub : ∀{Γ} → Sub Γ Γ
  idSub γ = γ

  weaken1Ren : ∀{Γ T} → Sub Γ (cons Γ T)
  weaken1Ren = proj₁

  subType : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
  subType sub T = λ γ₂ → T (sub γ₂)

  forget1ren : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → (T : Type Γ₁)
    → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
  forget1ren sub T (γ , t) = sub γ , t

  subExp : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Exp Γ₁ T → Exp Γ₂ (subType sub T)
  subExp sub e = λ γ₂ → e (sub γ₂)

i = S.i
j = S.j

data Context : S.Ctx → Set j where
  ∅ : Context S.∅
  _,_ : ∀{sΓ} → Context sΓ → (T : S.Type sΓ) → Context (S.cons sΓ T)

data Var : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → (S.Exp sΓ T) → Set j where
  same : ∀{sΓ T} → {Γ : Context sΓ} → Var (Γ , T) (S.weakenT T) S.same
  next : ∀{sΓ Γ T A s} → Var {sΓ} Γ A s → Var (Γ , T) (S.weakenT A) (S.next s)

mutual
  data FuncExp : {sΓ : S.Ctx} → (Γ : Context sΓ)
    → (A : S.Type sΓ) → (B : S.Type (S.cons sΓ A))
    → S.Exp sΓ (S.Π A B) → Set j where
    lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s}
      → Exp3 (Γ , A) B s → FuncExp Γ A B (S.lambda s)
    fromExp : ∀{sΓ Γ A B t} → Ne {sΓ} Γ (S.Π A B) t → FuncExp Γ A B t

  data Ne : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
    → S.Exp sΓ T → Set j where
    var : {sΓ : S.Ctx} → {Γ : Context sΓ} → {T : S.Type sΓ} → {s : S.Exp sΓ T}
      → Var Γ T s → Ne {sΓ} Γ T s
    app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
        → FuncExp Γ A B s₁ → (x : Exp3 Γ A s₂)
        → Ne Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
    -- Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
    --   → (A : Ne Γ S.U₀ s₁)
    --   → (B : Ne (Γ , s₁) S.U₀ s₂)
    --   → Ne Γ S.U₀ (S.Π₀ s₁ s₂)
    -- Π₁ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
    --   → (A : Ne Γ S.U₁ s₁)
    --   → (B : Ne (Γ , s₁) S.U₁ s₂)
    --   → Ne Γ S.U₁ (S.Π₁ s₁ s₂)
    -- U₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → Ne {sΓ} Γ S.U₁ S.U₀

  data Exp3 : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
    → S.Exp sΓ T → Set j where
    fromExp2 : ∀{sΓ Γ T t} → Ne {sΓ} Γ T t → Exp3 Γ T t
    fromFuncExp : ∀{sΓ Γ A B t} → FuncExp {sΓ} Γ A B t → Exp3 Γ (S.Π A B) t

data Exp : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → S.Exp sΓ T → Set j where
  lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s}
    → Exp (Γ , A) B s → Exp Γ (S.Π A B) (S.lambda s)
  var : {sΓ : S.Ctx} → {Γ : Context sΓ} → {T : S.Type sΓ} → {s : S.Exp sΓ T}
    → Var Γ T s → Exp {sΓ} Γ T s
  app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
      → Exp Γ (S.Π A B) s₁ → (x : Exp Γ A s₂)
      → Exp Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
  Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
    → (A : Exp Γ S.U₀ s₁)
    → (B : Exp (Γ , s₁) S.U₀ s₂)
    → Exp Γ S.U₀ (S.Π₀ s₁ s₂)
  Π₁ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
    → (A : Exp Γ S.U₁ s₁)
    → (B : Exp (Γ , s₁) S.U₁ s₂)
    → Exp Γ S.U₁ (S.Π₁ s₁ s₂)
  U₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → Exp {sΓ} Γ S.U₁ S.U₀

Ren : ∀{sΓ₁ sΓ₂} → S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set j
Ren sub Γ₁ Γ₂ = ∀{T t} → Var Γ₁ T t → Var Γ₂ (S.subType sub T) (S.subExp sub t)

idRen : ∀{sΓ Γ} → Ren {sΓ} S.idSub Γ Γ
idRen x = x

forget1ren : ∀{sΓ₁ sΓ₂ T} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₁ Γ₂ → Ren (S.forget1ren sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)
forget1ren ren same = same
forget1ren ren (next x) = next (ren x)

weaken1Ren : ∀{sΓ Γ T} → Ren {sΓ} S.weaken1Ren Γ (Γ , T)
weaken1Ren = next

mutual
  renExp3 : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Ren sub Γ₁ Γ₂ → Exp3 Γ₁ T t → Exp3 Γ₂ (S.subType sub T) (S.subExp sub t)
  renExp3 ren (fromExp2 e) = fromExp2 (renNe ren e)
  renExp3 ren (fromFuncExp e) = fromFuncExp (renFuncExp ren e)

  renNe : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Ren sub Γ₁ Γ₂ → Ne Γ₁ T t → Ne Γ₂ (S.subType sub T) (S.subExp sub t)
  renNe ren (var x) = var (ren x)
  renNe ren (app e₁ e₂) = app (renFuncExp ren e₁) (renExp3 ren e₂)
  -- renNe ren (Π₀ A B) = {!   !}
  -- renNe ren (Π₁ A B) = {!   !}
  -- renNe ren U₀ = U₀

  renFuncExp : ∀{sΓ₁ sΓ₂ A B t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Ren sub Γ₁ Γ₂ → FuncExp Γ₁ A B t
    → FuncExp Γ₂ (S.subType sub A) (S.subType (S.forget1ren sub _) B) (S.subExp sub t)
  renFuncExp ren (lambda e) = lambda (renExp3 (forget1ren ren) e)
  renFuncExp ren (fromExp e) = fromExp (renNe ren e)

{-

Why this will fail:
when defining subExp,subNe, subFuncExp,
the substitution will output Exp3's. So, renNe will output Exp3 instead of Ne.
Therefore, so will renFuncExp, because it uses it.
But then, on left of app, wont be able to fill in.

what is sub_ outputs Exp instead???

-}

renExp : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₁ Γ₂ → Exp Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)
renExp ren (lambda e) = lambda (renExp (forget1ren ren) e)
renExp ren (var x) = var (ren x)
renExp ren (app e₁ e₂) = app (renExp ren e₁) (renExp ren e₂)
renExp ren (Π₀ A B) = Π₀ (renExp ren A) (renExp (forget1ren ren) B)
renExp ren (Π₁ A B) = Π₁ (renExp ren A) (renExp (forget1ren ren) B)
renExp ren U₀ = U₀

Sub : ∀{sΓ₁ sΓ₂} → S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set j
Sub sub Γ₁ Γ₂ = ∀{T t} → Var Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)

forget1sub : ∀{sΓ₁ sΓ₂ T} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₁ Γ₂ → Sub (S.forget1ren sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)
forget1sub sub same = var same
forget1sub sub (next x) = renExp weaken1Ren (sub x)

-- append1sub : ∀{Γ₁ Γ₂} → {T : Type Γ₁} → Sub Γ₁ Γ₂ → Exp Γ₁ T → Sub (cons Γ₁ T) Γ₂
-- append1sub sub e γ₂ = sub γ₂ , e (sub γ₂)
append1sub : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂}
  → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Exp Γ₁ T t
  → Sub sub Γ₁ Γ₂ → Sub (S.append1sub sub t) (Γ₁ , T) Γ₂

idSub : ∀{sΓ} → {Γ : Context sΓ} → Sub S.idSub Γ Γ

mutual
  subExp3 : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Sub sub Γ₁ Γ₂ → Exp3 Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)
  subExp3 sub (fromExp2 e) = subNe sub e
  subExp3 sub (fromFuncExp e) = subFuncExp sub e

  subNe : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Sub sub Γ₁ Γ₂ → Ne Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)
  subNe sub (var x) = sub x
  subNe sub (app e₁ e₂) = app (subFuncExp sub e₁) (subExp3 sub e₂)

  subFuncExp : ∀{sΓ₁ sΓ₂ A B t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Sub sub Γ₁ Γ₂ → FuncExp Γ₁ A B t
    → Exp Γ₂ (S.Π (S.subType sub A) (S.subType (S.forget1ren sub _) B)) (S.subExp sub t)
  subFuncExp sub (lambda e) = lambda (subExp3 (forget1sub sub) e)
  subFuncExp sub (fromExp e) = subNe sub e

thing : ∀{sΓ Γ T t} → ℕ → Exp3 {sΓ} Γ T t → Exp Γ T t
thing 0 _ = {!   !}
thing (suc n) (fromExp2 (var x)) = var x
thing (suc n) (fromExp2 (app (lambda e₁) e₂)) = subExp3 (append1sub (thing n e₂) idSub) e₁
thing (suc n) (fromExp2 (app (fromExp e) e₂)) = app (thing n (fromExp2 e)) (thing n e₂)
thing (suc n) (fromFuncExp (lambda x)) = lambda (thing n x)
thing (suc n) (fromFuncExp (fromExp x)) = thing n (fromExp2 x)

-- But... if we have something like
-- (λ x . x e) (λ x . x)
-- then the first β-reduction can happen, but the second one can't
-- because it would have to figure out that its a lambda...

-- axiom : ∀{A B A' B'} → ((a : A) → B a) ≡ ((a : A') → B' a) → A ≡ A' × B ≡ B'
-- using funext and SemT, we can get what we want with (A → B) ≡ (A' → B')  → A ≡ A', B ≡ B'

test : ∀{sΓ Γ T t} → Exp {sΓ} Γ T t → ℕ
test (lambda e) = {!   !}
test (var x) = {!   !}
test (app e e₁) = {!e   !}
test (Π₀ e e₁) = {!   !}
test (Π₁ e e₁) = {!   !}
test U₀ = {!   !}
