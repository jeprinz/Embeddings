{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality

module let-nf-encoding-augmented-shallow-embedding where

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

  append1sub : ∀{Γ₁ Γ₂} → {T : Type Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
  append1sub sub (γ₂ , t) = sub γ₂

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
  data Ne : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
    → S.Exp sΓ T → Set j where
    var : {sΓ : S.Ctx} → {Γ : Context sΓ} → {T : S.Type sΓ} → {s : S.Exp sΓ T}
      → Var Γ T s → Ne {sΓ} Γ T s
    app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
        → Ne Γ (S.Π A B) s₁ → (x : Nf Γ A s₂)
        → Ne Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
    Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
      → (A : Nf Γ S.U₀ s₁)
      → (B : Nf (Γ , s₁) S.U₀ s₂)
      → Ne Γ S.U₀ (S.Π₀ s₁ s₂)
    Π₁ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
      → (A : Nf Γ S.U₁ s₁)
      → (B : Nf (Γ , s₁) S.U₁ s₂)
      → Ne Γ S.U₁ (S.Π₁ s₁ s₂)
    U₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → Ne {sΓ} Γ S.U₁ S.U₀

  data Nf : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
    → S.Exp sΓ T → Set j where
    lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s}
      → Nf (Γ , A) B s → Nf Γ (S.Π A B) (S.lambda s)
    ne : ∀{sΓ Γ T t} → Ne {sΓ} Γ T t → Nf Γ T t
    Let : ∀{sΓ A a B b} → {Γ : Context sΓ}
      → Nf Γ A a → Nf (Γ , A) B b → Nf Γ (λ γ → B (γ , a γ)) (λ γ → b (γ , a γ))

-- x e₁ ... eₙ    is a Ne
-- (λ x . e₁) e₂   =  let x = e₂ in e₁
-- (λ x y z . e₁) e₂ e₃ e₄   =  let x = e₂, y = e₃, z = e₄ in e₁
-- (λ x . e₁) e₂ e₃ e₄      = (let x = e₂ in e₁) e₃ e₄
--                ? = (let x = e₂ in e₁ e₃ e₄) -- then recursively remove applications on e₁?

Ren : ∀{sΓ₁ sΓ₂} → S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set j
Ren sub Γ₁ Γ₂ = ∀{T t} → Var Γ₁ T t → Var Γ₂ (S.subType sub T) (S.subExp sub t)

idRen : ∀{sΓ Γ} → Ren {sΓ} S.idSub Γ Γ
idRen x = x

weaken1Ren : ∀{sΓ Γ T} → Ren {sΓ} S.weaken1Ren Γ (Γ , T)
weaken1Ren = next

forget1ren : ∀{sΓ₁ sΓ₂ T} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₁ Γ₂ → Ren (S.forget1ren sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)
forget1ren ren same = same
forget1ren ren (next x) = next (ren x)

mutual
  renNf : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Ren sub Γ₁ Γ₂ → Nf Γ₁ T t → Nf Γ₂ (S.subType sub T) (S.subExp sub t)
  renNf ren (lambda e) = lambda (renNf (forget1ren ren) e)
  renNf ren (ne e) = ne (renNe ren e)
  renNf ren (Let e₁ e₂) = Let (renNf ren e₁) (renNf (forget1ren ren) e₂)

  renNe : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
    → Ren sub Γ₁ Γ₂ → Ne Γ₁ T t → Ne Γ₂ (S.subType sub T) (S.subExp sub t)
  renNe ren (var x) = var (ren x)
  renNe ren (app e₁ e₂) = app (renNe ren e₁) (renNf ren e₂)
  renNe ren (Π₀ A B) = Π₀ (renNf ren A) (renNf (forget1ren ren) B)
  renNe ren (Π₁ A B) = Π₁ (renNf ren A) (renNf (forget1ren ren) B)
  renNe ren U₀ = U₀


Sub : ∀{sΓ₁ sΓ₂} → S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set j
Sub sub Γ₁ Γ₂ = ∀{T t} → Var Γ₁ T t → Nf Γ₂ (S.subType sub T) (S.subExp sub t)

App : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ}
  → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
  → Nf Γ (S.Π A B) s₁ → (x : Nf Γ A s₂)
  → Nf Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
App e₁ e₂ = Let e₁ (ne (app (var same) (renNf weaken1Ren e₂)))

-- Is expanded eta form possible?

forget1sub : ∀{sΓ₁ sΓ₂ T} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₁ Γ₂ → Sub (S.forget1ren sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)
forget1sub sub same = ne (var same)
forget1sub sub (next x) = renNf weaken1Ren (sub x)
{-

subExp : ∀{sΓ₁ sΓ₂ T t} → {sub : S.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₁ Γ₂ → Exp Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)
subExp sub (lambda e) = lambda (subExp (forget1sub sub) e)
subExp sub (var x) = sub x
subExp sub (app e₁ e₂) = app (subExp sub e₁) (subExp sub e₂)
subExp sub (Π₀ A B) = Π₀ (subExp sub A) (subExp (forget1sub sub) B)
subExp sub (Π₁ A B) = Π₁ (subExp sub A) (subExp (forget1sub sub) B)
subExp sub U₀ = U₀
-}

-- Let needs to work with variables that arent just at top of context !??!??
-- wait doesn't it?

-- (x a) [x ↦ e] where either e = (ne e)  or  e = lambda e
doTheStep : ∀{sΓ Γ}
