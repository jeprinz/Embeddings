open import Data.Nat
open import Data.List

{-

The idea of this file is to test the idea that an extrinsic approach
allows for subtyping.

E.g. with x : Fin n, x -:- Fin (1 + n).

-}

data Fin : ℕ → ℕ → Set where
  zero : ∀{n} → Fin (suc n) 0
  suc : ∀{n x} → Fin n x → Fin (suc n) (suc x)

-- equivalent to 5 : Fin 10
f : Fin 10 5
f = suc (suc (suc (suc (suc zero))))

data Fin2 : ℕ → ℕ → Set where
  zero : ∀{n} → Fin2 (suc n) n
  suc : ∀{n x} → Fin2 n x → Fin2 (suc n) x

-- equivalent to 5 : Fin 10
g : Fin2 10 5
g = suc (suc (suc (suc zero)))

data El : {T : Set} → List T → T → Set where
  zero : ∀{T t l} → El {T} (t ∷ l) t
  suc : ∀{T l t t'} → El {T} l t → El (t' ∷ l) t -- weakening for free!

{-

Goal for the rest of this file:
Implement EXTRINSIC NbE for STLC where NO renaming ever happens.
In general in NbE, weakening is needed but not actually general renaming.
With debruin LEVELS (as opposed to indices), weakening is nothing.

-- I should be able to figure this out eventually
-- consider looking at other people's existing implementations of extrinsic STLC

-}

data Type : Set where
  _⇒_ : Type → Type → Type
  base : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data _prefix_ : Ctx → Ctx → Set where
  refl : ∀{Γ} → Γ prefix Γ
  append : ∀{Γ₁ Γ₂ T} → Γ₁ prefix Γ₂ → Γ₁ prefix (Γ₂ , T)

len : Ctx → ℕ
len ∅ = 0
len (Γ , _) = 1 + len Γ

data Var : Ctx → Type → ℕ → Set where -- like ≥
  zero : ∀{Γ T} → Var (Γ , T) T (len Γ)
  succ : ∀{Γ A T n} → Var Γ T n → Var (Γ , A) T n


data PExp : Set where
  var : ℕ → PExp
  lambda : PExp → PExp
  app : PExp → PExp → PExp
  ⋆ : PExp

data _⊢_::_ : Ctx → PExp → Type → Set where
  -- var : ∀{Γ T} → (x : Ctx) → (x , T) prefix Γ → Γ ⊢ (var {!   !} ) :: T
  -- var : ∀{PΓ T} → {Γ : WCtx PΓ}
    -- → (x : PCtx) → PVar x PΓ → Γ ⊢ (var x) :: T
  var : ∀{Γ T} → {i : ℕ} → Var Γ T i → Γ ⊢ (var i) :: T
  lambda : ∀{Γ A B e} → (Γ , A) ⊢ e :: B → Γ ⊢ (lambda e) :: (A ⇒ B)
  app : ∀{Γ A B e₁ e₂} → Γ ⊢ e₁ :: (A ⇒ B) → Γ ⊢ e₂ :: A → Γ ⊢ (app e₁ e₂) :: B
  ⋆ : ∀{Γ} → Γ ⊢ ⋆ :: base


-- mutual
--   data Ne : Ctx → Type → Set where
--     -- var : ∀{Γ T} → (icx : InCtx Γ T) → Ne Γ T
--     var : ∀{Γ T} → (x : Ctx) → (x , T) prefix Γ → Ne Γ T
--     app : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
--     ⋆ : ∀{Γ} → Ne Γ base
--
--   data Nf : Ctx → Type → Set where
--     lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
--     ne : ∀{Γ} → Ne Γ base → Nf Γ base

PSem : Type → Set
PSem (A ⇒ B) = PSem A → PSem B
PSem base = PExp -- really Ne

WSem : (Γ : Ctx) → (T : Type) → PSem T → Set
WSem Γ (A ⇒ B) s = {sa : PSem A} → (a : WSem Γ A sa) → WSem Γ B (s sa) -- PSem Γ A → PSem Γ B
WSem Γ base s = Γ ⊢ s :: base -- should be Ne version of _⊢_::_

mutual
  PnApp : Ctx → ∀{T} → PExp → PSem T -- that PExp is really an Ne
  PnApp Γ {A ⇒ B} e = λ g → PnApp Γ (app e (Preify Γ g))
  PnApp Γ {base} e = e

  Preify : Ctx → ∀{T} → PSem T → PExp -- really an Nf
  Preify Γ {A ⇒ B} g = lambda (Preify (Γ , A) (g (PnApp (Γ , A) (var (len Γ)))))
  Preify Γ {base} g = g

mutual
  WnApp : (Γ : Ctx) → ∀{T} → {e : PExp} → Γ ⊢ e :: T → WSem Γ T (PnApp Γ e) -- that PExp is really an Ne
  WnApp Γ {A ⇒ B} E = λ G → WnApp Γ (app E (Wreify Γ G))
  WnApp Γ {base} E = E

  Wreify : (Γ : Ctx) → ∀{T} → {s : PSem T} → WSem Γ T s → Γ ⊢ (Preify Γ s) :: T -- really an Nf
  Wreify Γ {A ⇒ B} G = lambda (Wreify (Γ , A) let bla = G {! WnApp (Γ , A) ?  !} in {!   !} )
  Wreify Γ {base} G = G
{-

Sem : Ctx → Type → Set
Sem Γ (A ⇒ B) = Sem Γ A → Sem Γ B
Sem Γ base = Ne Γ base -- used to be Nf, but can be Ne!

mutual
  nApp : ∀{Γ T} → Ne Γ T → Sem Γ T
  nApp {_} {A ⇒ B} e = λ g → nApp (app e (reify g))
  nApp {_} {base} e = e

  reify : ∀{Γ T} → Sem Γ T → Nf Γ T
  -- reify {Γ} {A ⇒ B} g = lambda (reify (g (nApp ? )))
  reify {Γ} {A ⇒ B} g = lambda (reify {! g  !} )
  reify {Γ} {base} g = ne g

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → Sem Γ₂ T -- if Sub instead outputted a GSem, could renSem,renNf, and renNe be avoided?

idSub : ∀{Γ} → Sub Γ Γ
idSub x = nApp (var x)

_∘_ : ∀{A B C} → Ren A B → Ren B C → Ren A C
s₁ ∘ s₂ = λ x → s₂ (s₁ x)

renSem : ∀{Γ₁ Γ₂ T} → Ren Γ₁ Γ₂ → Sem Γ₁ T → Sem Γ₂ T
renSem {_} {_} {A ⇒ B} ren e = λ ren₁ a → e (ren ∘ ren₁) a
renSem {_} {_} {base} ren e = renNe ren e

transSR : ∀{Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Sub Γ₁ Γ₃
transSR sub ren x = renSem ren (sub x)

append1sub : ∀{Γ₁ A Γ₂} → Sub Γ₁ Γ₂ → Sem Γ₂ A → Sub (Γ₁ , A) Γ₂
append1sub sub e same = e
append1sub sub e (next x) = sub x

eval : ∀{Γ₁ Γ₂ T} → Exp Γ₁ T → Sub Γ₁ Γ₂ → Sem Γ₂ T
eval (var x) sub = sub x
-- eval (lambda e) sub = λ a → eval e (append1sub sub a)
eval (lambda e) sub = λ ren a → eval e (append1sub (transSR sub ren) a)
-- eval (app e₁ e₂) sub = (eval e₁ sub) (λ ren₁ → eval e₂ (transSR sub ren₁))
eval (app e₁ e₂) sub = (eval e₁ sub) idRen (eval e₂ sub)
eval ⋆ sub = ⋆

normalize : ∀{Γ T} → Exp Γ T → Nf Γ T
-- normalize e = reify (λ ren → eval e (transSR idSub ren))
normalize e = reify (eval e idSub)

-- some examples to test it out:

e1 : Exp ∅ base
e1 = app (lambda (var same)) ⋆

test1 : normalize e1 ≡ ne ⋆
test1 = refl

e2 : Exp ∅ base -- (λ x . x ⋆) (λ x . x)
e2 = app (lambda (app (var same) ⋆)) (lambda (var same))

test2 : normalize e2 ≡ ne ⋆
test2 = refl

e3 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) ⋆
e3 = lambda (app (lambda (var same)) ⋆)

test3 : normalize e3 ≡ lambda (ne ⋆)
test3 = refl

e4 : Exp ∅ (base ⇒ base) -- λ x . (λ y . y) x
e4 = lambda (app (lambda (var same)) (var same))

test4 : normalize e4 ≡ lambda (ne (var same))
test4 = refl


-- ------------------------------------ TEST --------------------------------------
-- weaken1Sub : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂)
--   → (T : Type) → Sub (Γ₁ , T) (Γ₂ , T)
-- weaken1Sub sub T = {!   !}
-}
