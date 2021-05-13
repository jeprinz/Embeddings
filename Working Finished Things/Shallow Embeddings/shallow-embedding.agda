{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --without-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
-- open import Data.Sum
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

{-

Just a standard shallow embedding of dependent type theory.

-}

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

Ctx : Set j
Type : Ctx → Set j
Term : (Γ : Ctx) → Type Γ → Set i
Ctx = Set i
Type Γ = Γ → Set i
Term Γ T = (γ : Γ) → T γ

-- Context constructors
nil : Ctx
nil = ⊤

cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ Γ T

-- Type constructors
U₀ : ∀{Γ} → Type Γ
U₀ = λ γ → Set₀

U₁ : ∀{Γ} → Type Γ
U₁ = λ γ → Set₁

Π : ∀{Γ} → (A : Type Γ) → (B : Type (cons Γ A)) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

weakenT : {Γ : Ctx} → {A : Type Γ} → Type Γ → Type (cons Γ A)
weakenT T = λ γ → T (proj₁ γ)

varT : {Γ : Ctx} → Type (cons Γ U₀)
varT = proj₂

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


-- Example:

-- the following is the type "(X : Set₀) → X → X"
idT : Type nil
idT = Π U₀ (Π varT (weakenT varT))

-- the following is the term "λ X x . x"
id : Term nil idT
id = lambda (lambda var)

-- Type can be removed and replaced with terms in dependent type theory fashion.
-- but this is nonstandard and therefore probably not included in the parametricity mapping

U₀' : ∀{Γ} → Term Γ U₁
U₀' = λ γ → Set₀

Π' : ∀{Γ} → (A : Term Γ U₀) → (B : Term (cons Γ A) U₀) → Term Γ U₀
Π' A B = λ γ → (a : A γ) → B (γ , a)
