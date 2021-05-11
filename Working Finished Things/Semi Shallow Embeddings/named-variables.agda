{-# OPTIONS --cumulativity --without-K #-}

{-

This file demonstrates something that the Exp type can do which shallow
embeddings can't. It is an implementation of named variables with strings for
variable names, rather than DeBruin indices. It still uses DeBruin indices
under the hood, but allows for a "macro" (implemented with dependent type magic)
which lets the programmer input a string. It searches the context for a variable
with that name, and returns it if it exists. Otherwise, it causes a type error.

-}

open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Data.Sum hiding (map)
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.String
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Maybe

a : Bool
a = ⌊ "yes" ≟ "no" ⌋

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
mutual
  data Context : Set j where
    ∅ : Context
    cons : (ctx : Context) → String → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (cons ctx name h) = Σ (ctxType ctx) (λ t → h t)

  data InCtx : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    same : ∀{Γ T name} → InCtx (cons Γ name T) (λ γ → T (proj₁ γ))
    next : ∀{Γ T A name} → InCtx Γ A → InCtx (cons Γ name T) (λ γ → A (proj₁ γ))

  proj : ∀{Γ T} → (icx : InCtx Γ T) → (γ : ctxType Γ) → T γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

mutual
  data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i}
      → (name : String)
      → {B : ctxType (cons Γ name A) → Set i} →
      Exp (cons Γ name A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Var : ∀{Γ T} → (icx : InCtx Γ T)
      → Exp Γ T
    App : ∀{name} → {Γ : Context} → {A : ctxType Γ → Set i}
        → {B : ctxType (cons Γ name A) → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
    Π₀ : {Γ : Context} → (name : String) → (A : Exp Γ (λ _ → Set))
      → (B : Exp (cons Γ name (λ γ → unq γ A)) (λ _ → Set))
      → Exp Γ (λ _ → Set)
    Π₁ : {Γ : Context} → (name : String) → (A : Exp Γ (λ _ → Set₁))
      → (B : Exp (cons Γ name (λ γ → unq γ A)) (λ _ → Set₁))
      → Exp Γ (λ _ → Set₁)
    Cumu₀ : ∀{Γ} → Exp Γ (λ _ → Set) → Exp Γ (λ _ → Set₁)
    𝓤₀ : ∀{Γ} → Exp Γ (λ _ → Set₁)
    ⋆ : ∀{Γ} → Exp Γ (λ _ → ⊤)

  -- unquote
  unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda name e) = λ x → unq (γ , x) e
  unq γ (Var icx) = proj icx γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ name A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₁ name A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set
  unq γ (Cumu₀ T) = unq γ T
  unq γ ⋆ = tt

weakenType1 : {A : Set j} → {B : A → Set i} → (A → Set i) → ((Σ A B) → Set i)
weakenType1 f (a , b) = f a

findVar : (Γ : Context) → String → Maybe (ctxType Γ → Set i)
findVar ∅ name = nothing
findVar (cons Γ name' T) name
  = if ⌊ name' ≟ name ⌋
    then just (weakenType1 T)
    else map weakenType1 (findVar Γ name)

resultType : (Γ : Context) → String → Set j
resultType Γ name with findVar Γ name
... | nothing = ⊤
... | just T = Exp Γ T

var : ∀{Γ} → (name : String) → resultType Γ name
var {Γ} name = {!   !}

example : Exp ∅ (λ _ → (X : Set) → X → X)
example = Lambda "X" (Lambda "x" (var {cons (cons ∅ "X" (λ _ → Set)) "x" proj₂} "x"))

test1 : resultType (cons ∅ "x" (λ _ → Set)) "x" ≡ Exp (cons ∅ "x" (λ _ → Set)) (λ _ → Set)
test1 = refl

{-

PROBLEM: It can't infer what Γ is because it has to unify with some nonsense.
Absolute janky solution: Instead, make so var always returns Exp Γ something,
where something depends on resultType.
But if not in context, just returns Exp Γ Unit  or something stupid.
-}

findVar' : (Γ : Context) → String → Maybe (Σ {j} {j} (ctxType Γ → Set i) (λ T → InCtx Γ T))
findVar' ∅ name = nothing
findVar' (cons Γ name' T) name
  = if ⌊ name' ≟ name ⌋
    then just (_,_ {j} {j} (weakenType1 T) same)
    else map ((λ (T , icx) → (weakenType1 T , next icx))) (findVar' Γ name)

resultType' : (Γ : Context) → String → (ctxType Γ → Set i)
resultType' Γ name with findVar' Γ name
... | nothing = λ _ → ⊤
... | just (X , icx) = X

var' : ∀{Γ} → (name : String) → Exp Γ (resultType' Γ name)
var' {Γ} name with findVar' Γ name
... | nothing = ⋆
... | just (T , x) = Var x

example2 : Exp ∅ (λ _ → (X : Set) → X → X)
example2 = Lambda "X" (Lambda "x" (var' "x"))

-- Λ "X" - Λ "x" - var "x"

-- Λ
-- λ X . λ x . x

example3 : Exp ∅ (λ _ → Set₁)
example3 = Π₁ "X" 𝓤₀ (Cumu₀ (Π₀ "_" (var' "X") (var' "X")) )
