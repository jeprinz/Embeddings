{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --without-K #-}

{-

FILE DESCRIPTION:

There is a known way to derive parametricity from a shallow embedding. It works
by making a shallow DSL where the programmer writes types and terms, just like
any DSL. However, when the programmer writes a type, this really maps to the
free therorem for that type. And when the programmer writes a term, it really
maps to the proof of the free theorem for that term. In this way, shallow
embeddings allow one to define maps on types and termswhich can't be defined
as functions.

In this file, I am aiming to use a similar strategy to implement NbE. There will
be a standard Exp type. Then, I will write a second Exp type which effectively
creates semantic domain objects, which are normalized to terms of the first
Exp type. This could all be done with standard shallow embeddings, but the idea
of normalization for a shallow embedding doesn't really make sense; the terms
are immediately reduced to Agda values anyway!



CURRENT PLAN:

Each term of Exp2 will be parametrized by it's sem type and value. However, we
need to be able to get Exps out of them. So we need to do either reification
somehow, or something like unquote-n. In that case, we would parametrize by
the arguments, so that each term always is reified the exact necessary amount.

-}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Bool

module exp-param-by-exp where

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
k = lsuc j -- type level 1+i

mutual
  data Context : Set i → Set j where
    ∅ : Context ⊤
    _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ {i} {i} aΓ T)

  data InCtx : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j where
    same : ∀{aΓ T} → {Γ : Context aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ))
    next : ∀{aΓ Γ T A} → InCtx {aΓ} Γ A → InCtx (Γ , T) (λ γ → A (proj₁ γ))

  proj : ∀{aΓ} → {Γ : Context aΓ} → ∀{T} → (icx : InCtx Γ T)
    → (γ : aΓ) → T γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

mutual
  data Exp : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j where
    Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Var : ∀{aΓ Γ T} → (icx : InCtx Γ T) → Exp {aΓ} Γ T
    App : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
    Π₀ : ∀{aΓ} → {Γ : Context aΓ} → (A : Exp Γ (λ _ → Set))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ _ → Set))
      → Exp Γ (λ _ → Set)
    𝓤₀ : ∀{aΓ Γ} → Exp {aΓ} Γ (λ _ → Set₁)
    ⋆ : ∀{aΓ Γ} → Exp {aΓ} Γ (λ _ → ⊤)

  -- unquote
  unq : ∀{aΓ} → {Γ : Context aΓ} → (γ : aΓ) → {T : aΓ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Var icx) = proj icx γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set
  unq γ ⋆ = tt

aRen : Set i → Set i → Set i
aRen aΓ₁ aΓ₂ = aΓ₂ → aΓ₁

Ren : {aΓ₁ aΓ₂ : Set i} → aRen aΓ₁ aΓ₂ → Context aΓ₁ → Context aΓ₂ → Set j
Ren aren Γ₁ Γ₂ = ∀{T} → InCtx Γ₁ T → InCtx Γ₂ (λ γ → T (aren γ))

idaRen : {aΓ : Set i} → aRen aΓ aΓ
idaRen γ = γ

idRen : {aΓ : Set i} → {Γ : Context aΓ} → Ren idaRen Γ Γ
idRen x = x

weaken1aRen : {aΓ₁ aΓ₂ : Set i} → {T : aΓ₁ → Set i} → (aren : aRen aΓ₁ aΓ₂)
  → aRen (Σ {i} {i} aΓ₁ T) (Σ {i} {i} aΓ₂ (λ γ → T (aren γ)))
weaken1aRen ar (γ , t) = ar γ , t

weaken1Ren : {aΓ₁ aΓ₂ : Set i} → {T : aΓ₁ → Set i} → {Γ₁ : Context aΓ₁} → {Γ₂ : Context aΓ₂} → (aren : aRen aΓ₁ aΓ₂)
  → Ren aren Γ₁ Γ₂
  → Ren (weaken1aRen aren) (Γ₁ , T) (Γ₂ , (λ γ → T (aren γ)))
weaken1Ren ar r same = same
weaken1Ren ar r (next x) = next (r x)

mutual

  data Args : ∀{aΓ} → Context aΓ → Set j where
    none : ∀{aΓ Γ} → Args {aΓ} Γ
    one : ∀{aΓ Γ} → (ctx : Args {aΓ} Γ)
      → (T : (γ : aΓ) → Set i) → Args Γ

  -- PUExp : ∀{aΓ} → (Γ : Context aΓ) → (T : aΓ → Set i) → Args Γ T → Set j
  -- PUExp  Γ T none = Exp Γ T
  -- PUExp Γ T (one args A) = {! (GExp Γ A) → ?  !}

  -- APUExp : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j
  -- APUExp Γ T = (args : Args Γ T) → PUExp Γ T args

  -- GExp : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j
  -- GExp Γ T = ∀{aΓ' aren} → {Γ' : Context aΓ'} → Ren aren Γ Γ' → APUExp Γ' (λ γ → T (aren γ))

  -- IDEA: do something that wont work in general, but just to think with,
  -- will be able to do (λ x . x) ⋆ ↦ ⋆
  data Exp3 : (T : Set j) → T → Set k where
    ⋆ : ∀{aΓ Γ} → Exp3 (Exp {aΓ} Γ (λ _ → ⊤)) ⋆
    Var : ∀{aΓ Γ T} → (icx : InCtx {aΓ} Γ T)
      → Exp3 (Exp Γ T) (Var icx)
    -- so essentially just for simplicity, we assume that all Lambdas are applied. Doesn't work in general though.
    Lambda0 : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} →  ∀{a}
      → Exp3 (Exp (Γ , A) B) a
      → Exp3 (Exp Γ (λ γ → ((x : A γ) → B (γ , x)))) (Lambda a)
    Lambda1 : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} →  ∀{a}
      → Exp3 (Exp (Γ , A) B) a
      → Exp3 ((x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x) )) (λ x → {!   !} )
    -- App : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (γ : aΓ) → A γ → Set i} → ∀{a₁ a₂}
      -- → Exp3 (Exp Γ (λ γ → (a : A γ) → B γ a)) a₁ → (x : Exp3 (Exp Γ A) a₂)
      -- → Exp3 (Exp Γ  (λ γ → B γ (a₂ γ))) (λ γ → (a₁ γ) (a₂ γ))

example1 : Exp3 (Exp ∅ (λ _ → ⊤)) _
example1 = ⋆

-- example2 : Exp3 ∅ (λ _ → Exp ∅ (λ _ → ⊤)) _
-- example2 = App {! Exp3.Lambda (Exp3.Var same)  !} ⋆

module idEmbedding where
  data Exp2 : ∀{aΓ} → (Γ : Context aΓ) → (T : aΓ → Set i)
    → (Exp Γ T) → Set j where
    Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ aΓ A) → Set i} → ∀{a}
      → Exp2 (Γ , A) B a → Exp2 Γ (λ γ → ((x : A γ) → B (γ , x))) (Lambda a)
    Var : ∀{aΓ Γ T} → (icx : InCtx Γ T) → Exp2 {aΓ} Γ T (Var icx)
    App : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ aΓ A) → Set i} → ∀{a₁ a₂}
        → Exp2 Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Exp2 Γ A a₂) → Exp2 Γ (λ γ → B (γ , unq γ a₂)) (App a₁ a₂)
    ⋆ : ∀{aΓ Γ} → Exp2 {aΓ} Γ (λ _ → ⊤) ⋆

  extract : ∀{aΓ} → {Γ : Context aΓ} → {T : aΓ → Set i} → ∀{a} → Exp2 Γ T a → Exp Γ T
  extract {_} {_} {_} {a} e = a

  ex1 : Exp2 ∅ (λ _ → (X : Set) → X → X) _
  ex1 = Lambda (Lambda (Var same))

  check : (extract ex1) ≡ Lambda (Lambda (Var same))
  check = refl

module renEmbedding where
  data Exp2 : ∀{aΓ} → (Γ : Context aΓ) → (T : aΓ → Set i)
    → (∀{aΓ'} → {Γ' : Context aΓ'} → {aren : aRen aΓ aΓ'} → Ren aren Γ Γ' → Exp Γ' (λ γ → T (aren γ)))
    → Set j where
    Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → {a : {aΓ' : Set i} {Γ' : Context aΓ'} {aren : aRen (Σ {i} {i} aΓ A) aΓ'} → Ren aren (Γ , A) Γ' → Exp Γ' (λ γ → B (aren γ))}
      → Exp2 (Γ , A) B a → Exp2 Γ (λ γ → ((x : A γ) → B (γ , x))) (λ r → Lambda (a {! weaken1Ren  !} ) )
    -- Var : ∀{aΓ Γ T} → (icx : InCtx Γ T) → Exp2 {aΓ} Γ T (Var icx)
    -- App : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ aΓ A) → Set i} → ∀{a₁ a₂}
    --     → Exp2 Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Exp2 Γ A a₂) → Exp2 Γ (λ γ → B (γ , unq γ a₂)) (App a₁ a₂)
    ⋆ : ∀{aΓ Γ} → Exp2 {aΓ} Γ (λ _ → ⊤) (λ r → ⋆)

{-

TODO: fix lambda case, do var case.

THEN: is App case impossible? It might be because the unq has to work out...
if it is impossible, then probably this whole plan is nothing...

-}
