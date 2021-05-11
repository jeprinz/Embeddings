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

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
k = lsuc j -- type level 1+i

mutual
  data Context : Set i → Set j where
    ∅ : Context ⊤
    _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ aΓ T)

  data InCtx : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j where
    same : ∀{aΓ T} → {Γ : Context aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ))
    next : ∀{aΓ Γ T A} → InCtx {aΓ} Γ A → InCtx (Γ , T) (λ γ → A (proj₁ γ))

  proj : ∀{aΓ} → {Γ : Context aΓ} → ∀{T} → (icx : InCtx Γ T)
    → (γ : aΓ) → T γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

mutual
  data Exp : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j where
    Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ aΓ A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Var : ∀{aΓ Γ T} → (icx : InCtx Γ T) → Exp {aΓ} Γ T
    App : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ aΓ A) → Set i} →
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

mutual

  data Args : ∀{aΓ} → Context aΓ → (aΓ → Set i) → Set j where
    ∅ : ∀{aΓ Γ} → Args {aΓ} Γ (λ _ → ⊤)
    _,_ : ∀{aΓ Γ aargs} → (ctx : Args {aΓ} Γ aargs)
      → (T : (γ : aΓ) → aargs γ → Set i) → Args Γ (λ γ → Σ (aargs γ)  (T γ))

  -- data Exp2 : ∀{aΓ} → (Γ : Context aΓ) → (T : aΓ → Set j)
  --   → ((γ : aΓ) → T γ) → Set k where
  --   ⋆ : ∀{aΓ Γ} → Exp2 {aΓ} Γ (λ _ → Exp Γ (λ _ → ⊤)) (λ _ → ⋆)
  --   Var : ∀{aΓ Γ T} → (icx : InCtx {aΓ} Γ T)
  --     → Exp2 Γ T (proj icx)

  -- Essentially, Exp2 is supposed to be parametrized by (Sem Γ T)
  -- so the Sem type and its elements are built up at once.

  addArg : ∀{aΓ A aargs} → {Γ : Context aΓ} → Args (Γ , A) aargs
    → Args Γ (λ γ → Σ (A γ) (λ a → aargs (γ , a)))
  addArg {_} {A} ∅ = {! ∅ , A  !}
  addArg {_} {A} (args , T₁) = {!   !}

  data Exp2 : ∀{aΓ aargs} → (Γ : Context aΓ) → Args Γ aargs → (T : aΓ → Set j)
    → ((γ : aΓ) → T γ) → Set k where
    ⋆ : ∀{aΓ Γ} → Exp2 {aΓ} Γ ∅ (λ _ → Exp Γ (λ _ → ⊤)) (λ _ → ⋆)
    -- Var : ∀{aΓ Γ T} → (icx : InCtx {aΓ} Γ T)
      -- → Exp2 Γ T (proj icx)
    Lambda : ∀{aΓ A B a} → {Γ : Context aΓ} → ∀{aargs} → {args : Args (Γ , A) aargs}
      → Exp2 (Γ , A) args B a
      → let yeet = Args._,_ args λ γ b → A (proj₁ γ)
        in Exp2 Γ {! yeet  !} {!   !} {!   !}
