{-# OPTIONS --cumulativity --without-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Maybe

module termExp where

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

Σi = Σ {i} {i}

mutual -- Γ ⊢ e : T    corresponds to     e : Exp Γ T
  data Exp : (Γ : Set i) → (T : Γ → Set i) → ((γ : Γ) → T γ) → Set j where
    Lambda : {Γ : Set i} → {A : Γ → Set i} → {B : Σi Γ A → Set i} → ∀{x}
      → Exp (Σ {i} {i} Γ A) B x → Exp Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ → λ a → x (γ , a))
    -- Π₀ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₀))
    --   → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₀))
    --   → Exp Γ (λ γ → Set₀)
    -- Π₁ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₁))
    --   → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₁))
    --   → Exp Γ (λ γ → Set₁)
    -- 𝓤₀ : {Γ : Set i} → Exp Γ (λ γ → Set₁)
    -- 𝓤₁ : {Γ : Set i} → Exp Γ (λ γ → Set₂)
    -- Cumulativity : ∀{Γ} → Exp Γ (λ _ → Set₀) → Exp Γ (λ _ → Set₁)
    App : {Γ : Set i} → {A : Γ → Set i} → {B : Σi Γ A → Set i} → ∀{x₁ x₂}
        → Exp Γ (λ γ → (a : A γ) → B (γ , a)) x₁ → (x : Exp Γ A x₂)
        → Exp Γ (λ γ → B (γ , x₂ γ)) λ γ → (x₁ γ) (x₂ γ)
    Weaken : {Γ : Set i} → {A B : Γ → Set i} → ∀ {x}
      → Exp Γ B x → Exp (Σ Γ A) (λ γ → B (proj₁ γ)) λ γ → x (proj₁ γ)
    EndCtx : {Γ : Set i} → {A : Γ → Set i}
      → Exp (Σ Γ A) (λ γ → A (proj₁ γ)) proj₂
    constℕ : {Γ : Set i} → (n : ℕ) → Exp Γ (λ _ → ℕ) (λ _ → n)
    plus : {Γ : Set i} → Exp Γ (λ _ → ℕ → ℕ → ℕ) (λ _ → _+_)

-- TODO: replace x's above with t

consistent : ∀{b} → ¬ (Exp ⊤ (λ _ → ⊥) b)
consistent {b} e = b tt

idMap : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
idMap (Lambda e) = Lambda (idMap e)
idMap (App e₁ e₂) = App (idMap e₁) (idMap e₂)
idMap (Weaken e) = Weaken (idMap e)
idMap EndCtx = EndCtx
idMap (constℕ n) = constℕ n
idMap plus = plus

-- slaps a (λ x . x) in front of every subterm
stupidTransform : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
stupidTransform (Lambda e) = Lambda (App (Lambda EndCtx) e)
stupidTransform (App e₁ e₂) = App (App (Lambda EndCtx) e₁) (App (Lambda EndCtx) e₂)
stupidTransform (Weaken e) = Weaken (App (Lambda EndCtx) e)
stupidTransform EndCtx = EndCtx
stupidTransform (constℕ n) = constℕ n
stupidTransform plus = plus

f : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
f (Lambda e) = {! e  !}
f (App e₁ e₂) = {! e₁  !}
f (Weaken e) = {!  e !}
f EndCtx = {!   !}
f (constℕ n) = {!   !}
f plus = {!   !}


module newAttempt where
  data InfoA (A : Set i) (Γ : Set i) (T : Γ → Set i) (t : (γ : Γ) → T γ) : Set j where
    info : (p : T ≡ λ _ → A) → (n : A)
      → (subst (λ f → (γ : Γ) → f γ) p t ≡ (λ _ → n ))
      → InfoA A Γ T t

  _⊎j_ = _⊎_ {j} {j}

  appCase : ∀{Γ T₁ T₂ t₁ t₂}
    → ((InfoA ℕ Γ T₁ t₁) ⊎j ((InfoA (ℕ → ℕ) Γ T₁ t₁) ⊎j (InfoA (ℕ → ℕ → ℕ) Γ T₁ t₁)))
    → ((InfoA ℕ Γ T₂ t₂) ⊎j ((InfoA (ℕ → ℕ) Γ T₂ t₂) ⊎j (InfoA (ℕ → ℕ → ℕ) Γ T₂ t₂)))
    -- → Maybe ((InfoA ℕ Γ T t) ⊎j ((InfoA (ℕ → ℕ) Γ T t) ⊎j (InfoA (ℕ → ℕ → ℕ) Γ T t)))
    → Maybe ℕ
  appCase (inj₁ i₁) i₂ = nothing -- can't apply ℕ to anything
  appCase (inj₂ (inj₁ (info refl f refl))) (inj₁ (info refl n refl)) = just {!   !}
  appCase (inj₂ (inj₁ i₁)) (inj₂ y) = nothing -- can't apply (ℕ → ℕ) to (ℕ → ℕ) or (ℕ → ℕ → ℕ)
  appCase (inj₂ (inj₂ (info refl f refl))) (inj₁ (info refl g refl)) = just {!   !}
  appCase (inj₂ (inj₂ i₁)) (inj₂ i₂) = nothing -- can't apply (ℕ → ℕ → ℕ) to (ℕ → ℕ) or (ℕ → ℕ → ℕ)

  constElimImpl : ∀{Γ T t} → Exp Γ T t
    → (Exp Γ T t) × Maybe {j} ((InfoA ℕ Γ T t) ⊎j ((InfoA (ℕ → ℕ) Γ T t) ⊎j (InfoA (ℕ → ℕ → ℕ) Γ T t)))
  constElimImpl (Lambda e) with constElimImpl e
  ... | e' , i = Lambda e' , nothing
  constElimImpl (App e₁ e₂) with constElimImpl e₁ | constElimImpl e₂
  ... | e₁' , just i₁ | e₂' , just i₂ = App e₁' e₂' , just {!   !}
  ... | e₁' , _ | e₂' , _ = App e₁' e₂' , nothing
    -- IDEA: just remove T from InfoA type? but then..... constElim (notImpl)...
  constElimImpl (Weaken e) with constElimImpl e
  ... | e' , nothing = Weaken e' , nothing
  ... | e' , just (inj₁ (info refl n refl)) = Weaken e' , just (inj₁ (info refl n refl))
  ... | e' , just (inj₂ x) = {!   !}
  constElimImpl EndCtx = EndCtx , nothing
  constElimImpl (constℕ n) = constℕ n , just (inj₁ (info refl n refl))
  constElimImpl plus = plus , just (inj₂ (inj₂ (info refl _+_ refl)))

  constElim : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
  constElim e with constElimImpl e
  ... | e' , nothing = e'
  ... | e' , just (inj₁ (info refl n refl)) = constℕ n
  ... | e' , just (inj₂ (inj₁ (info p n x))) = e'
  ... | e' , just (inj₂ (inj₂ y)) = e'

module longAttempt where

  data Info (Γ : Set i) (T : Γ → Set i) (t : (γ : Γ) → T γ) : Set j where
    info : (p : T ≡ λ _ → ℕ) → (n : ℕ) → (subst (λ f → (γ : Γ) → f γ) p t ≡ (λ _ → n )) → Info Γ T t

  data InfoA (A : Set i) (Γ : Set i) (T : Γ → Set i) (t : (γ : Γ) → T γ) : Set j where
    info : (p : T ≡ λ _ → A) → (n : A)
      → (subst (λ f → (γ : Γ) → f γ) p t ≡ (λ _ → n ))
      → Exp Γ T t
      → InfoA A Γ T t

  _⊎j_ = _⊎_ {j} {j}

  constElimImpl : ∀{Γ T t} → Exp Γ T t
    → (Exp Γ T t) ⊎j ((InfoA ℕ Γ T t) ⊎j ((InfoA (ℕ → ℕ) Γ T t) ⊎j (InfoA (ℕ → ℕ → ℕ) Γ T t)))
  constElimImpl (Lambda e) with constElimImpl e
  ... | inj₁ e' = inj₁ (Lambda e')
  ... | inj₂ (inj₁ (info refl n refl e₁)) = inj₁ (Lambda (constℕ n))
  ... | inj₂ (inj₂ (inj₁ (info refl f refl e₁))) = inj₁ (Lambda e₁)
  ... | inj₂ (inj₂ (inj₂ (info refl f refl e₁))) = inj₁ (Lambda e₁)
  constElimImpl (App e₁ e₂) with constElimImpl e₁ | constElimImpl e₂
  ... | inj₁ e₁' | inj₁ e₂' = inj₁ (App e₁' e₂')
  ... | inj₁ e₁' | inj₂ (inj₁ (info refl n refl e₂')) = inj₁ (App e₁' e₂')
  ... | inj₁ e₁' | inj₂ (inj₂ (inj₁ (info refl n refl e₂'))) = inj₁ (App e₁' e₂')
  ... | inj₁ e₁' | inj₂ (inj₂ (inj₂ (info refl n refl e₂'))) = inj₁ (App e₁ e₂')
  ... | inj₂ (inj₁ (info p n x e₁')) | inj₁ e₂' = inj₁ (App e₁' e₂') -- this (and many other) case can never happen but whatever.
  ... | inj₂ (inj₁ (info p n x e₁')) | inj₂ (inj₁ (info p₁ n₁ x₁ e₂')) = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₁ (info p n x e₁')) | inj₂ (inj₂ (inj₁ (info p₁ n₁ x₁ e₂'))) = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₁ (info p n x e₁')) | inj₂ (inj₂ (inj₂ (info refl n₁ refl e₂'))) = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₂ (inj₁ (info p n x e₁'))) | inj₁ e₂' = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₂ (inj₁ (info p f x e₁'))) | inj₂ (inj₁ (info refl n p₃ e₂'))
  -- ℕ → ℕ     applied to     ℕ    case
    = inj₂ (inj₁ (info {! p  !} (f n) {! x  !} (App e₁' e₂')))
  ... | inj₂ (inj₂ (inj₁ (info p n x e₁'))) | inj₂ (inj₂ (inj₁ (info refl n₁ refl e₂'))) = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₂ (inj₁ (info p n x e₁'))) | inj₂ (inj₂ (inj₂ (info p₁ n₁ x₂ e₂'))) = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₂ (inj₂ (info p n x e₁'))) | inj₁ e₂' = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₂ (inj₂ (info p f x₁ e₁'))) | inj₂ (inj₁ (info refl g refl e₂'))
  -- ℕ → ℕ → ℕ     applied to     ℕ    case
    = inj₂ (inj₂ (inj₁ (info {!   !} (f g) {!   !} (App e₁' e₂'))))
  ... | inj₂ (inj₂ (inj₂ (info p f p₁ e₁'))) | inj₂ (inj₂ (inj₁ (info refl g refl e₂'))) = inj₁ (App e₁' e₂')
  ... | inj₂ (inj₂ (inj₂ (info p f p₁ e₁'))) | inj₂ (inj₂ (inj₂ (info refl n refl e₂'))) = inj₁ (App e₁' e₂')
  constElimImpl (Weaken e) = {!   !}
  constElimImpl EndCtx = {!   !}
  constElimImpl (constℕ n) = inj₂ (inj₁ (info refl n refl (constℕ n)))
  constElimImpl plus = inj₂ (inj₂ (inj₂ (info refl _+_ refl plus)))

-- TODO: is it possible to implement substitution?

{-
constElim : ∀{Γ T t} → Exp Γ T t → (Exp Γ T t) ⊎ (Info Γ T t)
constElim (Lambda e) with constElim e
... | inj₁ e' = inj₁ (Lambda e')
... | inj₂ (info refl n refl) = inj₁ (Lambda (constℕ n))
constElim (App e₁ e₂) = {!   !}
constElim (Weaken e) = {!   !}
constElim EndCtx = {!   !}
constElim (constℕ n) = inj₂ (info refl n refl)
constElim plus = {!   !}

constElimFinal : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
constElimFinal e with constElim e
... | inj₁ x = x
... | inj₂ (info refl n refl) = constℕ n
-}

-- Sadly, doesn't work:
-- plusElim : ∀{Γ T t} → Exp Γ T t → Exp Γ T t
-- plusElim (Lambda e) = {!   !}
-- plusElim (App e₁ e₂) = {!   !}
-- plusElim (Weaken e) = {!   !}
-- plusElim EndCtx = {!   !}
-- plusElim (App (App plus (constℕ n)) (constℕ m)) = ?
-- plusElim (constℕ n) = {!   !}
-- plusElim plus = {!   !}

unqStupid : ∀{Γ T t} → Exp Γ T t → (γ : Γ) → T γ
unqStupid {Γ} {T} {t} e = t

-- mutual
--   unq : ∀{Γ T t} → Exp Γ T t → (γ : Γ) → T γ
--   unq (Lambda e) γ = λ a → unq e (γ , a)
--   unq (App e₁ e₂) γ = {! (unq e₁ γ) (unq e₂ γ)  !}
--   unq (Weaken e) γ = {!   !}
--   unq EndCtx γ = {!   !}
--
--   unq≡ : ∀{Γ T t} → (e : Exp Γ T t) → t ≡ (unq e)
--   unq≡ e = {!   !} -- won't be able to do without function extentionality
