{-# OPTIONS --cumulativity #-}

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
open import Data.Maybe

{-

This file is effectively the same as "original-exp-but-with-ctx-as-unq.agda",
but it incorporates ALL of the modifications which I have deemed to be good.

1) Context is a datatype, allowing storage of metadata for e.g. named vars
2) Parametrized by values rather than having unq, allowing for substitution

-}

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

data Context : Set i → Set j where
  ∅ : Context ⊤
  _,_ : ∀{aΓ} → (ctx : Context aΓ) → (T : aΓ → Set i) → Context (Σ {i} {i} aΓ T)

data VarData : ∀{aΓ} → Context aΓ → Set where
  ∅ : VarData ∅
  _,_ : ∀{aΓ} → {Γ : Context aΓ} → {T : aΓ → Set i}
    → VarData Γ → Bool → VarData (Γ , T)

noneVars : ∀{aΓ} → (Γ : Context aΓ) → VarData Γ
noneVars ∅ = ∅
noneVars (Γ , T) = noneVars Γ , false

data Check : ∀{aΓ} → {Γ : Context aΓ}
  → VarData Γ → VarData Γ → VarData Γ → Set j where
  ∅ : Check ∅ ∅ ∅
  consLeft : ∀{aΓ} → {Γ : Context aΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ} → (T : aΓ → Set i)
    → Check Γ₁ Γ₂ Γ₃ → Check {_} {Γ , T} (Γ₁ , true) (Γ₂ , false) (Γ₃ , true)
  consRight : ∀{aΓ} → {Γ : Context aΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ} → (T : aΓ → Set i)
    → Check Γ₁ Γ₂ Γ₃ → Check {_} {Γ , T} (Γ₁ , false) (Γ₂ , true) (Γ₃ , true)
  consNeither : ∀{aΓ} → {Γ : Context aΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ} → (T : aΓ → Set i)
    → Check Γ₁ Γ₂ Γ₃ → Check {_} {Γ , T} (Γ₁ , false) (Γ₂ , false) (Γ₃ , false)

check : ∀{aΓ} → (Γ : Context aΓ) → (vd₁ vd₂ : VarData Γ)
  → Maybe (Σ {j} {j} (VarData Γ) (λ vd₃ → Check vd₁ vd₂ vd₃))
check _ ∅ ∅ = just (∅ , ∅)
check _ (vd₁ , x) (vd₂ , x₁) with check _ vd₁ vd₂
check (_ , _) (vd₁ , b₁) (vd₂ , b₂) | nothing = nothing
check (_ , _) (vd₁ , false) (vd₂ , false) | just (vd₃ , c) = just ((vd₃ , false) , consNeither _ c)
check (_ , _) (vd₁ , false) (vd₂ , true) | just (vd₃ , c) = just ((vd₃ , true) , consRight _ c)
check (_ , _) (vd₁ , true) (vd₂ , false) | just (vd₃ , c) = just ((vd₃ , true) , consLeft _ c)
check (_ , _) (vd₁ , true) (vd₂ , true) | just (vd₃ , c) = nothing
-- check .∅ ∅ ∅ = {!   !}
-- check .(_ , _) (vd₁ , false) (vd₂ , false) = {!   !}
-- check (Γ , _) (vd₁ , false) (vd₂ , true) with check Γ vd₁ vd₂
-- ... | nothing = nothing
-- ... | just (fst , snd) = {!   !}
--   -- = just ((vd₁ , true) , {! checkRight  !} )
-- check .(_ , _) (vd₁ , true) (vd₂ , false) = {!   !}
-- check .(_ , _) (vd₁ , true) (vd₂ , true) = {!   !}

-- data AInCtx : {aΓ : Set i} → (Γ : AContext aΓ) → (T : aΓ → Set i)
--   → ((γ : aΓ) → T γ) → Set j where
--   same : ∀{aΓ T b} → {Γ : AContext aΓ} → AInCtx (cons Γ b T) (λ γ → T (proj₁ γ)) proj₂
--   next : ∀{aΓ Γ T A a b} → AInCtx {aΓ} Γ A a → AInCtx (cons Γ b T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

data InCtx : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
  → ((γ : aΓ) → T γ) → Set j where
  same : ∀{aΓ T} → {Γ : Context aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ)) proj₂
  next : ∀{aΓ Γ T A a} → InCtx {aΓ} Γ A a → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

oneVars : ∀{aΓ T t} → (Γ : Context aΓ) → InCtx Γ T t → VarData Γ
oneVars .(_ , _) same = noneVars _ , true
oneVars .(_ , _) (next x) = oneVars _ x , false

data LExp : {aΓ : Set i} → (Γ : Context aΓ) → VarData Γ → (T : aΓ → Set i)
  → ((γ : aΓ) → T γ) → Set j where
  Lambda : ∀{aΓ} → {Γ : Context aΓ} → {vd : VarData Γ}
    → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a}
    → LExp (Γ , A) (vd , true) B a → LExp Γ vd (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
  Var : {aΓ : Set i} → {Γ : Context aΓ}
    → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
    → (icx : InCtx Γ T a) → LExp {aΓ} Γ (oneVars Γ icx) T a
  App : {aΓ : Set i} → {Γ : Context aΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ} → {A : aΓ → Set i}
      → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
      → LExp Γ Γ₁ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : LExp Γ Γ₂ A a₂)
      → Check Γ₁ Γ₂ Γ₃
      → LExp Γ Γ₃ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))
  Π₀ : {b : Bool} → {aΓ : Set i} → {Γ : Context aΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ}
    → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
    → (A : LExp Γ Γ₁ (λ _ → Set) a₁)
    → (B : LExp (Γ , a₁) (Γ₂ , b) (λ _ → Set) a₂)
    → Check Γ₁ Γ₂ Γ₃
    → LExp Γ Γ₃ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
  𝓤₀ : {aΓ : Set i} → {Γ : Context aΓ} → LExp {aΓ} Γ (noneVars _) (λ _ → Set₁) (λ _ → Set₀)

data Exp : {aΓ : Set i} → (Γ : Context aΓ) → (T : aΓ → Set i)
  → ((γ : aΓ) → T γ) → Set j where
  Lambda : ∀{aΓ} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a}
    → Exp (Γ , A) B a → Exp Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
  Var : {aΓ : Set i} → {Γ : Context aΓ} → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
    → (icx : InCtx Γ T a) → Exp {aΓ} Γ T a
  App : {aΓ : Set i} → {Γ : Context aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
      → Exp Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Exp Γ A a₂)
      → Exp Γ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))
  Π₀ : {aΓ : Set i} → {Γ : Context aΓ} → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
    → (A : Exp Γ (λ _ → Set) a₁)
    → (B : Exp (Γ , (λ γ → a₁ γ)) (λ _ → Set) a₂)
    → Exp Γ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
  𝓤₀ : {aΓ : Set i} → {Γ : Context aΓ} → Exp {aΓ} Γ (λ _ → Set₁) (λ _ → Set₀)

mutual
  checkLinear : ∀{aΓ Γ T t} → Exp {aΓ} Γ T t
    → Maybe (Σ {j} {j} (VarData Γ) (λ vd → LExp {aΓ} Γ vd T t))
  checkLinear (Lambda e) with checkLinear e
  ... | nothing = nothing
  ... | just ((vd , false) , Ae) = nothing
  ... | just ((vd , true) , Ae) = just (vd , Lambda Ae)
  checkLinear (Var icx) = just (oneVars _ icx , Var icx)
  checkLinear (App e₁ e₂) with checkLinear e₁ | checkLinear e₂
  ... | nothing | res2 = nothing
  ... | just x | nothing = nothing
  ... | just (vd₁ , Ae₁) | just (vd₂ , Ae₂) with check _ vd₁ vd₂
  ... | nothing = nothing
  ... | just (vd₃ , c) = just (vd₃ , App Ae₁ Ae₂ c)
  checkLinear (Π₀ e₁ e₂) = {!   !}
  checkLinear 𝓤₀ = just (noneVars _ ,  𝓤₀)


-- Example:

ex1 : LExp ∅ ∅ (λ _ → (Set → Set)) _
ex1 = Lambda (Var same)

ex1' : Exp ∅ (λ _ → (Set → Set)) _
ex1' = Lambda (Var same)

test1 : checkLinear ex1' ≡ just (_ , ex1)
test1 = refl

ex2 : Exp ∅ (λ _ → (X : Set) → X → X) _
ex2 = Lambda (Lambda (Var same))

test2 : checkLinear ex2 ≡ nothing
test2 = refl
