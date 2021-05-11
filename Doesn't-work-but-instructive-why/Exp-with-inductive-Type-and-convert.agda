{-# OPTIONS --cumulativity --without-K #-}

{-

The goal of this file was to solve the issue with the Exp type that it's not really
possible to do pattern mathching on Exp for anything useful. I accomplished this
by storing not only an Agda type, but also having an inductive Type. This helps
the pattern matching. I then have a convert constructor which lets you convert
between types that represent the same agda type. Predictably, this just pushes
the same old problems one step further. In the end, it is technically possible
to do a little bit more with this one, like define an optimization which
does (λ x . x) e → e. However, not much more is possible. For example, it is not
possible to do (λ x y . x) e₁ e₂ → e₁.  I think that the idea in this file is
not good and should never be spoken of again.

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
open import Data.Maybe


{-
TODO: in the spirit of Exp → TermExp, probably ctxType should be removed and
replaced with a parameter of Context. Although, there doesn't seem to be
any problem with how it is now.
Update: I have found the problem! it needed to convert terms between contexts.
-}

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
mutual
  data Context : Set j where
    ∅ : Context
    _,_ : (Γ : Context) → {at : ctxType Γ → Set i}
      → Type Γ at → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (_,_ Γ {aT} T) =  Σ (ctxType Γ) (λ γ → aT γ) -- Σ (ctxType Γ) (λ t → h t)

  data Type : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    U₀ : ∀{Γ} → Type Γ (λ _ → Set₀)
    U₁ : ∀{Γ} → Type Γ (λ _ → Set₁)
    Π : ∀{Γ aA aB} → (A : Type Γ aA) → (B : Type (Γ , A) aB)
      → Type Γ (λ γ → (a : aA γ) → aB (γ , a))
    fromExp : ∀{Γ a} → Exp Γ U₀ a → Type Γ a
    tsub : ∀{Γ aA at aa} → {A : Type Γ aA} → Type (Γ , A) at → Exp Γ A aa
      → Type Γ (λ γ → at (γ , aa γ))
    Weaken : ∀{Γ aA aT} → {A : Type Γ aA} → Type Γ aT → Type (Γ , A) (λ γ → aT (proj₁ γ))

  data Exp : (Γ : Context) → ∀{aT} → (T : Type Γ aT) → ((γ : ctxType Γ) → aT γ) → Set j where
    Lambda : ∀{Γ aA aB} → {A : Type Γ aA} → {B : Type (Γ , A) aB} → ∀{ae}
      → Exp (Γ , A) B ae → Exp Γ (Π A B) (λ γ → λ a → ae (γ , a))
    App : ∀{Γ aA aB} → {A : Type Γ aA} → {B : Type (Γ , A) aB} → ∀{af aa}
      → (f : Exp Γ (Π A B) af) → (a : Exp Γ A aa)
      → Exp Γ (tsub B a) (λ γ → af γ (aa γ))
    convert : ∀{Γ aT a} → {A B : Type Γ aT}
      → Exp Γ A a → Exp Γ B a
      -- NOTE: the fact that it only has Set, while Type has Set i, means we can't
      -- pattern match on the type inside this.
      -- The (annoying) solution would be to make Type₀, Type₁, ...
      -- Maybe Type can be parametrized by a level or something?
    fromT₀ : ∀{Γ} → {a : (ctxType Γ) → Set} → Type Γ a → Exp Γ U₀ a
    Var : ∀{Γ aT} → {T : Type Γ aT} → (icx : InCtx Γ T)
      → Exp Γ T (proja icx)

  data InCtx : (Γ : Context) → {aT : ctxType Γ → Set i}
    → Type Γ aT → Set j where
    same : ∀{Γ aT} → {T : Type Γ aT} → InCtx (Γ , T) (Weaken T)
    next : ∀{Γ aT aA} → {T : Type Γ aT} → {A : Type Γ aA}
      → InCtx Γ A → InCtx (Γ , T) (Weaken A)

  proja : ∀{Γ aT} → {T : Type Γ aT} → (icx : InCtx Γ T) → (γ : ctxType Γ) → aT γ
  proja same (γ , t) = t
  proja (next icx) (γ , _) = proja icx γ

unq : ∀{Γ aT T a} → Exp Γ {aT} T a → (γ : ctxType Γ) → aT γ
unq {_} {_} {_} {a} e = a

test1 : ∀{Γ aT a} → (T : Type Γ aT) → Exp Γ {aT} T a → ℕ
test1 U₀ (convert e) = {!   !}
test1 U₀ (fromT₀ x) = {!   !}
test1 U₁ (convert e) = {!   !}
test1 (Π T₁ T₂) (Lambda e) = {!   !}
test1 (Π T₁ T₂) (convert e) = {!   !}
test1 (fromExp x) (convert e) = {!   !}
test1 (tsub T₁ x) (App e .x) = {!   !}
test1 (tsub T₁ x) (convert e) = {!   !}
test1 (Weaken T₁) (convert e) = {!   !}
test1 (Weaken T₁) (Var icx) = {!   !}

-- Exp ⊥ → ⊥
-- ¬ (Exp ⊥)

consistency : ∀{a} → Exp ∅ (Π U₀ (fromExp (convert (Var same)))) a → ⊥
consistency {a} e = a tt ⊥

  -- proj : ∀{Γ aT} → {T : Type Γ aT} → (icx : InCtx Γ T) → Exp Γ T (proja icx)
  -- proj {(Γ , _)} same = {!   !}
  -- proj {.(_ , _)} (next icx) = {!   !}

test : ∀{Γ aT T t} → Exp Γ {aT} T t → ℕ
test (Lambda (Lambda e)) = 5
test (Lambda (App (Var x) e₁)) = {!   !}
test (Lambda (App (Lambda e) e₁)) = {!   !}
test (Lambda (App (convert e) e₁)) = {!   !}
test (Lambda (convert e)) = 8
test (Lambda (fromT₀ x)) = 0
test (Lambda (Var icx)) = 0
test (App e₁ e₂) = 1
test (convert e) = 0
test (fromT₀ T) = 0
test (Var x) = 0

test2 : ∀{Γ aA aB t} → {A : Type Γ aA} → {B : Type (Γ , A) aB}
  → Exp Γ (Π A B) t → ℕ
-- TODO TODO: why doesn't it see Var as an option?
test2 (Lambda e) = {!   !}
test2 (convert {_} {_} {_} {T₁} {T₂} e) = {! T₁  !}
-- The fact that we can't case split T₁ in the above hole represents the following
-- limitation of this encoding:
-- Although we can induct on terms, we can't in general induct on the types of terms.
-- This shows up in the convert constructor.

limitation : ∀{Γ aT a} → (T : Type Γ aT) → Exp Γ T a → ℕ
limitation T e = {! T  !}


-- The following is equivalent to
-- (λ X x . x)   :   (X : Set) → X → X
example : Exp ∅ (Π U₀ (Π (fromExp (convert (Var same))) (fromExp (convert (Var (next same)))))) _
example = Lambda (Lambda (convert (Var same)))

-- although it is annoying to put converts everywhere, Agda is able to infer everything.
-- I could conceivable define something like
-- var x = convert (Var x)
-- app e₁ e₂ = convert (App e₁ e₂)

{-
NOTE: there would not need to be converts in "example" above if Weaken was implemented as as FUNCTION,
rather than a constructor. I should look into if this is possible to do.
-}

vSub : (Γ₁ Γ₂ : Context) → Set j
vSub Γ₁ Γ₂ = ctxType Γ₂ → ctxType Γ₁

liftvSub : ∀{Γ₁ Γ₂ aT} → {T : Type Γ₁ aT}
  -- → (vsub : vSub Γ₁ Γ₂) → vSub (Γ₁ , T) (Γ₂ , (λ γ → aT (vsub γ)))
  → (vsub : vSub Γ₁ Γ₂) → vSub (Γ₁ , T) (Γ₂ , {! T  !} )
liftvSub vsub (γ , t) = vsub γ , t

forget1vsub : ∀{Γ₁ Γ₂ aT} → {T : Type Γ₁ aT} → (vsub : vSub (Γ₁ , T) Γ₂) → vSub Γ₁ Γ₂
forget1vsub vsub γ = proj₁ (vsub γ)

TSub : (Γ₁ Γ₂ : Context) → vSub Γ₁ Γ₂ → Set j
TSub Γ₁ Γ₂ vsub = ∀{aT} → (x : InCtx Γ₁ U₀)
  → Type Γ₂ aT

-- Sub : (Γ₁ Γ₂ : Context) → vSub Γ₁ Γ₂ → Set j
-- Sub Γ₁ Γ₂ vsub = ∀{T} → (x : InCtx Γ₁ T) → Exp Γ₂ {!   !} {!   !}

-- Sub : (Γ₁ Γ₂ : Context) → vSub Γ₁ Γ₂ → Set j
-- Sub Γ₁ Γ₂ vsub = ∀{T} → (x : InCtx Γ₁ T)
  -- → Exp Γ₂ (λ γ → T (vsub γ)) (λ γ → proj x (vsub γ))

-- liftSub : ∀{Γ₁ Γ₂ T vsub} → Sub Γ₁ Γ₂ vsub → Sub (Γ₁ , T) (Γ₂ , (λ γ → T (vsub γ))) (liftvSub vsub)
-- liftSub sub same = Var same
-- liftSub sub (next x) = Weaken (sub x)

-- forget1Sub : ∀{Γ₁ Γ₂ T vsub} → Sub (Γ₁ , T) Γ₂ vsub → Sub Γ₁ Γ₂ (forget1vsub vsub)
-- forget1Sub sub x = sub (next x)

-- append1Sub : ∀{Γ T} → {t : (γ : ctxType Γ) → T γ}
--   → Exp Γ T t
--   → Sub (Γ , T) Γ (append1vsub t)
-- append1Sub e same = e
-- append1Sub e (next x) = Var x

-- (λ x y . x) a b → a

a = {! proj₂  !}

mutual
  exampleOptimization : ∀{Γ aT T t} → Exp Γ {aT} T t → Exp Γ T t
  exampleOptimization (Lambda e) = Lambda (exampleOptimization e)
  exampleOptimization (App (Lambda (Var same)) e) = convert (exampleOptimization e)
  exampleOptimization (App (convert e) e₃) = {! e  !}
  exampleOptimization (App e₁ e₂) = convert (App (exampleOptimization e₁) (exampleOptimization e₂))
  exampleOptimization (convert e) = convert (exampleOptimization e)
  exampleOptimization (fromT₀ x) = fromT₀ (exampleOptimizationT x)
  exampleOptimization (Var icx) = Var icx

  exampleOptimizationT : ∀{Γ aT} → Type Γ aT → Type Γ aT
  exampleOptimizationT U₀ = U₀
  exampleOptimizationT U₁ = U₁
   -- need something like convert, except for contexts, using ctxType.
   -- Maybe, Context should actually be parametrized by ctxType!!!!!!
  exampleOptimizationT (Π T₁ T₂) = {!   !}
  exampleOptimizationT (fromExp x) = fromExp (exampleOptimization x)
  exampleOptimizationT (tsub T x) = tsub (exampleOptimizationT T) (exampleOptimization x)
  exampleOptimizationT (Weaken T) = Weaken (exampleOptimizationT T)
-- exT : Type ∅ (λ _ → Set → Set)
exT : Type ∅ _         ---  NOTE that the agda type can be left off!!!! could be implicit!!!
exT = Π U₀ U₀

-- Note that none of the agda types and terms are necessary here, even in convert!!!
exE : Exp ∅ exT _
exE = Lambda (convert (App (Lambda (Var same)) (Var same)))


useOptimize : exampleOptimization exE ≡ Lambda (convert (convert (Var same)))
useOptimize = refl

{-

HMM: converts are kind of weird. Maybe it should be built separately into
each constructor, so that each constructor does conversion on its own?
Rename to cast?

-}

-- Idea: make substitution a function (which doesn't do any normalization after sub!
-- just a simple sub!) Then, use in App constructor. This would allow for multiple Apps
-- in pattern matching. Of course, it wouldn't allow everything, but enough to be
-- compelling hopefully.
