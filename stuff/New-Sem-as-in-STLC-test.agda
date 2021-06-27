{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

module New-Sem-as-in-STLC-test where

{-
mutual
  data SemT : Set where -- the X parameter reminds me of Semn and SemTn parameters in depthy!
    _⇒_ : SemT → SemT → SemT
    base : SemT

  Sem : SemT → Set
  Sem (A ⇒ B) = Sem A → Sem B
  Sem base = {!   !}
-}

{-
IDEA: Maybe semantics should be parametrized by Ctx and InCtx????
After all, Sem (from racket) needs to hold variables, and nothing else from Exp.

Except no, not just variables (well, maybe so in STLC, but not dep thy) it needs
to hold Ne's in general.
-}

-- really Exp is also parametrized by Type, but the SemT IS the type.
module semantics (Ctx : Set) (Exp : Ctx → Set) where
  Ren : Ctx → Ctx → Set
  Ren Γ₁ Γ₂ = Exp Γ₁ → Exp Γ₂

  data SemT : Set where
    _⇒_ : SemT → SemT → SemT
    base : SemT

  Sem : Ctx → SemT → Set
  GSem : Ctx → SemT → Set
  Sem Γ (A ⇒ B) = GSem Γ A → Sem Γ B
  Sem Γ base = Exp Γ -- Nf Γ base

  GSem Γ T = ∀{Γ'} → Ren Γ Γ' → Sem Γ' T

open semantics

mutual
  Type : Set
  base' : Type
  Type = SemT Ctx (λ Γ → Nf Γ base')
  base' = base

  data Ctx : Set where
    ∅ : Ctx
    _,_ : Ctx → Type → Ctx


  data InCtx : (Γ : Ctx) → Type → Set where
    same : ∀{Γ T} → InCtx (Γ , T) T
    next : ∀{Γ T A} → InCtx Γ A → InCtx (Γ , T) A

  data Ne : Ctx → Type → Set where
    var : ∀{Γ T} → (icx : InCtx Γ T) → Ne Γ T
    app : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

  data Nf : Ctx → Type → Set where
    lambda : ∀{Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    -- ne : ∀{Γ T} → Ne Γ T → Nf Γ T
    ne : ∀{Γ} → Ne Γ base → Nf Γ base -- the fact that its only base enforces expanded η form. The above version would also typecheck just fine though.
    ⋆ : ∀{Γ} → Nf Γ base

Sem' = Sem Ctx (λ Γ → Nf Γ base')
GSem' = GSem Ctx (λ Γ → Nf Γ base')

mutual
  nApp : ∀{Γ T} → Ne Γ T → Sem' Γ T
  nApp {Γ} {A ⇒ B} e = {!   !}
  nApp {Γ} {base} e = {!   !}
  -- nApp {_} {A ⇒ B} e = λ g → nApp {_} {B} (app e (reify g))
  -- nApp {_} {base} e = ne e

  -- I may have overcomplicated this definition?
  reify : ∀{Γ T} → GSem' Γ T → Nf Γ T
  reify {Γ} {A ⇒ B} g = lambda (reify {Γ , A} {B} λ ren → g {!   !}
    (λ ren₂ → nApp {! ren₂ (ren (ne (var same)))  !} ))
  reify {Γ} {base} g = g (λ x → x)
  -- reify {Γ} {A ⇒ B} g
  --   = lambda (reify {Γ , A} {B} (λ ren → g (forget1ren ren)
  --         (λ ren₂ → nApp {_} {A} (var (ren₂ (ren same))))))
  -- reify {_} {base} g = g idRen
