{-# OPTIONS --without-K #-}

open import Data.Unit
open import Data.Nat
open import Data.Product

{-

The question that I'm trying to answer in this file is what does the shallow
embedding here actually do? If I remove it, can I still define reify?

ANSWER - yes, apparently.
Next step: build full one-way-normalization, for typed and untyped version here.

-}

-------------------- Augmented "shallow" embedding -----------------------------
-- keep only context and level, no S.Type or S.Term.

data Context : Set₁ where
  ∅ : Context
  _,_ : (ctx : Context) → ℕ → Context

data Var : Context → ℕ → Set₁ where
  same : ∀{Γ n} → Var (Γ , n) n
  next : ∀{n Γ m} → Var Γ n → Var (Γ , m) n

data Exp : Context → ℕ → Set₁ where
  Elambda : ∀{Γ n} → Exp (Γ , n) n → Exp Γ n
  Evar : ∀{Γ n} → Var Γ n → Exp Γ n
  Eapp : ∀{Γ n} → Exp Γ n → Exp Γ n → Exp Γ n
  EΠ : ∀{Γ n} → Exp Γ n → Exp (Γ , n) n → Exp Γ n
  EU : ∀{Γ n} → Exp Γ (suc n)
  Ecumu : ∀{Γ n} → Exp Γ n → Exp Γ (suc n)
  EcumuValue : ∀{Γ n} → Exp Γ n → Exp Γ (suc n)

ERen : Context → Context → Set₁
ERen Γ₁ Γ₂ = ∀{n} → Var Γ₁ n → Var Γ₂ n

EidRen : ∀{Γ} → ERen Γ Γ
EidRen x = x

Eforget1ren : ∀{n} → {Γ₁ Γ₂ : Context}
  → ERen Γ₁ Γ₂ → ERen (Γ₁ , n) (Γ₂ , n)
Eforget1ren ren same = same
Eforget1ren ren (next x) = next (ren x)

Eweaken1Ren : ∀{Γ n} → ERen Γ (Γ , n)
Eweaken1Ren = next

renExp : ∀{n} → {Γ₁ Γ₂ : Context}
  → ERen Γ₁ Γ₂ → Exp Γ₁ n → Exp Γ₂ n
renExp ren (Elambda e) = Elambda (renExp (Eforget1ren ren) e)
renExp ren (Evar x) = Evar (ren x)
renExp ren (Eapp e₁ e₂) = Eapp (renExp ren e₁) (renExp ren e₂)
renExp ren (EΠ A B) = EΠ (renExp ren A) (renExp (Eforget1ren ren) B)
renExp ren EU = EU
renExp ren (Ecumu e) = Ecumu (renExp ren e)
renExp ren (EcumuValue e) = EcumuValue (renExp ren e)

ESub : Context → Context → Set₁
ESub Γ₁ Γ₂ = ∀{n} → Var Γ₁ n → Exp Γ₂ n

EidSub : ∀{Γ} → ESub Γ Γ
EidSub x = Evar x

Eforget1sub : ∀{n} → {Γ₁ Γ₂ : Context}
  → ESub Γ₁ Γ₂ → ESub (Γ₁ , n) (Γ₂ , n)
Eforget1sub sub same = Evar same
Eforget1sub sub (next x) = renExp Eweaken1Ren (sub x)


------------------- Normal form augmented "shallow" embedding ------------------

mutual
  data Ne : Context → ℕ → Set₁ where
    Evar : ∀{Γ n} → Var Γ n → Ne Γ n
    Eapp : ∀{Γ n} → Ne Γ n → Nf Γ n → Ne Γ n
    unCumu : ∀{n Γ} → Ne Γ (suc n) → Ne Γ n
    EcumuValue : ∀{Γ n} → Ne Γ n → Ne Γ (suc n)

  data Nf : Context → ℕ → Set₁ where
    Elambda : ∀{Γ n} → Nf (Γ , n) n → Nf Γ n
    EcumuValue : ∀{Γ n} → Nf Γ n → Nf Γ (suc n)
    fromNe : ∀{Γ n} → Ne Γ n → Nf Γ n
    fromType : ∀{Γ n} → EType Γ n → Nf Γ (suc n)

  data EType : Context → ℕ → Set₁ where
    EΠ : ∀{Γ n} → EType Γ n → EType (Γ , n) n → EType Γ n
    EU : ∀{Γ n} → EType Γ (suc n)
    Ecumu : ∀{Γ n} → EType Γ n → EType Γ (suc n)
    fromNe : ∀{Γ n} → Ne Γ (suc n) → EType Γ n

mutual
  renNe : ∀{n} → {Γ₁ Γ₂ : Context}
    → ERen Γ₁ Γ₂ → Ne Γ₁ n → Ne Γ₂ n
  renNe ren (Evar x) = Evar (ren x)
  renNe ren (Eapp e₁ e₂) = Eapp (renNe ren e₁) (renNf ren e₂)
  renNe ren (EcumuValue e) = EcumuValue (renNe ren e)
  renNe ren (unCumu e) = unCumu (renNe ren e)

  renNf : ∀{n} → {Γ₁ Γ₂ : Context}
    → ERen Γ₁ Γ₂ → Nf Γ₁ n → Nf Γ₂ n
  renNf ren (Elambda e) = Elambda (renNf (Eforget1ren ren) e)
  renNf ren (EcumuValue e) = EcumuValue (renNf ren e)
  renNf ren (fromNe e) = fromNe (renNe ren e)
  renNf ren (fromType T) = fromType (renEType ren T)

  renEType : ∀{n} → {Γ₁ Γ₂ : Context}
    → ERen Γ₁ Γ₂ → EType Γ₁ n → EType Γ₂ n
  renEType ren (EΠ A B) = EΠ (renEType ren A) (renEType (Eforget1ren ren) B)
  renEType ren EU = EU
  renEType ren (Ecumu e) = Ecumu (renEType ren e)
  renEType ren (fromNe e) = fromNe (renNe ren e)

------------------ Semantic domain, parametrized by shallow --------------------
data ESemTzero : Context → Set₁ where
    fromNe : ∀{Γ} → Ne Γ 1  → ESemTzero Γ
ESemzero : (Γ : Context) →  ESemTzero Γ → Set₁
ESemzero Γ (fromNe e) = Nf Γ 1 -- TODO: should be Ne? should be 1?

module Esucn (n : ℕ)
  (ESemTn : Context → Set₁)
  (ESemn : (Γ : Context) → ESemTn Γ → Set₁)
  where
  mutual
    data ESemTsucn : Context → Set₁ where
      EU : {Γ : Context} → ESemTsucn Γ
      fromNe : ∀{Γ} → Ne Γ (suc (suc n)) → ESemTsucn Γ -- why 2 sucs?
      Ecumu : {Γ : Context} → ESemTn Γ → ESemTsucn Γ
      EΠ : {Γ : Context}
        → (A : ∀{Γ'} → ERen Γ Γ' → ESemTsucn Γ')
        → (B : ∀{Γ'} → (eren : ERen Γ Γ')
            → ESemsucn Γ' (A eren) → ESemTsucn Γ')
        → ESemTsucn Γ

    ESemsucn : (Γ : Context) → ESemTsucn Γ → Set₁
    ESemsucn Γ EU = ESemTn Γ
    ESemsucn Γ (fromNe e) = Ne Γ (suc n) -- NOTE: if Ne is parametrized specifically by Ne in SHALLOW embedding, then that will help here later...
    ESemsucn Γ (Ecumu T) = ESemn Γ T
    ESemsucn Γ (EΠ A B)
      = ∀{Γ'} → (eren : ERen Γ Γ')
        → (a : ESemsucn Γ' (A eren))
        → ESemsucn Γ' (B eren a)

    -- Why does ESem have to be parametrized be ESemT?
open Esucn

mutual
  ESemT : ℕ → (Γ : Context) → Set₁
  ESemT zero = ESemTzero
  ESemT (suc n) = ESemTsucn n (ESemT n) (ESem {n})

  ESem : ∀{n} → (Γ : Context) → ESemT n Γ → Set₁
  ESem {zero} = ESemzero
  ESem {suc n} = ESemsucn n (ESemT n) (ESem {n})

mutual
  renSemT : ∀{n Γ₁ Γ₂} → ERen Γ₁ Γ₂ → ESemT n Γ₁ → ESemT n Γ₂
  renSemT {zero} ren (fromNe x) = {!   !}
  renSemT {suc n} ren EU = EU
  renSemT {suc n} ren (fromNe x) = {!   !}
  renSemT {suc n} ren (Ecumu T) = Ecumu (renSemT ren T)
  renSemT {suc n} ren (EΠ A B) = EΠ {! renSemT ren A  !} {!   !}

-- Shallow embedding on top of ESem?
U : ∀{n Γ} → ESemT (suc n) Γ
U = EU

-- Π : ∀{n Γ} → (A : ESemT (suc n) Γ)
--   → ESemT (suc n) (Γ , suc n {-A-})
--   → ESemT (suc n) Γ
-- Π A B = EΠ {! λ ren   !} {!   !}


mutual
  {-
  Why don't these functions pass Agda's termination checker?
  There is a lexicographic ordering in the functions on the arguments "n" and "T".
  Either n decreases, or n stays the same and T decreases.
  -}

  reifyT : ∀{n Γ} → (T : ESemT n Γ) → EType Γ n
  reifyT {zero} (fromNe e) = fromNe e
  reifyT {suc n} EU = EU
  reifyT {suc n} (fromNe x) = fromNe x
  reifyT {suc n} (Ecumu T) = Ecumu (reifyT {n} T)
  reifyT {suc n} (EΠ A B) = EΠ (reifyT {suc n} (A EidRen))
    (reifyT {suc n} (B Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same))))

  nApp : ∀{n Γ} → (T : ESemT n Γ) → Ne Γ n → ESem Γ T
  nApp {zero} (fromNe T) e = {! fromNe e  !} -- fromNe e
  -- nApp {suc n} EU e = {! ESemTsucn.fromNe ?  !} -- issue is some type level stuff.... need to eliminate all suc(suc n), should only need (suc n)
  nApp {suc zero} EU e = fromNe e
  nApp {suc (suc n)} EU e = fromNe e
  nApp {suc n} (fromNe x) e = e -- something something with η-expanded form, the other cases shouldn't be able to be defined like this...
  nApp {suc n} (Ecumu T) e = nApp {n} T (unCumu e) -- something about the way that cumu is stored in Nf/Ne, should be unique normal forms!
  nApp {suc n} (EΠ A B) e
    = λ eren t → nApp (B eren t) (Eapp (renNe eren e) (reify (A eren) t))

  reify : ∀{n Γ} → (T : ESemT n Γ) → ESem Γ T → Nf Γ n
  reify {zero} (fromNe T) e = {!   !} --e
  reify {suc n} EU t = fromType (reifyT {n} t)
  reify {suc n} (fromNe x) t = fromNe t
  reify {suc n} (Ecumu T) t = EcumuValue (reify {n} T t)
  reify {suc n} (EΠ A B) t
    = Elambda (reify (B Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same)))
                      (t Eweaken1Ren (nApp (A Eweaken1Ren) (Evar same))))

-- Have I become extrinsic?


-- eval : ∀{n Γ} → (T : ESemT n Γ)
--   → Exp Γ n → ESem Γ T
-- eval {zero} T (Elambda e) = {!   !}
-- eval {zero} T (Evar x) = {!   !}
-- eval {zero} T (Eapp e e₁) = {!   !}
-- eval {zero} T (EΠ e e₁) = {!   !}
-- eval {suc n} T (Elambda e) = {!   !}
-- eval {suc n} T (Evar x) = {!   !}
-- eval {suc n} T (Eapp e e₁) = {!   !}
-- eval {suc n} T (EΠ e e₁) = {!   !}
-- eval {suc n} T EU = {!   !}
-- eval {suc n} T (Ecumu e) = {!   !}
-- eval {suc n} T (EcumuValue e) = {!   !}
