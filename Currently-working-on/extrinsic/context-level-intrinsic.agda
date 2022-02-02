open import Data.Nat
{-

What is really so hard about extrinsic anyway?
Can I translate my paper proof of consistency to Agda?
In the paper proof, I never need to prove commutativity of anything
I think?

Things which can be intrinsic to a term:
Context? (at least it's length) (proving normalization terminates doesn't actually require knowing the types in the context...)
Spine? only really needed on types...
Level

Term should be annotated - have type annotations on lambda inputs
  (or just on every term)


----------------------------------------------------
Does my simple proof work on dep thy, not just sys F?
Π (a : A) B

-}

data Context : Set -- where
data Var : Context → ℕ → Set -- where
data Type : Context → ℕ → Set -- where
data Ne : Context → ℕ → Set -- where
data Nf : Context → ℕ → Set -- where
data Context where
  ∅ : Context
  _,_ : ∀{n} → (Γ : Context) → Type Γ n → Context
data Var where
  same : ∀{Γ n} → {T : Type Γ n} → Var (Γ , T) n
  next : ∀{Γ n m} → {T : Type Γ m} → Var Γ n → Var (Γ , T) n
data Type where
  U : ∀{Γ n} → Type Γ (suc n)
  Π : ∀{Γ n} → (A : Type Γ n) → Type (Γ , A) n → Type Γ n
  fromNe : ∀{Γ n} → Ne Γ n → Type Γ n
  Lift : ∀{Γ n} → Type Γ n → Type Γ (suc n)
data Ne where
  var : ∀{Γ n} → Var Γ n → Ne Γ n
  app : ∀{Γ n} → Ne Γ n → Nf Γ n → Ne Γ n
  lower : ∀{Γ n} → Ne Γ (suc n) → Ne Γ n
data Nf where
  fromNe : ∀{Γ n} → Ne Γ n → Nf Γ n -- only when of type Ne, so as not to duplicate fromType(fromNe e). Also keeps things expanded η !!!
  fromType : ∀{Γ n} → Type Γ n → Nf Γ n
  lambda : ∀{Γ n} → {A : Type Γ n} → Nf (Γ , A) n → Nf Γ n -- should there be two different levels here?
  lift : ∀{Γ n} → Nf Γ n → Nf Γ (suc n)

mutual
  data apply : ∀{Γ n} → Nf Γ n → Nf Γ n → Nf Γ n → Set where
    fromNe : ∀{Γ n} → (e₁ : Ne Γ n)
      → (e₂ : Nf Γ n)
      → apply (fromNe e₁) e₂ (fromNe (app e₁ e₂))
    lambda : ∀{Γ n} → {A : Type Γ n}
      → (e₁ : Nf (Γ , A) n)
      → (e₂ : Nf Γ n)
      → {subΓ : substCtx (Γ , A) same Γ}
      → {e₁' : Nf Γ n}
      → substNf same subΓ e₁ e₁'
      → apply (lambda e₁) e₂ e₁'
  data substCtx : ∀{n} → (Γ : Context) → Var Γ n → Context → Set where
  -- hereditary substitution
  data substNf : ∀{Γ Γ' n m}
    → (x : Var Γ m) → substCtx Γ x Γ' → Nf Γ n → Nf Γ' n → Set where
    -- lambda : ∀{Γ n}
  data substNe : ∀{Γ Γ' n m}
    → (x : Var Γ m) → substCtx Γ x Γ' → Ne Γ n → Ne Γ' n → Set where
  data substType : ∀{Γ Γ' n m}
    → (x : Var Γ m) → substCtx Γ x Γ' → Type Γ n → Type Γ' n → Set where

{-
Consider
id : (X : Set₀) → Lift (X → X)
T : Set₀  t : T

(lower (id T)) t : T

Where will lower get called by sub?
Do I need a repeated lowering and app concept?
  Essentially like Ne but Nf on left instead of var.
-}

Ren : Context → Context → Set
Ren Γ₁ Γ₂ = ∀{n} → Var Γ₁ n → Var Γ₂ n

idRen : ∀{Γ} → Ren Γ Γ
idRen x = x

appendRen : ∀{Γ₁ Γ₂ n} → {T : Type Γ₂ n} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
appendRen ren x = next (ren x)

renType : ∀{n Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Type Γ₁ n → Type Γ₂ n
renNe : ∀{n Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Ne Γ₁ n → Ne Γ₂ n
renNf : ∀{n Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Nf Γ₁ n → Nf Γ₂ n

liftRen : ∀{Γ₁ Γ₂ n} → {T : Type Γ₁ n} → (ren : Ren Γ₁ Γ₂)
  → Ren (Γ₁ , T) (Γ₂ , renType ren T)
liftRen ren same = same
liftRen ren (next x) = next (ren x)

renType ren U = U
renType ren (Π A B) = Π (renType ren A) (renType (liftRen ren) B)
renType ren (fromNe e) = fromNe (renNe ren e)
renType ren (Lift T) = Lift (renType ren T)

renNe ren (var x) = var (ren x)
renNe ren (app e₁ e₂) = app (renNe ren e₁) (renNf ren e₂)
renNe ren (lower e) = lower (renNe ren e)

renNf ren (fromNe e) = fromNe (renNe ren e)
renNf ren (fromType T) = fromType (renType ren T)
renNf ren (lambda e) = lambda (renNf (liftRen ren) e)
renNf ren (lift e) = lift (renNf ren e)

data WFVar : ∀{n} → (Γ : Context) → Type Γ n → Var Γ n → Set where -- \ni
  same : ∀{Γ n} → {T : Type Γ n}
    → WFVar (Γ , T) (renType (appendRen idRen) T) same -- but T needs to be weakened!
  next : ∀{Γ n m} → {T : Type Γ n} → {A : Type Γ m} → {x : Var Γ n}
    → WFVar Γ T x
    → WFVar (Γ , A) (renType (appendRen idRen) T) (next x) -- but T needs to be weakened!

WFRen : ∀{Γ₁ Γ₂} → Ren Γ₁ Γ₂ → Set
WFRen {Γ₁} {Γ₂} ren = ∀{n} → (T : Type Γ₁ n) → {x : Var Γ₁ n}
  → WFVar Γ₁ T x → WFVar Γ₂ (renType ren T) (ren x)
--                          ↑ might be easier if we DIDN'T have type param by Γ,
--                            and instead proved that
-- if Ren Γ₁ Γ₂, then WFType Γ₁ T → WFType Γ₂ T

idRenWF : ∀{Γ} → WFRen (idRen {Γ})
-- idRenWF {Γ} U x = x
-- idRenWF {Γ} (Π A B) x = {!   !}
-- idRenWF {Γ} (fromNe x₁) x = {!   !}
-- idRenWF {Γ} (Lift T) x = {! idRenWF T   !}

liftRenWF : ∀{Γ₁ Γ₂ n} → {ren : Ren Γ₁ Γ₂} → {T : Type Γ₁ n}
  → WFRen ren → WFRen (liftRen {_} {_} {_} {T} ren)
liftRenWF {_} {_} {_} {ren} {T} wfren wfx = {!   !}


mutual
  data WFType : ∀{n} → (Γ : Context) → Type Γ n → Set where
    U : ∀{n Γ} → WFType Γ (U {Γ} {n})
    Π : ∀{Γ n} → {A : Type Γ n} → {B : Type (Γ , A) n}
      → WFType Γ A → WFType (Γ , A) B → WFType Γ (Π A B)
    -- fromNe : ∀{Γ n} → Ne Γ n → Type Γ n
    -- Lift : ∀{Γ n} → Type Γ n → Type Γ (suc n)

  data WFContext : Context → Set where
    ∅ : WFContext ∅
    _,_ : ∀{Γ n} → {T : Type Γ n}
      → WFContext Γ → WFType Γ T → WFContext (Γ , T)

  data WFNeutral : ∀{n} → (Γ : Context) → (T : Type Γ n) → Ne Γ n → Set where
    var : ∀{Γ n T} → {x : Var Γ n}
      → WFVar Γ T x → WFNeutral Γ T (var x)
    app : ∀{Γ n} → {A : Type Γ n} → {B : Type (Γ , A) n}
      → ∀{e₁ e₂}
      → WFNeutral Γ (Π A B) e₁
      → (a : WFNormal Γ A e₂)
      → WFNeutral Γ {! B !} (app e₁ e₂) -- either syntactic reduction as relation, OR NBE from working99percent-what-is...
    lower : ∀{Γ n T e} → WFNeutral {suc n} Γ (Lift T) e
      → WFNeutral {n} Γ T (lower e)

  data WFNormal : ∀{n} → (Γ : Context) → (T : Type Γ n) → Nf Γ n → Set where
    -- fromNe : ∀{Γ n} → Ne Γ n → Nf Γ n -- only when of type Ne, so as not to duplicate fromType(fromNe e)
    -- fromType : ∀{Γ n} → Type Γ n → Nf Γ n
    fromNe : ∀{n Γ T e} → WFNeutral {n} Γ (fromNe T) e
      → WFNormal {n} Γ (fromNe T) (fromNe e)
    lambda : ∀{Γ n} → {A : Type Γ n} → {B : Type (Γ , A) n} → {e : Nf (Γ , A) n}
      → WFNormal (Γ , A) B e → WFNormal Γ (Π A B) (lambda e)
    lift : ∀{Γ n T e} → WFNormal {n} Γ T e
      → WFNormal {suc n} Γ (Lift T) (lift e)

test : ∀{n Γ A B e} → WFNormal {n} Γ (Π A B) e → ℕ
test (lambda e) = {!   !}

{-

Two approaches: induction and NbE.

For now i'll think about induction.
Ultimately, I want to define
app : e → e₁ ... eₙ → e
and
sub : e → x → e → e

as functions. But, I could first define them as relations?
1) define as relations on preterms
2) define as functions on WF-terms

-}

{-

NOTE: In this file I made the decision to have preterms parametrized by precontext
and level. However, it might be better not to, because then one could prove something
like:
If Γ < Γ' then
if Γ ⊢ T : U, then Γ' ⊢ T : U

And this might make reasoning about some things more straightforwards:
type can be equal even if they are not in the same context.



Think about in math/category theory: If H is a subgroup of G, then is
G ⊂ H as sets, or is there a morphism ϕ : H → G  ?

The former presentation is convenient for parametrized types: If H ≤ G, and
h : H, and T : Group → Set, then
h : T H, but also h : T G
With the morphism presentation, would need a way of transforming a morphism
H → G  into a morphism   T H → T G

-}
