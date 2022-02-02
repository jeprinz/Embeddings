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

mutual
  data Context : Set where
    ∅ : Context
    _,_ : Context → Type → Context
  data Var : Set where
    same : Var
    next : Var → Var
  data Type : Set where
    U : ℕ → Type
    Π : Type → Type → Type
    fromNe : Ne → Type
    Lift : Type → Type
  data Ne : Set where
    var : Var → Ne
    app : Ne → Nf → Ne
    lower : Ne → Ne
  data Nf : Set where
    fromNe : Ne → Nf -- only when of type Ne, so as not to duplicate fromType(fromNe e)
    fromType : Type → Nf
    lambda : Nf → Nf
    lift : Nf → Nf

-- Ren : Context → Context → Set
-- Ren Γ₁ Γ₂ =

-- data _∋_::_ : Context → Var → Type → Set where -- \ni
  -- same : ∀{Γ T} → (Γ , T) ∋ same :: T -- but T needs to be weakened!
