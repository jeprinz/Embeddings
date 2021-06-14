{-# OPTIONS --cumulativity #-}
{-# OPTIONS --without-K #-}

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

{-

-}

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
k = lsuc j -- type level 1+i

Ctx : Set j
Type : Ctx → Set j
Term : (Γ : Ctx) → Type Γ → Set i
Ctx = Set i
Type Γ = Γ → Set i
Term Γ T = (γ : Γ) → T γ

-- Context constructors
nil : Ctx
nil = ⊤

cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ Γ T

-- Type constructors
U₀ : ∀{Γ} → Type Γ
U₀ = λ γ → Set₀

U₁ : ∀{Γ} → Type Γ
U₁ = λ γ → Set₁

U₂ : ∀{Γ} → Type Γ
U₂ = λ γ → Set₂

Π : ∀{Γ} → (A : Type Γ) → (B : Type (cons Γ A)) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

weakenT : {Γ : Ctx} → {A : Type Γ} → Type Γ → Type (cons Γ A)
weakenT T = λ γ → T (proj₁ γ)

varT : {Γ : Ctx} → Type (cons Γ U₀)
varT = proj₂

sub : {Γ : Ctx} → {A : Type Γ} → Type (cons Γ A)
  → Term Γ A → Type Γ
sub T e = λ γ → T (γ , e γ)

-- Term constructors

lambda : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app  : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term Γ (Π A B) → (x : Term Γ A) → Term Γ (sub B x)
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

weaken : {Γ : Ctx} → {A T : Type Γ}
  → Term Γ T → Term (cons Γ A) (weakenT T)
weaken e = λ γ → e (proj₁ γ)

var : {Γ : Ctx} → {T : Type Γ}
  → Term (cons Γ T) (weakenT T)
var = proj₂

U₀' : ∀{Γ} → Term Γ U₁
U₀' = λ γ → Set₀

U₁' : ∀{Γ} → Term Γ U₂
U₁' = λ γ → Set₁

Π' : ∀{Γ} → (A : Term Γ U₀) → (B : Term (cons Γ A) U₀) → Term Γ U₀
Π' A B = λ γ → (a : A γ) → B (γ , a)

mutual
  data ECtx : Ctx → Set j where
    ∅ : ECtx ⊤
    _,_ : ∀{aΓ} → (ctx : ECtx aΓ) → (T : aΓ → Set i) → ECtx (Σ {i} {i} aΓ T)

  data InCtx : {aΓ : Ctx} → (Γ : ECtx aΓ) → (T : aΓ → Set i)
    → ((γ : aΓ) → T γ) → Set j where
    same : ∀{aΓ T} → {Γ : ECtx aΓ} → InCtx (Γ , T) (λ γ → T (proj₁ γ)) proj₂
    next : ∀{aΓ Γ T A a} → InCtx {aΓ} Γ A a → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

mutual
  data Nf : {aΓ : Set i} → (Γ : ECtx aΓ) → (T : Type aΓ)
    → ((γ : aΓ) → T γ) → Set j where
    Elambda : ∀{aΓ} → {Γ : ECtx aΓ} → {A : Type aΓ} → {B : Type (cons aΓ A)} → ∀{a}
      → Nf (Γ , A) B a → Nf Γ (λ γ → ((x : A γ) → B (γ , x))) (λ γ x → a (γ , x))
    EΠ₀ : {aΓ : Set i} → {Γ : ECtx aΓ} → {a₁ : aΓ → Set} → {a₂ : Σ {i} {i} aΓ a₁ → Set}
      → (A : Nf Γ (λ _ → Set) a₁)
      → (B : Nf (Γ , (λ γ → a₁ γ)) (λ _ → Set) a₂)
      → Nf Γ (λ _ → Set) (λ γ → (x : a₁ γ) → a₂ (γ , x))
    EU₀ : {aΓ : Set i} → {Γ : ECtx aΓ} → Nf {aΓ} Γ U₁ U₀'
    fromNe : ∀{aΓ} → {Γ : ECtx aΓ} → {T : aΓ → Set i}
      → {a : (γ : aΓ) → T γ} → Ne Γ T a → Nf Γ T a

  data Ne : {aΓ : Set i} → (Γ : ECtx aΓ) → (T : Type aΓ)
    → ((γ : aΓ) → T γ) → Set j where
    Evar : {aΓ : Set i} → {Γ : ECtx aΓ} → {T : aΓ → Set i} → {a : (γ : aΓ) → T γ}
      → (icx : InCtx Γ T a) → Ne {aΓ} Γ T a
    Eapp : {aΓ : Set i} → {Γ : ECtx aΓ} → {A : aΓ → Set i} → {B : (Σ {i} {i} aΓ A) → Set i} → ∀{a₁ a₂}
        → Ne Γ (λ γ → (a : A γ) → B (γ , a)) a₁ → (x : Nf Γ A a₂)
        → Ne Γ (λ γ → B (γ , a₂ γ)) (λ γ → (a₁ γ) (a₂ γ))

-- Need ECtx?

{-
Suppose that I have T, e are type and term in a shallow embedding.
If in this embedding, I build the same looking NType and NTerm, then
The NType gives (Sem Γ T), and the NTerm gives eval e : Sem Γ T

Except it must be something like unquote-n, so that the objects in Sem Γ T can
easily be converted to Exp.
Or, could build reify from NType?

-}

NCtx : (Γ : Ctx) → ECtx Γ → Set k
NCtx Γ EΓ = Set j

NType' : {Γ : Ctx} → {EΓ : ECtx Γ} → (NΓ : NCtx Γ EΓ) → Type Γ → Set k
NType' NΓ T = Set j
NType : {Γ : Ctx} → (EΓ : ECtx Γ) → Type Γ → Set k
NType EΓ T = Set j

NCons : {Γ : Ctx} → {EΓ : ECtx Γ} → (NΓ : NCtx Γ EΓ)
  → {T : Type Γ}
  → NType' NΓ T → NCtx (cons Γ T) (EΓ , T)
NCons NΓ NT = Σ NΓ {! NT  !}


NTerm : ∀{Γ : Ctx} → (EΓ : ECtx Γ)
  → {T : Type Γ}
  → NType EΓ T
  → (a : Term Γ T)
  → Nf EΓ T a
  → Set k
NTerm EΓ T t e = T

NU₀ : ∀{Γ} → {EΓ : ECtx Γ}
  → NType EΓ U₁
NU₀ {aΓ} {Γ} = Nf Γ U₁ U₀'

NU₁ : ∀{Γ} → (EΓ : ECtx Γ)
  → NType EΓ U₁
NU₁ Γ = Nf Γ U₂ U₁'

-- U₀' : ∀{Γ} → Term Γ U₁
-- U₀' = λ γ → Set₀
NU₀' : ∀{aΓ} → {Γ : ECtx aΓ}
  -- → NTerm Γ (NU₁ Γ) U₀'
  → Nf Γ U₁ U₀'
NU₀' = EU₀

NΠ : ∀{Γ} → {A : Type Γ} → {B : Type (cons Γ A)}
  → {EΓ : ECtx Γ}
  → NType EΓ A → NType (EΓ , A) B
  → NType EΓ (Π A B)
NΠ {Γ} {A} {B} {EΓ} NA NB =
  Σ {i} {j} (Term Γ (Π A B)) -- For some agda value of the function f,
  (λ f →
    (Nf EΓ (Π A B) f) -- Term of appropriate type
    ×
    (∀{a} → Nf EΓ A a → Nf EΓ (sub B a) (app f a)) -- function unquoted by one.
  )

{-

Thoughts on above:
If use unq version of Exp, then don't need Σ. Will the Σ cause issues elsewhere?

Need Ren Γ Γ' on left?

-}

Nlambda : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → {EΓ : ECtx Γ} → {NA : NType EΓ A} → {NB : NType (EΓ , A) B}
  → ∀{a e}
  -- → Nf (Γ , A) B a → Nf Γ (Π A B) (lambda a)
  → NTerm {cons Γ A} (EΓ , A) {B} NB a e
  → NTerm {Γ} EΓ (NΠ {Γ} {A} {B} {EΓ} NA NB) (lambda a) (Elambda e)
-- Nlambda e = Elambda e
Nlambda {Γ} {A} {B} {EΓ} {NA} {NB} {a} {e} n
  = (lambda a)
  , (Elambda e)
  , (λ e₁ → {!  e !} )

-- extract : NTerm Γ T → Exp Γ T

{-

Its like if in unquote-n, instead of having a type called Exp and then a function
unquote-n : Exp Γ T → ... [Γ , T], instead we have for each constructor c of Exp,
unquote-n-c : ... [Γ , T]
and instead of unquote-n (c₁ (c₂ c₃)), we have
unqc₁ (unc₂ unc₃)

so for c : A's → C, we have
unquote-n-c : A's → ... [Γ , T]

-}

{-

Ctx : Set j
Type : Ctx → Set k
Term : (Γ : Ctx) → Type Γ → Set i

Ctx = Set i
-- Type Γ = Γ → (Set i × Set i)
-- Type Γ = (Γ → Set i) × Set j

Type Γ = Γ → Set i
-- Term Γ T = (γ : Γ) → T γ

-- Context constructors
nil : Ctx
nil = ⊤

cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ Γ T



-- Type constructors
U₀ : ∀{Γ} → Type Γ
U₀ = λ γ → Set₀

U₁ : ∀{Γ} → Type Γ
U₁ = λ γ → Set₁

weakenT : {Γ : Ctx} → {A : Type Γ} → Type Γ → Type (cons Γ A)
weakenT T = λ γ → T (proj₁ γ)

varT : {Γ : Ctx} → Type (cons Γ U₀)
varT = proj₂

sub : {Γ : Ctx} → {A : Type Γ} → Type (cons Γ A)
  → Term Γ A → Type Γ
sub T e = λ γ → T (γ , e γ)

-- Term constructors

lambda : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app  : {Γ : Ctx} → {A : Type Γ} → {B : Type (cons Γ A)}
  → Term Γ (Π A B) → (x : Term Γ A) → Term Γ (sub B x)
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

weaken : {Γ : Ctx} → {A T : Type Γ}
  → Term Γ T → Term (cons Γ A) (weakenT T)
weaken e = λ γ → e (proj₁ γ)

var : {Γ : Ctx} → {T : Type Γ}
  → Term (cons Γ T) (weakenT T)
var = proj₂


-- Example:

-- the following is the type "(X : Set₀) → X → X"
idT : Type nil
idT = Π U₀ (Π varT (weakenT varT))

-- the following is the term "λ X x . x"
id : Term nil idT
id = lambda (lambda var)

-- Type can be removed and replaced with terms in dependent type theory fashion.
-- but this is nonstandard and therefore probably not included in the parametricity mapping

U₀' : ∀{Γ} → Term Γ U₁
U₀' = λ γ → Set₀

Π' : ∀{Γ} → (A : Term Γ U₀) → (B : Term (cons Γ A) U₀) → Term Γ U₀
Π' A B = λ γ → (a : A γ) → B (γ , a)

-}
