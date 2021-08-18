{-# OPTIONS --without-K #-}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function

{-

It turns out to be possible to do β-reduction (nor full on normalization, just a
single reduction) with augmented shallow embeddings. Two things are necessary
for this:
1) Use a datatype encoding of the universe of types, here "SemT"
2) Use function extentionality.
  In order to make this approach as widely applicable as possible, I have turned
  off axiom K, and used only the non-dependent version of function extentionality.

  In order to implement function extentionality, I use two postulates and a
  rewrite rule. This gives the necessary computation. I see no reason that this
  stuff wouldn't work in any theory which supports computational function
  extentionality, however.

-}

----------------------------- Function Extentionality --------------------------

postulate
  funExt : ∀{l} {A B : Set l} {f g : A → B}
     → ((x : A) → f x ≡ g x) → f ≡ g
  funExtElim : ∀{l} {A B : Set l} {f : A → B}
     → funExt {l} {A} {B} {f} {f} (λ x → refl) ≡ refl

{-# REWRITE funExtElim #-}

happly : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
            → f ≡ g → ((x : A) → f x ≡ g x)
happly refl x = refl

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

--------------------------------------------------------------------------------

module sucn (SemTn : Set) (Semn : SemTn → Set) where
  mutual
    data SemTsucn : Set where
        U : SemTsucn
        Π : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        cumu : SemTn → SemTsucn

    Semsucn : SemTsucn → Set
    Semsucn U = SemTn
    Semsucn (Π A B) = (a : Semsucn A) → Semsucn (B a)
    Semsucn (cumu T) = Semn T

open sucn

mutual
  SemT : ℕ → Set
  SemT zero = SemTzero
  SemT (suc n) = sucn.SemTsucn (SemT n) (Sem n)

  Sem : (n : ℕ) → SemT n → Set
  Sem zero T = Semzero T
  Sem (suc n) T = sucn.Semsucn _ _ T

type⊥ : ∀{n} → SemT (2 + n)
type⊥ = Π U λ X → cumu X

------------------------  "Shallow" embedding   --------------------------------

Ctx = Set
Type : ℕ → Ctx → Set
Type n Γ = Γ → SemT n
Term : ∀{n} → (Γ : Ctx) → Type n Γ → Set
Term Γ T = (γ : Γ) → Sem _ (T γ)
nil : Ctx
nil = ⊤
cons : ∀{n} → (Γ : Ctx) → Type n Γ → Ctx
cons Γ T = Σ Γ (λ γ → Sem _ (T γ))

SU : ∀{n Γ} → Type (suc n) Γ
SU = λ _ → U

SΠ : ∀{n Γ} → (A : Type (suc n) Γ) → Type (suc n) (cons Γ A) → Type (suc n) Γ
SΠ A B = λ γ → Π (A γ) ((λ a → B (γ , a)))

Slambda : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term (cons Γ A) B → Term Γ (SΠ A B)
Slambda e = λ γ → λ a → e (γ , a)

Sapp : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
  → Term Γ (SΠ A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
Sapp e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

Svar : ∀{n Γ} → {A : Type (suc n) Γ} → Term (cons Γ A) (λ γ → (A (proj₁ γ)))
Svar = proj₂

Sweaken : ∀{n Γ} → {T A : Type n Γ} → Term Γ T → Term (cons Γ A) (λ γ → (T (proj₁ γ)))
Sweaken e = λ γ → e (proj₁ γ)

ScumuT : ∀{n Γ} → (T : Type n Γ) → Type (suc n) Γ
ScumuT T = λ γ → cumu (T γ)

Scumu : ∀{n Γ} → {T : Type n Γ} → Term Γ T → Term Γ (ScumuT T)
Scumu e = e

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

append1ren : ∀{n Γ₁ Γ₂} → {T : Type n Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
append1ren sub (γ₂ , t) = sub γ₂

append1sub : ∀{n Γ₁ Γ₂} → {T : Type n Γ₁} → Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
append1sub sub e γ₂ = sub γ₂ , e (sub γ₂)

idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

weaken1Ren : ∀{Γ n T} → Sub Γ (cons {n} Γ T)
weaken1Ren = proj₁

subType : ∀{Γ₁ Γ₂ n} → Sub Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
subType sub T = λ γ₂ → T (sub γ₂)

forget1ren : ∀{Γ₁ Γ₂ n} → (sub : Sub Γ₁ Γ₂) → (T : Type n Γ₁)
  → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
forget1ren sub T (γ , t) = sub γ , t

subExp : ∀{Γ₁ Γ₂ n T} → (sub : Sub Γ₁ Γ₂) → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
subExp sub e = λ γ₂ → e (sub γ₂)

-------------------- Augmented "shallow" embedding -----------------------------

data Context : Ctx → Set₁ where
  ∅ : Context nil
  _,_ : ∀{n SΓ} → (ctx : Context SΓ) → (T : Type n SΓ) → Context (cons SΓ T)

data Var : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Type n SΓ} → {Γ : Context SΓ}
    → Var {n} (Γ , T) (λ γ → T (proj₁ γ)) proj₂
  next : ∀{n m SΓ Γ A a} → {T : Type n SΓ} → Var {m} {SΓ} Γ A a
    → Var (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

data Exp : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
    → {B : Type (suc n) (cons SΓ A)} → ∀{a}
    → Exp (Γ , A) B a → Exp Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
  Evar : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → {a : Term SΓ T}
    → (icx : Var Γ T a) → Exp {n} {SΓ} Γ T a
  Eapp : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
      → {B : Type (suc n) (cons SΓ A)} → ∀{a₁ a₂}
      → Exp {suc n} Γ (SΠ A B) a₁ → (x : Exp {suc n} Γ A a₂)
      → Exp {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sapp {n} {SΓ} {A} {B} a₁ a₂)
  EΠ : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {a₁ : Term SΓ (SU {suc n})}
    → {a₂ : Type (suc n) (cons SΓ a₁)} → (A : Exp Γ (SU {suc n}) a₁)
    → (B : Exp (Γ , a₁) (SU {suc n}) a₂)
    → Exp Γ (SU {suc n}) (SΠ {n} a₁ a₂)
  EU : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → Exp {suc (suc n)} {SΓ} Γ SU SU
  -- TODO: shouldn't have to be 2+n there. Something funky with way I've defined things above!
  -- Eweaken : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ}
    -- → {A : Type n SΓ} → ∀{a}
    -- → Exp Γ T a → Exp (Γ , A) (λ γ → (T (proj₁ γ))) (Sweaken {_} {_} {T} {A} a)
  EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
    → Exp Γ T a → Exp Γ (ScumuT T) (Scumu {n} {_} {T} a)
  Ecumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
    → Exp Γ (SU {n}) a → Exp Γ (SU {suc n}) (ScumuT a)

  -- Renamings and Substitutions on Exp

ERen : ∀{sΓ₁ sΓ₂} → Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
ERen sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Var Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)

EidRen : ∀{sΓ Γ} → ERen {sΓ} idSub Γ Γ
EidRen x = x

Eforget1ren : ∀{n sΓ₁ sΓ₂ T} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → ERen sub Γ₁ Γ₂ → ERen (forget1ren {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , subType sub T)
Eforget1ren ren same = same
Eforget1ren ren (next x) = next (ren x)

Eweaken1Ren : ∀{sΓ Γ n T} → ERen {sΓ} (weaken1Ren {sΓ} {n} {T}) Γ (Γ , T)
Eweaken1Ren = next

renExp : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → ERen sub Γ₁ Γ₂ → Exp {n} Γ₁ T t → Exp Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)
renExp ren (Elambda e) = Elambda (renExp (Eforget1ren ren) e)
renExp ren (Evar x) = Evar (ren x)
renExp ren (Eapp e₁ e₂) = Eapp (renExp ren e₁) (renExp ren e₂)
renExp ren (EΠ A B) = EΠ (renExp ren A) (renExp (Eforget1ren ren) B)
renExp ren EU = EU
renExp ren (Ecumu e) = Ecumu (renExp ren e)
renExp ren (EcumuValue e) = EcumuValue (renExp ren e)

ESub : ∀{sΓ₁ sΓ₂} → Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
ESub sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Exp Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)

EidSub : ∀{sΓ Γ} → ESub {sΓ} idSub Γ Γ
EidSub x = Evar x

Eforget1sub : ∀{n sΓ₁ sΓ₂ T} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → ESub sub Γ₁ Γ₂ → ESub (forget1ren {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , subType sub T)
Eforget1sub sub same = Evar same
Eforget1sub sub (next x) = renExp Eweaken1Ren (sub x)

EsubExp : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → ESub sub Γ₁ Γ₂ → Exp {n} Γ₁ T t → Exp Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)
EsubExp sub (Elambda e) = Elambda (EsubExp (Eforget1sub sub) e)
EsubExp sub (Evar x) = sub x
EsubExp sub (Eapp e₁ e₂) = Eapp (EsubExp sub e₁) (EsubExp sub e₂)
EsubExp sub (EΠ A B) = EΠ (EsubExp sub A) (EsubExp (Eforget1sub sub) B)
EsubExp sub EU = EU
EsubExp sub (Ecumu e) = Ecumu (EsubExp sub e)
EsubExp sub (EcumuValue e) = EcumuValue (EsubExp sub e)

Eappend1sub : ∀{sΓ₁ sΓ₂ n Γ₁ Γ₂ sub} → {T : Type n sΓ₁} → {t : Term sΓ₁ T}
  → ESub {sΓ₁} {sΓ₂} sub Γ₁ Γ₂
  → Exp Γ₁ T t → ESub (append1sub {_} {_} {_} {T} sub t) (Γ₁ , T) Γ₂
Eappend1sub sub e same = EsubExp sub e
Eappend1sub sub e (next x) = sub x

--------------------------------------------------------------------------------

Eq3 : {l : Level} {P : Set l} {Q : P → Set l} {R : (p : P) → Q p → Set l}
  → (a₁ a₂ : P) → (b₁ : Q a₁) → (b₂ : Q a₂) → R a₁ b₁ → R a₂ b₂ → Set l
Eq3 {l} {P} {Q} {R} a₁ a₂ b₁ b₂ c₁ c₂
  = _≡_ {l} {Σ P (λ a → Σ (Q a) (R a))} (a₁ , b₁ , c₁) (a₂ , b₂ , c₂)

maybeLamImpl : ∀{n SΓ Γ T t} → Exp {suc n} {SΓ} Γ T t
  → Maybe (Σ (Type (suc n) SΓ)
          (λ A → Σ (Type (suc n) (cons SΓ A))
          (λ B → Σ (Term (cons SΓ A) B)
          (λ t' → Σ (_≡_ {_} {(γ : SΓ) → Σ (SemT (suc n)) (Sem (suc n))}
            (λ γ → (T γ , t γ))
            (λ γ → ((SΠ A B) γ , λ a → t' (γ , a))))
          (λ p → Exp (Γ , A) B t')))))
maybeLamImpl (Elambda e) = just (_ , _ , _ , refl , e)
maybeLamImpl _ = nothing

lemma : ∀{n} → {A A' : SemT (suc n)} → {B : Sem (suc n) A → SemT (suc n)}
  → {B' : Sem (suc n) A' → SemT (suc n)}
  → ∀{t t'}
  → (_≡_ {_} {Σ (SemT (suc n)) (Sem (suc n))}
      ((Π A B) , t)
      ((Π A' B') , t'))
  → Eq3 A A' B B' t t'
lemma refl = refl

theorem : ∀{n Γ} → {A A' : Type (suc n) Γ}
  → {B : Type (suc n) (cons Γ A)}
  → {B' : Type (suc n) (cons Γ A')}
  → {t : Term (cons Γ A) B}
  → {t' : Term (cons Γ A') B'}
  → _≡_ {_} {(γ : Γ) → Σ (SemT (suc n)) (Sem (suc n))}
      (λ γ → ((SΠ A B) γ , λ a → t (γ , a)))
      (λ γ → ((SΠ A' B') γ , λ a → t' (γ , a)))
  → Eq3 A A' B B' t t'
theorem p
   = cong (λ f → (proj₁ ∘ f , (λ (γ , a) → proj₁ (proj₂ (f γ)) a) , λ (γ , a) → proj₂ (proj₂ (f γ)) a))
      (funExt (λ γ → lemma (happly p γ)))

maybeLam : ∀{n SΓ Γ A B t} → Exp {suc n} {SΓ} Γ (SΠ A B) t
  → Maybe (Exp (Γ , A) B (λ (γ , a) → t γ a))
maybeLam {n} {SΓ} {Γ} e with maybeLamImpl e
... | nothing = nothing
... | just (A , B , t' , p , e') with (theorem p)
... | refl = just e'

βreduce : ∀{n sΓ Γ T t} → Exp {n} {sΓ} Γ T t → Exp {n} {sΓ} Γ T t
βreduce (Elambda e) = Elambda (βreduce e)
βreduce (Evar icx) = Evar icx
βreduce (EΠ A B) = EΠ (βreduce A) (βreduce B)
βreduce EU = EU
βreduce (EcumuValue e) = EcumuValue (βreduce e)
βreduce (Ecumu e) = Ecumu (βreduce e)
βreduce (Eapp e₁ e₂) with maybeLam e₁
... | nothing = Eapp (βreduce e₁) (βreduce e₂)
... | just e = EsubExp (Eappend1sub EidSub e₂) e

term1 : Exp {2} ∅ SU SU
term1 = Eapp (Elambda (Evar same)) EU

test : βreduce term1 ≡ EU
test = refl
