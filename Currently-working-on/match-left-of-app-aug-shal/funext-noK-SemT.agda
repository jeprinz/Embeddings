{-# OPTIONS --without-K #-}

open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function

{-

The embedding from Core.agda, but built into a shallow embedding and stored
shallow embedding. Doesn't seem to gain particularly much from doing this.

-}

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

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

consistency : ∀{n} → Sem (2 + n) type⊥ → ⊥
consistency {zero} e with (e U)
... | ()
consistency {suc n} e = consistency (e type⊥)

_⇒_ : ∀{n} → SemT n → SemT n → SemT n
_⇒_ {suc n} A B = Π A (λ _ → B)

typeBool : ∀{n} → SemT (suc n)
typeBool = Π U (λ X → (cumu X) ⇒ (cumu X ⇒ cumu X))

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

-------------------- Augmented "shallow" embedding -----------------------------

data Context : Ctx → Set₁ where
  ∅ : Context nil
  _,_ : ∀{n SΓ} → (ctx : Context SΓ) → (T : Type n SΓ) → Context (cons SΓ T)

data InCtx : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Type n SΓ} → {Γ : Context SΓ}
    → InCtx {n} (Γ , T) (λ γ → T (proj₁ γ)) proj₂
  next : ∀{n m SΓ Γ A a} → {T : Type n SΓ} → InCtx {m} {SΓ} Γ A a
    → InCtx (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

data Exp : ∀{n} → {SΓ : Ctx} → (Γ : Context SΓ) → (T : Type n SΓ)
  → Term SΓ T → Set₁ where
  Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
    → {B : Type (suc n) (cons SΓ A)} → ∀{a}
    → Exp (Γ , A) B a → Exp Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
  Evar : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → {a : Term SΓ T}
    → (icx : InCtx Γ T a) → Exp {n} {SΓ} Γ T a
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

extractTerm : ∀{n SΓ Γ T t} → Exp {n} {SΓ} Γ T t → Term SΓ T
extractTerm {_} {_} {_} {_} {t} e = t

exampleType : Exp {2} ∅ SU _
exampleType = EΠ EU (EΠ (Ecumu (Evar same)) (Ecumu (Evar (next same))))

exampleTerm : Exp ∅ (extractTerm exampleType) _
exampleTerm = Elambda (Elambda (Evar same))

--------------------------------------------------------------------------------

data Eq2 {l : Level} {P : Set l} {Q : P → Set l} :
  (a₁ a₂ : P) → Q a₁ → Q a₂ → Set l where
  refl : ∀{a b} → Eq2 a a b b

Eq2' : {l : Level} {P : Set l} {Q : P → Set l}
  → (a₁ a₂ : P) → Q a₁ → Q a₂ → Set l
Eq2' {l} {P} {Q} a₁ a₂ b₁ b₂
  = _≡_ {l} {Σ P Q} (a₁ , b₁) (a₂ , b₂)

Eq3 : {l : Level} {P : Set l} {Q : P → Set l} {R : (p : P) → Q p → Set l}
  → (a₁ a₂ : P) → (b₁ : Q a₁) → (b₂ : Q a₂) → R a₁ b₁ → R a₂ b₂ → Set l
Eq3 {l} {P} {Q} {R} a₁ a₂ b₁ b₂ c₁ c₂
  = _≡_ {l} {Σ P (λ a → Σ (Q a) (R a))} (a₁ , b₁ , c₁) (a₂ , b₂ , c₂)

lemma : ∀{n} → {A A' : SemT (suc n)} → {B : Sem (suc n) A → SemT (suc n)}
  → {B' : Sem (suc n) A' → SemT (suc n)}
  → (p : Π A B ≡ Π A' B')
  → Eq2 A A' B B'
lemma refl = refl

lemma2 : ∀{n} → {A A' : SemT (suc n)} → {B : Sem (suc n) A → SemT (suc n)}
  → {B' : Sem (suc n) A' → SemT (suc n)}
  → (p : Π A B ≡ Π A' B')
  → Eq2' A A' B B'
lemma2 refl = refl

funExt : ∀{l} {A : Set l} {B : A → Set l} {f g : (x : A) → B x}
           → ((x : A) → f x ≡ g x) → f ≡ g
funExt = {!   !} -- p x i

-- funExt2 : ∀{l} {A : Set l} {B : A → Set l} {C : (a : A) → B a → Set l}
--   → {f₁ f₂ : (a : A) → B a}
--   → {g₁ : (a : A) → C a (f₁ a)}
--   → {g₂ : (a : A) → C a (f₂ a)}
--   → ((a : A) → Eq2 {l} {B a} {C a} (f₁ a) (f₂ a) (g₁ a) (g₂ a) )
--   → Eq2 f₁ f₂ g₁ g₂
-- funExt2 p = {! funExt p  !}

happly : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
            → f ≡ g → ((x : A) → f x ≡ g x)
happly refl x = refl

theorem : ∀{n Γ} → {A A' : Type (suc n) Γ}
  → {B : Type (suc n) (cons Γ A)}
  → {B' : Type (suc n) (cons Γ A')}
  → SΠ A B ≡ SΠ A' B'
  → Eq2' A A' B B'
theorem p
  = cong (λ f → (proj₁ ∘ f , λ (γ , a) → proj₂ (f γ) a)) (funExt (λ γ → lemma2 (happly p γ)))

maybeLamImpl : ∀{n SΓ Γ T t} → Exp {suc n} {SΓ} Γ T t
  → Maybe (Σ (Type (suc n) SΓ)
          (λ A → Σ (Type (suc n) (cons SΓ A))
          (λ B → Σ (Term (cons SΓ A) B)
          -- (λ t' → Eq2' {_} {Type (suc n) SΓ} {λ T → Term SΓ T}
              -- (SΠ A B) T (Slambda {_} {SΓ} {A} {B} t') t
          (λ t' → Σ (T ≡ (SΠ A B))
          (λ p → Exp (Γ , A) B (λ (γ , a) → (subst (Term SΓ) p t) γ a))))))
maybeLamImpl {n} {SΓ} {Γ} {T} {t} (Elambda e) = just (_ , _ , (λ (γ , a) → t γ a) , refl , e)
maybeLamImpl _ = nothing

maybeLamImplTest1 : ∀{n SΓ Γ T t} → Exp {suc n} {SΓ} Γ T t
  → Maybe (Σ (Type (suc n) SΓ)
          (λ A → Σ (Type (suc n) (cons SΓ A))
          (λ B → Σ (Term (cons SΓ A) B)
          (λ t' → Σ (_≡_ {_} {(γ : SΓ) → Σ (SemT (suc n)) (Sem (suc n))}
            (λ γ → (T γ , t γ))
            (λ γ → ((SΠ A B) γ , λ a → t' (γ , a))))
          (λ p → Exp (Γ , A) B t')))))
maybeLamImplTest1 (Elambda e) = just (_ , _ , _ , refl , e)
maybeLamImplTest1 _ = nothing

lemma3 : ∀{n} → {A A' : SemT (suc n)} → {B : Sem (suc n) A → SemT (suc n)}
  → {B' : Sem (suc n) A' → SemT (suc n)}
  → ∀{t t'}
  → (_≡_ {_} {Σ (SemT (suc n)) (Sem (suc n))}
      ((Π A B) , t)
      ((Π A' B') , t'))
  → Eq3 A A' B B' t t'
lemma3 refl = refl

theorem3 : ∀{n Γ} → {A A' : Type (suc n) Γ}
  → {B : Type (suc n) (cons Γ A)}
  → {B' : Type (suc n) (cons Γ A')}
  → {t : Term (cons Γ A) B}
  → {t' : Term (cons Γ A') B'}
  → _≡_ {_} {(γ : Γ) → Σ (SemT (suc n)) (Sem (suc n))}
      (λ γ → ((SΠ A B) γ , λ a → t (γ , a)))
      (λ γ → ((SΠ A' B') γ , λ a → t' (γ , a)))
  → Eq3 A A' B B' t t'
theorem3 p
   = cong (λ f → (proj₁ ∘ f , (λ (γ , a) → proj₁ (proj₂ (f γ)) a) , λ (γ , a) → proj₂ (proj₂ (f γ)) a))
      (funExt (λ γ → lemma3 (happly p γ)))

maybeLam : ∀{n SΓ Γ A B t} → Exp {suc n} {SΓ} Γ (SΠ A B) t
  → Maybe (Exp (Γ , A) B (λ (γ , a) → t γ a))
maybeLam {n} {SΓ} {Γ} e with maybeLamImplTest1 e
... | nothing = nothing
-- ... | just (A , B , t' , p , e') with (theorem p)
-- ... | refl = just {!  e' !} -- note that this problem doesn't happen with axiom K because can just pattern match on p
... | just (A , B , t' , p , e') with (theorem3 p)
... | refl = just e'
