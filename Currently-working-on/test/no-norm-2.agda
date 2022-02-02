open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

data TypeCode₀ : Set where
⟦_⟧₀ : TypeCode₀ → Set
⟦_⟧₀ ()

module Universe {TypeCode : Set} {⟦_⟧ : TypeCode → Set} where
  mutual
    data TypeCodeₙ₊₁ : Set where
        `U : TypeCodeₙ₊₁
        `Π : (A : TypeCodeₙ₊₁) → (⟦_⟧ₙ₊₁ A → TypeCodeₙ₊₁) → TypeCodeₙ₊₁
        `lift : TypeCode → TypeCodeₙ₊₁

    ⟦_⟧ₙ₊₁ : TypeCodeₙ₊₁ → Set
    ⟦ `U ⟧ₙ₊₁ = TypeCode
    ⟦ `Π A B ⟧ₙ₊₁ = (a : ⟦ A ⟧ₙ₊₁) → ⟦ B a ⟧ₙ₊₁
    ⟦ `lift T ⟧ₙ₊₁ = ⟦ T ⟧

open Universe

mutual
  TypeCode : ℕ → Set
  TypeCode zero = TypeCode₀
  TypeCode (suc n) = TypeCodeₙ₊₁ {TypeCode n} {⟦_⟧}

  ⟦_⟧ : {n : ℕ} → TypeCode n → Set
  ⟦_⟧ {zero} T = ⟦ T ⟧₀
  ⟦_⟧ {suc n} T = ⟦ T ⟧ₙ₊₁

Ctx = Set
Type : Ctx → Set₁
Type Γ = Γ → Set

Type' : ℕ → Ctx → Set₁
Type' n Γ = Γ → TypeCode n → Set

U : ∀{n Γ} → Type' n Γ
U {suc n} γ `U = ⊤
U {suc n} γ (`Π A B) = ⊥
-- U {suc n} _ (`lift x) = ⊥
U {suc n} γ (`lift T) = U γ T -- ???

-- cons : ∀{n} → (Γ : Ctx) → Type' n Γ → Ctx
-- cons Γ T = Σ Γ (λ γ → ⟦ T γ ⟧)
cons : ∀{n} → (Γ : Ctx) → Type' n Γ → Ctx → Set
cons Γ T Γ' = {!   !}

Π : ∀{n Γ} → Type' n Γ → {!   !} → Type' n Γ
Π {suc n} A B γ `U = ⊥
Π {suc n} A B γ (`Π A' B') = A γ A' × {! B γ B'  !}
Π {suc n} A B γ (`lift T) = ⊥

UisntΠ : ∀{n Γ A B} → U {n} {Γ} ≡ Π A B → ⊥
UisntΠ p = {! p  !}



-- Π : ∀{n Γ} → (A : Type' (suc n) Γ) → Type' (suc n) (cons Γ A) → Type' (suc n) Γ
-- Π A B = λ γ → `Π (A γ) ((λ a → B (γ , a)))
-- Π A B = ?

{-

Hypothesis: ≡ is bad, and relational style makes ≡ never necessary
(and therefore funext and ua unecessary.)

There is a difference between a function in the mathematical sense, which is
best described as a relation, and a function in a computational sense, which
is more like a proof of implication.

-}

{-

Task: intuitively, proving that
renType ren₁ (renType ren₂ T) ≡ renType (ren₁ ∘ ren₂) T
is trivial, I understand ren in terms of what is MEANS.

Task: use this idea to prove:
Poly : Type, Poly = List ℕ   standard form coefficients
apply : Poly → ℕ → ℕ
∘ : Poly → Poly → Poly

And then prove,
apply P (apply Q n) ≡ apply (P ∘ Q) n
without syntactic manipulation:

1) prove that elements of poly relate to elements of (ℕ → ℕ)
2) prove that apply relates to application, and ∘ to composition
3) use to trivially derive result.

really should map e.g. ℕ → ℕ' as well

injection:

F a b → F a' b → a ≡ a'
F a b → F a' b →

- sub as constructor
- QIT
- eval goes to shallow
- eval e ≡ eval e' → e ≡ e'
    - can trivially derive β,η equivalence
    - trivial aug shallow param by Type, all normal form, with app constructor
       just requiring equivalence in shallow embedding.
-}
