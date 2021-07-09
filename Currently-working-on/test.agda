open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product renaming (Σ to Σbi) -- bi stands for built-in
open import Data.List

data SemTzero : Set where
Semzero : SemTzero → Set
Semzero ()

module sucn (SemTn : Set) (Semn : SemTn → Set) where
  mutual
    data SemTsucn : Set where
        U : SemTsucn
        Π : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        Σ : (A : SemTsucn) → (Semsucn A → SemTsucn) → SemTsucn
        cumu : SemTn → SemTsucn

    Semsucn : SemTsucn → Set
    Semsucn U = SemTn
    Semsucn (Π A B) = (a : Semsucn A) → Semsucn (B a)
    Semsucn (Σ A B) = Σbi (Semsucn A) (λ a → Semsucn (B a))
    Semsucn (cumu T) = Semn T

open sucn

mutual
  SemT : ℕ → Set
  SemT zero = SemTzero
  SemT (suc n) = sucn.SemTsucn (SemT n) (Sem n)

  Sem : (n : ℕ) → SemT n → Set
  Sem zero T = Semzero T
  Sem (suc n) T = sucn.Semsucn _ _ T

U' : (n : ℕ) → SemT (suc n)
U' zero = U
U' (suc n) = U

-- what level context?
data Exp : ∀{n} → SemT n → Set where
  -- lambda : {Γ A B} → Exp (Π (Σ Γ A) B) → {!   !}
  lambda : ∀{n} → {Γ : SemT (suc n)}
    → {A : Sem (suc n) Γ → SemT (suc n)}
    -- → {A : Sem (suc n) (Π Γ (λ _ → U))}
    → {B : Sem (suc n) (Σ Γ A) → SemT (suc n)}
    → Exp (Π (Σ Γ A) B) → Exp (Π Γ (λ γ → Π (A γ) (λ a → B (γ , a))))
  -- cumu : ∀{n} → {Γ : SemT (suc n)} → {T : Sem ()}
  -- lam2 : ∀{n} → {A : SemT (suc n)} → {B : Sem (suc n) A → SemT (suc n)} →

eval : ∀{n} → {T : SemT n} → Exp T → Sem n T
eval (lambda e) = λ f → λ a → eval e (f , a)

-- reify : ∀{n} → (T : SemT n) → Sem n T → Exp T
-- reify {suc n} U e = {!   !}
-- reify {suc n} (Π A B) e = {! B  !}
-- reify {suc n} (Σ T₁ x) e = {!   !}
-- reify {suc n} (cumu x) e = {!   !}

reify : ∀{n} → (Γ : SemT (suc n)) → (T : Sem (suc n) Γ → SemT (suc n))
  → Sem (suc n) (Π Γ T) → Exp (Π Γ T)
reify Γ T e = {! Γ  !}
