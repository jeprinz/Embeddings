open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product

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

-- data Ctx : Set → Set₁ where
--   ∅ : Ctx ⊤
--   _,_ : ∀{n sΓ} → (Γ : Ctx sΓ) → (T : sΓ → SemT n) → Ctx (Σ sΓ (λ γ → Sem n (T γ)))
--   -- doesn't feel right, not equivalent to how Π constructor above works!

data Ctx : Set where -- reversed from normal?
  ∅ : Ctx
  _,_ : ∀{n} → (T : SemT n) → (Sem n T → Ctx) → Ctx

test : ∀{n} → SemT n → {!   !}
test {suc n} U = {!   !}
test {suc zero} (Π U B) = {!   !}
test {suc zero} (Π (Π A x) B) = {!   !}
test {suc (suc n)} (Π U B) with B U
... | U = {!   !}
... | Π res x = {!   !}
... | cumu res = {!   !}
test {suc (suc n)} (Π (Π A x) B) with B {!   !}
... | res = {!   !}
test {suc (suc n)} (Π (cumu x) B) with B {!   !}
... | res = {!   !}
test {suc (suc n)} (cumu x) = {! x  !}
