{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Maybe
open import Function

BinRel : ∀{i j} → (A : Set i) → (B : A → Set j) → Set (lsuc (i ⊔ j))
BinRel {i} {j} A B = (a : A) → B a → Set (i ⊔ j)

Functional : ∀{i j A B} → BinRel {i} {j} A B → Set (lsuc (i ⊔ j))
Functional f = {!   !}

-- data SET (l : Level) : Set (lsuc l) where
  -- set : {T : Set l} → (T → SET l) → SET l

-- represents a Set of elements of A
data SETof (l : Level) (A : Set l) : Set (lsuc l) where
  set : {T : Set l} → (T → A) → SETof l A

module sucn (SETn : Set) (eln : SETn → Set) where
  data SETsucn : Set where
    set : {T : SETn} → (eln T → SETsucn) → SETsucn

  elsucn : SETsucn → Set
  elsucn (set {T} x) = {! Σ (eln T) !}

_∼_ : ∀{l} → {A : Set l} → {B : A → Set l}
  → (f g : (a : A) → B a) → Set l
f ∼ g = (a : _) → f a ≡ g a

isEquiv : ∀{l} → {A : Set l} → {B : Set l}
  → (A → B) → Set l
isEquiv {l} {A} {B} f
  = (Σ (B → A) (λ g → (g ∘ f) ∼ id))
    × Σ (B → A) (λ h → (f ∘ h) ∼ id)

_≃_ : ∀{l} → Set l → Set l → Set l
A ≃ B = Σ (A → B) isEquiv

leibniz : ∀{l} → (A : Set l) → A → A → Set (lsuc l)
leibniz {l} A x y = (P : A → A → Set l) → ((a : A) → P a a) → P x y
--                                                     ↑ ↑

loobnoz : ∀{l} → (A B : Set l) → Set (lsuc l)
loobnoz {l} A B = (P : Set l → Set l → Set l)
  → ((X Y : Set l) → X ≃ Y → P X Y)
  → P A B

id∼ : ∀{l} → {A : Set l} → {B : A → Set l}
  → {f : (a : A) → B a} → f ∼ f
id∼ = λ a → refl

id≃ : ∀{l} → {A : Set l} → A ≃ A
id≃ = id , (id , id∼) , (id , id∼)

roofl : ∀{l} → (A : Set l) → loobnoz A A
roofl A = λ P x → x A A id≃

fact : {n m : ℕ} → just n ≡ just m → n ≡ m
fact refl = {!   !}
