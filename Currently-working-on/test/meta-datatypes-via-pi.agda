Bool₀ : Set₁
Bool₀ = (P : Set₀) → P → P → P

true₀ : Bool₀
true₀ _ a b = a

false₀ : Bool₀
false₀ _ a b = b

Bool₁ : Bool₀ → Set₂
Bool₁ b = (P : Bool₀ → Set₁) → P true₀ → P false₀ → P b

true₁ : Bool₁ true₀
true₁ _ a b = a

false₁ : Bool₁ false₀
false₁ _ a b = b

not : Bool₀ → Bool₀
not b P p₁ p₂ = b P p₂ p₁

_≡_ : {A : Set₁} → A → A → Set₁
_≡_ {A} a b = (P : A → A → Set₀) → ((x : A) → P x x) → P a b

refl : {A : Set₁} → (a : A) → a ≡ a
refl a P p = p a

-- for all b, not (not b) ≡ b
theorem : {b₀ : Bool₀} → (b₁ : Bool₁ b₀) → not (not b₀) ≡ b₀
theorem b₁ = b₁ (λ b → not (not b) ≡ b) (refl true₀) (refl false₀)
