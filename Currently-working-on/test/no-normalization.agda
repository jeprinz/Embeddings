
data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  z : ∀{n} → Z + n ≡ n
  s : ∀{a b c} → a + b ≡ c → (S a) + b ≡ S c

plus : ℕ → ℕ → ℕ
plus Z n = n
plus (S n) m = S (plus n m)

pplus : ∀{n m} → n + m ≡ plus n m
pplus {Z} = z
pplus {S n} = s pplus

{-# NON_TERMINATING #-} -- this just makes Agda not normalize the function.
+-z : ∀{n} → n + Z ≡ n
+-z {Z} = z
+-z {S n} = s +-z

{-# NON_TERMINATING #-} -- this just makes Agda not normalize the function.
+-s : ∀{a b c} → a + b ≡ c → a + (S b) ≡ S c
+-s z = z
+-s (s r) = s (+-s r)

{-# NON_TERMINATING #-} -- this just makes Agda not normalize the function.
+-comm : ∀{a b c} → a + b ≡ c → b + a ≡ c
+-comm z = +-z
+-comm (s r) = +-s (+-comm r)

-- TODO: what even is the correct statement here? I should probably define what a function
-- (in a relational sense) is and prove that + is a function.
+-assoc : ∀{a b c ab bc abc} → a + b ≡ ab → ab + c ≡ abc → b + c ≡ bc → a + bc ≡ abc
+-assoc {.Z} {b} {c} z r2 r3 = {!   !}
+-assoc {.(S _)} {b} {c} (s r1) r2 r3 = {!   !}

data Function {A B : Set} (F : A → B → Set) : Set where
  fun : (f : A → B) → ((a : A) → F a (f a)) → Function F
-- Function {A} {B} f = {! (a : A) → Σ  !}

compose : {A B C : Set} → (F : A → B → Set) → Function F
  → (G : B → C → Set) → (A → C → Set)
compose F (fun f x) G a c = G (f a) c

Compose : {A B C : Set} → {F : A → B → Set} → {G : B → C → Set}
  → (f : Function F) → (g : Function G) → Function (compose _ f G)
Compose {_} {_} {_} {F} {G} (fun f pf) (fun g pg)
  = fun (λ a → g (f a)) (λ a → pg (f a))
  -- TODO: don't use pf anywhere?

data Function2 {A B C : Set} (F : A → B → C → Set) : Set where
  fun : (f : A → B → C) → ((a : A) → (b : B) → F a b (f a b)) → Function2 F

+-Func : Function2 _+_≡_
+-Func = fun plus λ a b → pplus

-- apply : ∀{A B} → (F : A → B → Set) → Function F → A → B

data _==_ : {X : Set} → X → X → Set where
  refl : ∀{X x} → _==_ {X} x x

ap : {A B : Set} → (f : A → B) → {a₁ a₂ : A} → a₁ == a₂ → f a₁ == f a₂
ap f refl = refl

+-assoc' : ∀{a b c} → plus (plus a b) c == plus a (plus b c)
+-assoc' {Z} {b} {c} = refl
+-assoc' {S a} {b} {c} = ap S (+-assoc' {a} {b} {c})

data Vec : Set → ℕ → Set where
  ∅ : ∀{T} → Vec T Z
  _,_ : ∀{T n} → T → Vec T n → Vec T (S n)

infixl 10 _,_

data append : ∀{T a b c}
  → a + b ≡ c
  → Vec T a → Vec T b → Vec T c → Set where
  z : ∀{T n} → {v : Vec T n} → append z ∅ v v
  s : ∀{T a b c r t} → {v₁ : Vec T a} → {v₂ : Vec T b} → {v₃ : Vec T c}
      → append r v₁ v₂ v₃
      → append (s r) (t , v₁) v₂ (t , v₃)

{-

Want to prove that
renType ren₁ (renType ren₂ T) = renType (ren₁ ∘ ren₂) T

This is obvious is think of types as functions from context to "type"
Γ → Type
A function A → B is:
(A → B)
subset of A × B
relation A → B → Set

-}

Ctx = Set
Type : Ctx → Set₁
Type Γ = Γ → Set

Type' : Ctx → Set₁
Type' Γ = Γ → Set → Set


{-

General theory of type theory, without giving a special meaning to equality:

- Set of contexts, types, terms
- Predicates of sub (hereditary) and app (multi-arg)
- Predicates of Γ⊢_:_, Γ⊢_:U
- Predicates of
- Proof that all predicates hold

-}
