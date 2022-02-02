open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

lem1 : (n : ℕ) → n ≡ n + zero
lem1 zero = refl
lem1 (suc n) = cong suc (lem1 n)

lem2 : (a b : ℕ) → (a + suc b) ≡ suc (a + b)
lem2 zero b = refl
lem2 (suc a) b = cong suc (lem2 a b)

comm : (a b : ℕ) → a + b ≡ b + a
comm zero b = lem1 b
comm (suc a) b = trans (cong suc (comm a b)) (sym (lem2 b a))

assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
assoc zero b c = refl
assoc (suc a) b c = cong suc (assoc a b c)

data plus : ℕ → ℕ → ℕ → Set where
  zero : ∀{n} → plus zero n n
  suc : ∀{a b c} → plus a b c → plus (suc a) b (suc c)

lem1r : ∀{n} → plus n zero n
lem1r {zero} = zero
lem1r {suc n} = suc lem1r

lem2r : ∀{a b c} → plus a b c → plus a (suc b) (suc c)
lem2r zero = zero
lem2r (suc p) = suc (lem2r p)

commr : ∀{a b c} → plus a b c → plus b a c
commr zero = lem1r
commr (suc p) = lem2r (commr p)

Fun : {A B : Set} → (A → B → Set) → Set
Fun {A} {B} R = (a : A) → Σ B (λ b → R a b)

Fun2 : {A B C : Set} → (A → B → C → Set) → Set
Fun2 {A} {B} {C} R = (a : A) → (b : B) → Σ C (λ c → R a b c)

rel+ : ∀{a b} → plus a b (a + b)
rel+ {zero} {b} = zero
rel+ {suc a} {b} = suc rel+

_∘1_ : {A : Set}
  → (F : A → A → Set)
  → (G : A → A → Set)
  → (A → A → Set)
_∘1_ {A} F G x y = Σ A (λ z → G x z × F z y)

-- if get really fancy, build a little DSL where you can make expressions like
-- f 1 (g 3 4) 5 = h 3, but it really is working with relations.

-- another property of being a function
wfplus : ∀{a b c d} → plus a b c → plus a b d → c ≡ d
wfplus zero zero = refl
wfplus (suc p1) (suc p2) = cong suc (wfplus p1 p2)


plusFun2 : Fun2 plus
plusFun2 a b = a + b , rel+

-- Idea is that can use relational techniques to prove properties about
-- functions which may be partial or not computable.
-- So this is wrong, because it requires you to compute b+c.
-- assocr : (a b c x sum : ℕ)
--   → plus a b x
--   → plus x c sum
--   → Σ ℕ (λ y →
--     (plus a y sum) × (plus b c y))

assocr : (a b c p1 p2 sum : ℕ)
  → plus a b p1
  → plus p1 c sum
  → plus b c p2
  → plus a p2 sum
assocr .0 b c .b p2 sum zero r2 r3 = {! wfplus r2 r3  !}
assocr .(suc _) b c .(suc _) p2 sum (suc r1) r2 r3 = {!   !}

-- should be able to reason about non computable functions
-- halt (p1 ; p2) = (halt p1) and (halt p2)

{-

Idea: relational style prevents the need for annoying transports.
To test, find a proof that can only be done with annoying transports,
and do it in a relational style.

Idea 2 (could be complete nonsense):
In relational style, parametricity does what univalence does in
function+equality style.

-}
