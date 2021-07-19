{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --without-K #-} -- This uses axiom K! Can't uncomment this!

{-

Derivation that type-in-type leads to contradiction, using Godel's second theorem.
This uses an inductive type as well as Axiom K, so it is not a very general
proof.

-}

data ⊥ : Set where
¬_ : Set → Set
¬ T = T → ⊥

data SelfProv : (A : Set) → A → Set where
  selfProv : (P : (A : Set) → A → Set) → P _ P → SelfProv _ P

G : Set
G = SelfProv _ (λ A a → ¬ SelfProv A a)

lemma1 : G → ¬ G
lemma1 (selfProv .(λ A a → SelfProv A a → ⊥) x) = x

lemma2 : ¬ G → G
lemma2 g = selfProv _ g

ng : ¬ G
ng g = (lemma1 g) g

contradiction : ⊥
contradiction = ng (lemma2 ng)

{-

Godel's second theorem states that a system which can prove it's own consistency
is inconsistent.

More specifically, Godel's second theorem says that if a system has a
particular kind of provability predicate AND can prove a particular statement
about that predicate representing consistency, then the system is inconsistent.

Here, consider L = (Σ Set (λ X → X)). This is the language's representation of
itself. (If not for type-in-type, it would only represent a fragment of itself.)
Instead of directly defining prov : L → Set, I define SelfProv, which
inputs an element of L, and
SelfProv l = prov (l l)

I am then able to construct the G scentence from Godel's theorem, and derive
the contradiction.


-}
