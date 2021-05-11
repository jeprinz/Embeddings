{-# OPTIONS --cumulativity --without-K #-}

open import Data.Product
-- open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Maybe

{-

The following description was the original intent of this file:
------------------------------------------------------------------

The intention of this file is to make a version of Exp and Type
which has normalization (or possible "equivalence" meaning have same normal form)
defined as a RELATION. So that we have a full on deeply embedded type theory.

BUT, it will also be parametrized by it's Agda terms. This way, we can unquote it.
I can then try removing the Agda terms, and seeing if unquoting is possible to define
later on, but somehow I think that that will run into issue.

------------------------------------------------------------------

However, it turns out that this relational approach is very difficult if possible.
The difficulty has nothing to do with the fact that I had things parametrized by
Agda terms, rather it comes from the relational approach to normalization.

Because it is intrinsically typed, in the App constructor, it must make reverence
to the η-equivalance relation. (Or you could have another constructor called
convert which converts between equivalent types). But then, the equivalence
relation must be able to show that terms which are equivalent except for different
equivalence relations are possible...

In the end, it is probably possible. There may even exist a very nice solution.
However, it is not simple.

Consider the following paper on implementing a deep embedding of dependent type
theory in dependent type theory:

"Type Theory in Type Theory using Quotient Inductive Types"
by Thorsten Altenkirch, Ambrus Kaposi
http://www.cs.nott.ac.uk/~psztxa/publ/tt-in-tt.pdf

The following excerpt is talking about the issue I mentioned above (albeit using
category theory language that I don't understand):

"However, it turns out that the overhead in form of type-theoretic boilerplate is
considerable. For example terms depend onboth contexts and types, we have to
include special constructors which formalize the idea that this is a setoid indexed
over two given setoids. Moreover each constructor comes with a congruencerule.
In the end the resulting definition becomes unfeasible, almost impossible to
write down explicitly but even harder to work with in practice."

Their use of Quotient Inductive Types automatically takes care of a bunch of
equivalence stuff, and so avoids the problem. They use some tricks to get QIT's
in Agda, which is fine. What is unclear to me is if they leave holes in the
proof other than the QITs. I have been told by Alex I think that they do. If not,
then this seems like a very compelling embedding.

On second thought, it seems that at the very least the DEFINITION should be
possible without holes. Probably just the normalization proof.

-}

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
mutual
  data Context : Set i → Set j where
    ∅ : Context ⊤
    _,_ : ∀{aΓ} → (Γ : Context aΓ) → {aT : aΓ → Set i}
      → Type Γ aT → Context (Σ {i} {i} aΓ (λ γ → aT γ))

  data Type : ∀{aΓ} → (Γ : Context aΓ) → (aΓ → Set i) → Set j where
    U₀ : ∀{aΓ} → {Γ : Context aΓ} → Type Γ (λ _ → Set₀)
    U₁ : ∀{aΓ} → {Γ : Context aΓ} → Type Γ (λ _ → Set₁)
    Π : ∀{aΓ aA aB} → {Γ : Context aΓ} → (A : Type Γ aA) → (B : Type (Γ , A) aB)
      → Type Γ (λ γ → (a : aA γ) → aB (γ , a))
    fromExp : ∀{aΓ a} → {Γ : Context aΓ} → Exp Γ U₀ a → Type Γ a
    _[_] : ∀{aΓ aA at aa} → {Γ : Context aΓ}
      → {A : Type Γ aA} → Type (Γ , A) at → Exp Γ A aa
      → Type Γ (λ γ → at (γ , aa γ))
    Weaken : ∀{aΓ aA aT} → {Γ : Context aΓ} → {A : Type Γ aA} → Type Γ aT → Type (Γ , A) (λ γ → aT (proj₁ γ))

  data Exp : ∀{aΓ} → (Γ : Context aΓ) → ∀{aT} → (T : Type Γ aT) → ((γ : aΓ) → aT γ) → Set j where
    Lambda : ∀{aΓ aA aB} → {Γ : Context aΓ} → {A : Type Γ aA} → {B : Type (Γ , A) aB} → ∀{ae}
      → Exp (Γ , A) B ae → Exp Γ (Π A B) (λ γ → λ a → ae (γ , a))
    App : ∀{aΓ aA aB} → {Γ : Context aΓ} → {A : Type Γ aA} → {B : Type (Γ , A) aB} → ∀{af aa}
      → (f : Exp Γ (Π A B) af) → (a : Exp Γ A aa)
      → ∀{T} → TypeEquivalent (B [ a ]) T
      → Exp Γ T (λ γ → af γ (aa γ))
    fromT₀ : ∀{aΓ} → {Γ : Context aΓ} → {a : aΓ → Set}
      → Type Γ a → Exp Γ U₀ a
    Var : ∀{aΓ aT} → {Γ : Context aΓ} → {T : Type Γ aT} → (icx : InCtx Γ T)
      → Exp Γ T (proja icx)
    _[_] : ∀{aΓ aA aB a₁ a₂} → {Γ : Context aΓ}
      → {A : Type Γ aA} → {B : Type (Γ , A) aB}
      → Exp (Γ , A) B a₁ → (a : Exp Γ A a₂)
      → Exp Γ (B [ a ]) (λ γ → a₁ (γ , a₂ γ))
    convert : ∀{aΓ aT a} → {Γ : Context aΓ} → {A B : Type Γ aT}
      → Exp Γ A a → TypeEquivalent A B
      → Exp Γ B a

  data InCtx : ∀{aΓ} → (Γ : Context aΓ) → {aT : aΓ → Set i}
    → Type Γ aT → Set j where
    same : ∀{aΓ aT} → {Γ : Context aΓ} → {T : Type Γ aT} → InCtx (Γ , T) (Weaken T)
    next : ∀{aΓ aT aA} → {Γ : Context aΓ} → {T : Type Γ aT} → {A : Type Γ aA}
      → InCtx Γ A → InCtx (Γ , T) (Weaken A)

  proja : ∀{aΓ aT} → {Γ : Context aΓ} → {T : Type Γ aT}
    → (icx : InCtx Γ T) → (γ : aΓ) → aT γ
  proja same (γ , t) = t
  proja (next icx) (γ , _) = proja icx γ

  data TypeEquivalent : ∀{aΓ aT} → {Γ : Context aΓ} → Type Γ aT → Type Γ aT → Set j where
    reflexivity : ∀{aΓ aT Γ T} → TypeEquivalent {aΓ} {aT} {Γ} T T
    -- rules for sub passing through each constructor

  data ExpEquivalent : ∀{aΓ aT a} → {Γ : Context aΓ} → {T : Type Γ aT}
    → Exp Γ T a → Exp Γ T a → Set j where
    β : ∀{aΓ aA aB a₁ a₂} → {Γ : Context aΓ}
      → (A : Type Γ aA) → (B : Type (Γ , A) aB)
      → (e₁ : Exp (Γ , A) B a₁) → (e₂ : Exp Γ A a₂)
      → ExpEquivalent (App (Lambda e₁) e₂ reflexivity ) (e₁ [ e₂ ])
    fromCancel : ∀{aΓ a} → {Γ : Context aΓ}
      → (e : Exp Γ U₀ a)
      → ExpEquivalent e (fromT₀ (fromExp e))
    convert : ∀{aΓ aT a} → {Γ : Context aΓ} → {A B : Type Γ aT}
      → (e₁ e₂ : Exp Γ A a) → ExpEquivalent e₁ e₂
      → {eq₁ : TypeEquivalent A B} → {eq₂ : TypeEquivalent B C}
      → ExpEquivalent (convert e₁ eq₁) (convert e₂ eq₂)

    -- If two Apps are made with different TypeEquivalent proofs, doesn't matter.
    appEquivCancel : ∀{aΓ aA aB a₁ a₂} → {Γ : Context aΓ} → {A : Type Γ aA}
      → {B : Type (Γ , A) aB} → {T : Type Γ (λ γ → aB (γ , a₂ γ))}
      → (e₁ : Exp Γ (Π A B) a₁) → (e₂ : Exp Γ A a₂)
      → ∀{eq₁ eq₂}
      → ExpEquivalent (App e₁ e₂ {T} eq₁) (App e₁ e₂ {T} eq₂)
    -- rules for passing subs through apps, vars, lambdas, etc
    -- rule for η reduction
    -- subApp : ∀{aΓ aT aA aB a₁ a₂} → {Γ : Context aΓ}
    --   → {S : Type Γ aT} → {A : Type (Γ , S) aA}
    --   → {B : Type ((Γ , S) , A) aB} → {T : Type (Γ , S) (λ γ → aB (γ , a₂ γ))}
    --   → (e₁ : Exp (Γ , S) (Π A B) a₁) → (e₂ : Exp (Γ , S) A a₂)
    --   → (e : Exp Γ ? ?)
    --   → ∀{eq}
    --   → ExpEquivalent ((App e₁ e₂ {T} eq) [ e ]) ((App (e₁ [ e ]) (e₂ [ e ])))
    -- IDEA: in order to make the above idea go through, need an ExpEquivalent
    -- constructor which makes subs commute. Basically, pass sub through sub.
    -- ALso, obviously we need more general subs, and App either needs to convert
    -- on input, or sub converts on output, or we just add convert constructor.


{-

Before I go any further: is this really going to work out?
The App constructor has ExpEquivalent in it. So would we need equivalences
on equivalences?

An alternate approach to all of this is to have the following type:

data NormalizesTo : ∀{aΓ aT a} → {Γ : Context aΓ} → {T : Type Γ aT}
  → Exp Γ T a → Nf Γ T a → Set j where

And basically, I define normalization as a function, except that its a relation
so I don't actually have to prove anything about termination.

So then, I need a substitution relation as well.
And for that, I don't need Exp, only Nf actually. Instead of NormalizesTo, I would have
SubsTo, and AppsTo   which does applications of normal forms.

Is that exactly as hard as a functional version with termination checking off?
For some reason that was hard, and I'm struggling to remember why.
Subs commuting?
Is it when subbing under an App?
If App constuctor has NormalizesTo in it then,
Need to show that    NormalizesTo (P a) T   →   NormalizesTo  ((P a) [x ↦ e]) T [x ↦ e]
VS
NormTo (P a) T → SubTo (P a) sub Pa' → SubTo T sub T' → NormalizesTo Pa' T'
or in functional style,
(normalize (P a)) [x ↦ e] ≡ (normalize ((P a) [x ↦ e]))

This leads to
e[x ↦ a] [y ↦ b] ≡ e [y ↦ b] [x ↦ a]
OR
SubsTo e a e'  → SubsTo e' b e'' → Σ e'''  SubsTo e b e''' ×  SubsTo e''' a e''

But, in a relational style, why do i actually need to prove this?
-- App constructor of SubsTo.

App : (p : NormalizesTo (B e₂) B')
  SubsTo sub e₁ e₁' → SubsTo sub e₂ e₂' → SubsTo sub (App e₁ e₂ p) (App e₁' e₂' ??????)

-}

-- think about the above next time. I think that this point is exactly whats hard about
-- a deep embedding of dependent type theory, even if not trying to prove normalization.
-- So if I'm going to make a hybrid shallow-deep embedding, this is exactly the thing I
-- need to bypass with agda normalizaiton instead of defined normalization.

-- But do I still need to do sub commute in the sub through App case
-- even in equivalance design?
