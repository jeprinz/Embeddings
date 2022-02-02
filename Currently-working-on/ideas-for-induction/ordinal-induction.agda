{-
One way to do induction, which is how set theorists do it, is to do it for
ordinals and then derive induction on other structures from that.
-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality

ℕ' : Set₁
ℕ' = (X : Set) → X → (X → X) → X

zero' : ℕ'
zero' X z s = z

suc' : ℕ' → ℕ'
suc' n X z s = s (n X z s)

Tree : Set₁
Tree = (X : Set) → X → (X → X → X) → X

leaf : Tree
leaf X l b = l

branch : Tree → Tree → Tree
branch t₁ t₂ X l b = b (t₁ X l b) (t₂ X l b)

indℕ' : (P : ℕ' → Set) → P zero' → ((n : ℕ') → P n → P (suc' n)) → (n : ℕ') → P n
indℕ' = {!   !}

-- Is it possible to derive indTree from indℕ, by inducting on the depth of
-- the tree? This is how mathematicians often describe induction, is by inducting
-- on the ordinal which results from "squashing" a partial order into a total order.

max : ℕ → ℕ → ℕ
max zero    n       = n
max m       zero    = m
max (suc m) (suc n) = suc (max m n)

depth : Tree → ℕ
depth t = t ℕ 0 max

indℕ : ∀{l} → (n : ℕ)
  → (P : ℕ → Set l) → P zero → ((n : ℕ) → P n → P (suc n)) → P n
indℕ zero P z s = z
indℕ (suc n) P z s = s n (indℕ n P z s)

indSpecTree : Tree → Set₁
indSpecTree t = (P : Tree → Set) → P leaf
  → ((t₁ t₂ : Tree) → P t₁ → P t₂ → P (branch t₁ t₂))
  → P t

indLeaf : indSpecTree leaf
indLeaf P l b = l

indBranch : ∀{t₁ t₂} → indSpecTree t₁ → indSpecTree t₂
  → indSpecTree (branch t₁ t₂)
indBranch {t₁} {t₂} i₁ i₂ P l b = b t₁ t₂ (i₁ P l b) (i₂ P l b)

lemma : ∀{t} → depth t ≡ 0 → t ≡ leaf
lemma {t} p = {! t  !}

indTreeImpl : (d : ℕ) → (t : Tree) → depth t ≡ d
  → (P : Tree → Set)
  → P leaf
  → ((t₁ t₂ : Tree) → P t₁ → P t₂ → P (branch t₁ t₂))
  → P t
indTreeImpl zero t p P l b = {! t  !}
indTreeImpl (suc d) t p P l b = {!   !}

indTree : (t : Tree)
  → (P : Tree → Set)
  → P leaf
  → ((t₁ t₂ : Tree) → P t₁ → P t₂ → P (branch t₁ t₂))
  → P t
indTree t
  = {! indℕ (depth t) ? ? ?  !}
  -- = indℕ (depth t) {!   !} {!   !} {!   !}
