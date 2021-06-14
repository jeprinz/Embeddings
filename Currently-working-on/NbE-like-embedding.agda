{-

If the NbE embedding is possible, then why can't I have in addition to standard
Exp, also Type : Context → (aΓ → Set i) → Set j
and stuff like SemΠ can just be output of
Sem : ∀{} → Type Γ → Set j

In other words, we have data Type (parametrized by its agda type),
but Exp is still parametrized by Agda types and values.

...  Not sure this really works, work on NbE-embedding-test for now...

-}
