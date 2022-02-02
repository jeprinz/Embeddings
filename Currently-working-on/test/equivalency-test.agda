{-

I want to define a structure isomorphic to a function space,
and then have another stucture parametrized by, and try to prove things
about it. This is supposed to correspond to proving things about
TT in TT.

-}

record Group : Set₁ where
  field
    S : Set
    _∘_ : S → S → S
    

-- data Group : Set where
--   group : (S : Set)
--     → (_∘_ : )
