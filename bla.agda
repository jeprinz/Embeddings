data A : Set where
  a : A
data B : Set where
  b : B
data C : Set where
  c : C

data Accept : Set → Set₁ where
    acceptA : Accept A
    acceptB : Accept B

acceptSome : {X : Set} → {accept : Accept X} → X → ⊤
acceptSome {_} {acceptA} a = tt
acceptSome {_} {acceptB} b = tt

test1 : ⊤
test1 = acceptSome {_} {acceptA} a

-- doesn't work
-- test1 : ⊤
-- test1 = acceptSome {_} {accept} c
