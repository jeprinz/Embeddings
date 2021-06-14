mutual
  data SemT : Set where
    U : SemT
    Π : (A : SemT) → Sem {! Π A U  !} → SemT

  Sem : SemT → Set
  Sem U = SemT
  Sem (Π A B) = Sem A → {!   !}
