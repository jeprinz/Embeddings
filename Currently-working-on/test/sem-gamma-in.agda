-- Is there a middle groud between putting Γ in and out of Sem?

Ctx = Set

mutual
  data SemT : Ctx → Set where
    U : ∀{Γ} → SemT Γ
    Π : ∀{Γ} → (A : SemT Γ) → (B : )

  -- asFunc : ∀{Γ} → SemT Γ → (Γ → )
