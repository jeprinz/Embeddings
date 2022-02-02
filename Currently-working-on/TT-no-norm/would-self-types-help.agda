{-

The concept is that self types might help to define renaming.

-}

Ren : Context → Context → Set
Ren Γ₁ Γ₂ = self ren . ∀{T} → Var Γ₁ T → Var Γ₂ (renType ren T)

renVarComm : ∀{Γ₁ Γ₂ Γ₃ n} → {ren₁ : Ren Γ₁ Γ₂} → {ren₂ : Ren Γ₂ Γ₃}
  → {T : Type n Γ₁}
  → {x : Var n Γ₁ T}
  → (renVar ren₂ (renVar ren₁ x           ))           ≡ renVar (ren₁ ∘ ren₂) x
--               {Var Γ₂ (renType ren­₁ T)}
--  {Var Γ₃ (renType ren₂ (renType ren₁ T))}    {Var Γ₃ (renType (ren₁ ∘ ren₂) T)}

_∘_ : ∀{Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
ren₁ ∘ ren₂ = λ x →              ren₂           (ren₁ x)
--              ↑ : Var Γ₁ T                    ↑ Var Γ₂ (renType ren₁ T)
-- Have:                         {Var Γ₃ (renType ren₂ (renType ren₁ T))}
-- Expecting: {Var Γ₃ (renType (ren₁ ∘ ren₂) T)}

SO: EVEN WITH SELF TYPES, renTypeComm must be present in definition of _∘_

renVarComm : ∀{Γ₁ Γ₂ Γ₃ n} → {ren₁ : Ren Γ₁ Γ₂} → {ren₂ : Ren Γ₂ Γ₃}
  → {T : Type n Γ₁}
  → {x : Var n Γ₁ T}
  → ren₂ (ren₁ x)           ≡  (ren₁ ∘ ren₂) x
--               {Var Γ₂ (renType ren­₁ T)}
--  {Var Γ₃ (renType ren₂ (renType ren₁ T))}    {Var Γ₃ (renType (ren₁ ∘ ren₂) T)}
