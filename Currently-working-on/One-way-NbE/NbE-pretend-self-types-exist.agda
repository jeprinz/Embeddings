{-

This file is not actually valid agda. The idea is to pretend that I have
self types and see what I can do.

-}

data Context : Set₁ -- where
data SemT : (Γ : Context) → Set₁ -- where
data Sem : (Γ : Context) → SemT Γ → Set₁ -- where

data Context where
  ∅ : Context
  _,_ : (Γ : Context) → SemT Γ → Context

data Var : (Γ : Context) → (T : SemT Γ) → Sem Γ T → Set₁ where
  -- same : ∀{n SΓ} → {T : Type n SΓ} → {Γ : Context SΓ}
  --   → Var {n} (Γ , T) (λ γ → T (proj₁ γ)) proj₂
  -- next : ∀{n m SΓ Γ A a} → {T : Type n SΓ} → Var {m} {SΓ} Γ A a
  --   → Var (Γ , T) (λ γ → A (proj₁ γ)) (λ γ → a (proj₁ γ))

Ren : Context → Context → Set₁
Ren Γ₁ Γ₂ = Self (ren : Ren Γ₁ Γ₂)
  . ∀{T} → VarT Γ₁ T t → VarT Γ₂ (renType ren T) (renTerm ren t))

idRen : ∀{Γ} → Ren Γ Γ
idRen Γ₁ Γ₂ = self ren . λ x
  → transport (proof that renType idRen T ≡ T) (proof that renTerm idRen T ≡ T) x

↑ this shows the problem. Even with self types, I still need to prove dumb stuff
like that idRen T = T. Whereas, with shallow approaches, that is not necessary.

-- Eforget1ren : ∀{n sΓ₁ sΓ₂ T} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
--   → ERen sub Γ₁ Γ₂ → ERen (forget1ren {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , subType sub T)
-- Eforget1ren ren same = same
-- Eforget1ren ren (next x) = next (ren x)

-- Eweaken1Ren : ∀{sΓ Γ n T} → ERen {sΓ} (weaken1Ren {sΓ} {n} {T}) Γ (Γ , T)
-- Eweaken1Ren = next

------------------- Normal form augmented "shallow" embedding ------------------

data Ne : (Γ : Context) → (T : SemT Γ) → Sem Γ T → Set₁ where
  -- Evar : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → {a : Term SΓ T}
  --   → (icx : Var Γ T a) → Ne {n} {SΓ} Γ T a
  -- Eapp : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
  --     → {B : Type (suc n) (cons SΓ A)} → ∀{a₁ a₂}
  --     → Ne {suc n} Γ (SΠ A B) a₁ → (x : Nf {suc n} Γ A a₂)
  --     → Ne {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sapp {n} {SΓ} {A} {B} a₁ a₂)
  -- EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
  --   → Ne Γ T a → Ne Γ (ScumuT T) (Scumu {n} {_} {T} a)
  -- unCumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
  --   → Ne Γ (ScumuT T) (Scumu {n} {_} {T} a) → Ne Γ T a

data Nf : (Γ : Context) → (T : SemT Γ) → Sem Γ T → Set₁ where
  -- Elambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Type (suc n) SΓ}
  --   → {B : Type (suc n) (cons SΓ A)} → ∀{a}
  --   → Nf (Γ , A) B a → Nf Γ (SΠ A B) (Slambda {n} {SΓ} {A} {B} a)
  -- EcumuValue : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ} → ∀{a}
  --   → Nf Γ T a → Nf Γ (ScumuT T) (Scumu {n} {_} {T} a)
  -- -- NOTE: does EcumuValue go in Nf, Ne, or both?
  -- fromNe : ∀{n SΓ Γ T t} → Ne {n} {SΓ} Γ T t → Nf Γ T t
  -- -- only when of type (Ne e)... need to have Shallow embedding
  -- -- split into Ne, Nf, Type. Instead of just Type, Term.
  -- fromType : ∀{n SΓ Γ T} → EType {n} {SΓ} Γ T → Nf {suc n} Γ SU T


data EType : (Γ : Context) → (T : SemT Γ) → Set₁ where
  -- EΠ : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {a₁ : Term SΓ (SU {suc n})}
  --   → {a₂ : Type (suc n) (cons SΓ a₁)} → (A : EType Γ a₁)
  --   → (B : EType (Γ , a₁) a₂)
  --   → EType Γ (SΠ {n} a₁ a₂)
  -- EU : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → EType {suc n} {SΓ} Γ SU
  -- Ecumu : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
  --   → EType {n} Γ a → EType Γ (ScumuT a)
  -- fromNe : ∀{n SΓ Γ T} → Ne {suc n} {SΓ} Γ SU T → EType Γ T

-- renNe : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  -- → ERen sub Γ₁ Γ₂ → Ne {n} Γ₁ T t → Ne Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)
-- renNe ren (Evar x) = Evar (ren x)
-- renNe ren (Eapp e₁ e₂) = Eapp (renNe ren e₁) (renNf ren e₂)
-- renNe ren (EcumuValue e) = EcumuValue (renNe ren e)
-- renNe ren (unCumu e) = unCumu (renNe ren e)

-- renNf : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  -- → ERen sub Γ₁ Γ₂ → Nf {n} Γ₁ T t → Nf Γ₂ (subType sub T) (subExp {_} {_} {_} {T} sub t)
-- renNf ren (Elambda e) = Elambda (renNf (Eforget1ren ren) e)
-- renNf ren (EcumuValue e) = EcumuValue (renNf ren e)
-- renNf ren (fromNe e) = fromNe (renNe ren e)
-- renNf ren (fromType T) = fromType (renEType ren T)

-- renEType : ∀{n sΓ₁ sΓ₂ T} → {sub : Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  -- → ERen sub Γ₁ Γ₂ → EType {n} Γ₁ T → EType Γ₂ (subType sub T)
-- renEType ren (EΠ A B) = EΠ (renEType ren A) (renEType (Eforget1ren ren) B)
-- renEType ren EU = EU
-- renEType ren (Ecumu e) = Ecumu (renEType ren e)
-- renEType ren (fromNe e) = fromNe (renNe ren e)

data SemT where
  EU : {Γ : Context} → SemT Γ
  fromNe : ∀{Γ T} → Ne Γ EU T → SemT Γ
  -- Ecumu : {SΓ : Ctx} → {Γ : Context SΓ} → ∀{a}
  --   → ESemTn Γ a → SemT Γ (ScumuT a)
  -- EΠ : {SΓ : Ctx} → {Γ : Context SΓ}
  --   → {a₁ : Term SΓ (SU {suc n})}
  --   → {a₂ : Type (suc n) (cons SΓ a₁)}
  --   → (A : ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → ERen ren Γ Γ' → SemT Γ' (subType ren a₁))
  --   → (B : ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → (eren : ERen ren Γ Γ') → ∀{a}
  --       → Sem Γ' (subType ren a₁) a (A eren)
  --       → SemT Γ' (subType (append1sub' a₁ ren a) a₂))
  --   → SemT Γ (SΠ {n} a₁ a₂)

data Sem where
-- Sem Γ ST St EU = ESemTn Γ St
-- Sem Γ ST St (fromNe e) = Nf Γ ST St -- NOTE: if Ne is parametrized specifically by Ne in SHALLOW embedding, then that will help here later...
-- Sem Γ ST St (Ecumu T) = ESemn Γ _ St T
-- Sem {SΓ} Γ ST St (EΠ {_} {_} {SA} {SB} A B)
--   = ∀{SΓ' Γ'} → {ren : Sub SΓ SΓ'} → (eren : ERen ren Γ Γ') → ∀{Sa}
--     → (a : Sem Γ' _ Sa (A eren))
--       → Sem Γ' _ (λ γ → St (ren γ) (Sa γ)) (B eren a)
