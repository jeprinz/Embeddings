data Context : Set -- where
  ∅ : Context
  _,_ : (Γ : Context) → SemT Γ → Context

-- Γ' > Γ means that Γ' is stronger than Γ
-- (AKA Γ' is like Γ but with more stuff added in)

idRen : ∀{Γ} → Ren Γ Γ
weaken1Ren : ∀{Γ T} → Ren Γ (Γ , T)

-- if Γ' > Γ , then SemT Γ ⊆ SemT Γ'
data SemT : Context → Set -- where
  U : ∀{Γ} → SemT Γ
  Π : ∀{Γ} → (A : SemT Γ)
    → (B : ∀{Γ' > Γ} → Sem Γ' A → SemT Γ')
    → SemT Γ
  fromNe : ∀{Γ} → Ne Γ U → SemT Γ

-- if Γ' > Γ , then Sem Γ T ⊆ Sem Γ' T
Sem : (Γ : Context) → SemT Γ → Set
Sem Γ U = SemT Γ
Sem Γ (Π A B) = (a : Sem Γ A) → Sem Γ (B a)
Sem Γ (fromNe e) = Nf Γ (fromNe e)

Var : (Γ : Context) → SemT Γ → Set

data Nf : (Γ : Context) → SemT Γ → Set where
data Ne : (Γ : Context) → SemT Γ → Set where
  var : ∀{Γ T} → Var Γ T → Ne Γ T

data Term : (Γ : Context) → SemT Γ → Set -- where
  var : ∀{Γ T} → Var Γ T → Term Γ T
  lambda : ∀{Γ} → {A : SemT Γ}
    → {B : ∀{Γ' > Γ} → Sem Γ' A → SemT Γ'}
    → Term (Γ , A) (B (reflect (var 0)))
    → Term Γ (Π A B)

Ren : Context → Context → Set
Sub : Context → Context → Set

reflect : ∀{Γ T} → Ne Γ T → Sem Γ T

reify : ∀{Γ T} → Sem Γ T → Nf Γ T

eval : ∀{Γ₁ Γ₂ T} → (sub : Sub Γ₁ Γ₂) → Term Γ₁ T → Sem Γ₂ sub(T)
eval sub (var x) = sub(x)
eval sub (lambda e) = λ a → eval e (append1sub (transSR sub ren) a)
