open import Grammar
open import Base
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Sum.Base using (_⊎_)
open import Data.Product

module SubPaths where
  data _⊏_ : path → path → Set where
    base : (p : path) → (f : kt-property-name) → p ⊏ (p ∙ f)
    rec : (p₁ p₂ : path) → (f : kt-property-name) → p₁ ⊏ p₂ → p₁ ⊏ (p₂ ∙ f)

  data _⊑_ : path → path → Set where
    less : {p₁ p₂ : path} → p₁ ⊏ p₂ → p₁ ⊑ p₂
    equal : {p₁ p₂ : path} → p₁ ≡ p₂ → p₁ ⊑ p₂


  -- TODO: need to branch on ⊑, need to add decidability for ≡ and ⊏
  _⊖_ : Ctx → path → Ctx
  [] ⊖ p = []
  (d ∷ Δ) ⊖ p = {!   !}

  _[_↦_] : Ctx → path → (α × β) → Ctx
  Δ [ p ↦ αₚ , βₚ ] with Δ ∖ p
  ... | Δ' = (p ∶ αₚ * βₚ) ∷ Δ'

  -- TODO: branch on decidability of ⊏
  sub-paths : Ctx → path → List path
  sub-paths [] p = [] 
  sub-paths (d ∷ Δ) p = {!   !}