open import Grammar
open import Base
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Data.Product
open import Data.Empty

module SubPaths where
  data _⊏_ : path → path → Set where
    ⊏-base : (p : path) → (f : kt-property-name) → p ⊏ (p ∙ f)
    ⊏-rec : (p₁ p₂ : path) → (f : kt-property-name) → p₁ ⊏ p₂ → p₁ ⊏ (p₂ ∙ f)

  ⊏-? : (p₁ p₂ : path) → Dec (p₁ ⊏ p₂)
  ⊏-? p₁ (var x) = no λ ()
  ⊏-? p₁ (p₂ ∙ f) with ⊏-? p₁ p₂
  ... | yes p₁⊏p₂ = yes (⊏-rec p₁ p₂ f p₁⊏p₂)
  ... | no p = {!  !} -- TODO

  data _⊑_ : path → path → Set where
    less : {p₁ p₂ : path} → p₁ ⊏ p₂ → p₁ ⊑ p₂
    equal : {p₁ p₂ : path} → p₁ ≡ p₂ → p₁ ⊑ p₂

  ⊑-? : (p₁ p₂ : path) → Dec (p₁ ⊑ p₂)
  ⊑-? p₁ p₂ with ≡-? p₁ p₂
  ... | yes p₁≡p₂ = yes (equal p₁≡p₂) 
  ... | no ¬p₁≡p₂ with ⊏-? p₁ p₂
  ... | yes p₁⊏p₂ = yes (less p₁⊏p₂)
  ... | no ¬p₁⊏p₂ = no λ { (less p) → ¬p₁⊏p₂ p ; (equal q) → ¬p₁≡p₂ q }

  _⊖_ : Ctx → path → Ctx
  [] ⊖ p = []
  ((p' ∶ δ-α * δ-β) ∷ Δ) ⊖ p with ⊑-? p p'
  ... | yes _ = Δ ⊖ p
  ... | no _ = (p' ∶ δ-α * δ-β) ∷ Δ ⊖ p

  _[_↦_] : Ctx → path → (α × β) → Ctx
  Δ [ p ↦ αₚ , βₚ ] with Δ ∖ p
  ... | Δ' = (p ∶ αₚ * βₚ) ∷ Δ'

  sub-paths : Ctx → path → List path
  sub-paths [] p = []       
  sub-paths ((δ-p ∶ δ-α * δ-β) ∷ Δ) p = {!   !} -- TODO