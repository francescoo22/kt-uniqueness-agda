{-# OPTIONS --allow-unsolved-metas #-}
open import Grammar
open import Base
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Data.Product using (_×_ ; _,_)
open import Data.Empty
open import Data.List.Base using (_∷ʳ_)

module SubPaths where
  data _⊏_ : Path → Path → Set where
    ⊏-base : (p : Path) → (f : kt-property-name) → p ⊏ (p ∙ f)
    ⊏-rec : {p₁ p₂ : Path} → (f : kt-property-name) → p₁ ⊏ p₂ → p₁ ⊏ (p₂ ∙ f)

  _⊏-?_ : (p₁ p₂ : Path) → Dec (p₁ ⊏ p₂)
  p₁ ⊏-? (var x) = no λ ()
  p₁ ⊏-? (p₂ ∙ f) with p₁ ⊏-? p₂
  ... | yes p₁⊏p₂ = yes (⊏-rec f p₁⊏p₂)
  ... | no ¬p₁⊏p₂ with p₁ ≡-? p₂
  ... | yes p₁≡p₂ = yes {!   !}
  ... | no ¬p₁≡p₂ = no λ sub → {!   !}

  data _⊑_ : Path → Path → Set where
    less : {p₁ p₂ : Path} → p₁ ⊏ p₂ → p₁ ⊑ p₂
    equal : {p₁ p₂ : Path} → p₁ ≡ p₂ → p₁ ⊑ p₂

  _⊑-?_ : (p₁ p₂ : Path) → Dec (p₁ ⊑ p₂)
  p₁ ⊑-? p₂ with p₁ ≡-? p₂
  ... | yes p₁≡p₂ = yes (equal p₁≡p₂) 
  ... | no ¬p₁≡p₂ with p₁ ⊏-? p₂
  ... | yes p₁⊏p₂ = yes (less p₁⊏p₂)
  ... | no ¬p₁⊏p₂ = no λ { (less p) → ¬p₁⊏p₂ p ; (equal q) → ¬p₁≡p₂ q }

  _⊖_ : Ctx → Path → Ctx
  [] ⊖ p = []
  ((p' ∶ δ-α * δ-β) ∷ Δ) ⊖ p with p ⊑-? p'
  ... | yes _ = Δ ⊖ p
  ... | no _ = (p' ∶ δ-α * δ-β) ∷ Δ ⊖ p

  _[_↦_] : Ctx → Path → (α × β) → Ctx
  Δ [ p ↦ αₚ , βₚ ] with Δ ∖ p
  ... | Δ' = (p ∶ αₚ * βₚ) ∷ Δ'

  diff : {p p' : Path} → p ⊏ p' → List kt-property-name
  diff (⊏-base _ f) = f ∷ []
  diff (⊏-rec f p⊏p₁) = diff p⊏p₁ ∷ʳ f

  sub-paths : Ctx → Path → List δ
  sub-paths [] p = []       
  sub-paths ((p' ∶ δ-α * δ-β) ∷ Δ) p with p ⊏-? p'
  ... | yes p⊏p' = (p' ∶ δ-α * δ-β) ∷ sub-paths Δ p
  ... | no ¬p⊏p' = sub-paths Δ p