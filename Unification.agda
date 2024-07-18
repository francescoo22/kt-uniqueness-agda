open import Grammar
open import Relations
open import Base
open import Agda.Builtin.List
open import Data.Product using (_×_ ; _,_)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core

module Unification where
  {-# TERMINATING #-} -- TODO: prove that Δ ∖ p reduces Δ
  _⊔_ : Ctx → Ctx → Ctx
  [] ⊔ [] = []
  ((δ-p ∶ δ-α * δ-β) ∷ Δ) ⊔ [] with (δ-α , δ-β) ⊔-αβ ([] ⟨ δ-p ⟩)
  ... | α-⊔ , β-⊔ = (δ-p ∶ α-⊔ * β-⊔) ∷ (Δ ⊔ [])
  Δ₁ ⊔ ((δ-p ∶ δ-α * δ-β) ∷ Δ₂) with (δ-α , δ-β) ⊔-αβ (Δ₁ ⟨ δ-p ⟩)
  ... | α-⊔ , β-⊔ = (δ-p ∶ α-⊔ * β-⊔) ∷ ((Δ₁ ∖ δ-p) ⊔ Δ₂)

  _◂_ : Ctx → Ctx → Ctx
  [] ◂ Δ₁ = [] 
  ((δ-p ∶ δ-α * δ-β) ∷ Δ) ◂ Δ₁ with root δ-p
  ... | x with x ∉-? Δ₁
  ... | yes x∉Δ₁ = Δ ◂ Δ₁
  ... | no ¬x∉Δ₁ = (δ-p ∶ δ-α * δ-β) ∷ (Δ ◂ Δ₁)

  unify : Ctx → Ctx → Ctx → Ctx
  unify Δ Δ₁ Δ₂ = (Δ₁ ⊔ Δ₂) ◂ Δ