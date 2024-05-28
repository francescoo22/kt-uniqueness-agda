open import Grammar
open import Base
open import Relations
open import SubPaths
open import Agda.Builtin.List
open import Data.List.NonEmpty
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_ ; _,_)

module Paths where
  _⟦_⟧ : Ctx → Path → αβ
  Δ ⟦ var x ⟧ = Δ ⟨ var x ⟩ 
  Δ ⟦ p ∙ f ⟧ = ⨆ ((Δ ⟦ p ⟧) ∷ ((Δ ⟨ p ∙ f ⟩) ∷ []))

  data std : Ctx → Path → αβ → Set where
    std-empty : (p : Path) → (r : αβ) → std [] p r
    std-rec-1 : {p p' : Path} → (r : αβ) → (Δ : Ctx) → ¬ (p ⊏ p') → std Δ p r
    std-rec-2 : {p p' : Path} {a a' : α} {b b' : β} {Δ : Ctx} →
                (p ⊏ p') →
                ((a' , b') ≼ (((root p ∶ a * b) ∷ []) ⟦ p' ⟧)) →
                (std Δ p (a , b)) →
                (std ((p' ∶ a' * b') ∷ Δ) p (a , b))