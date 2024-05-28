{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Grammar
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Data.Product using (_×_ ; _,_)

module Base where
  data _∉_ : Path → Ctx → Set where
    ∉-base : (p : Path) → p ∉ []
    ∉-rec  : {p : Path} {d : δ} {Δ : Ctx} → 
             ¬ (p ≡ δ.δ-p d) → 
             p ∉ Δ →
             p ∉ (d ∷ Δ)

  data valid-ctx : Ctx → Set where
    valid-ctx-base : valid-ctx []
    valid-ctx-rec  : {Δ : Ctx} {d : δ} →
                     valid-ctx Δ →
                     (δ.δ-p d) ∉ Δ →
                     valid-ctx (d ∷ Δ)

  -- TODO: more specific return type?
  root : Path → Path
  root (var x) = var x
  root (p ∙ f) = root p

  -- TODO: add default
  _⟨_⟩ : Ctx → Path → αβ
  [] ⟨ p ⟩ = {!   !}
  (record { δ-p = δ-p ; δ-α = δ-α ; δ-β = δ-β } ∷ Δ) ⟨ p ⟩ with p ≡-? δ-p
  ... | yes _ = δ-α , δ-β
  ... | no _ = Δ ⟨ p ⟩

  _∖_ : Ctx → Path → Ctx
  [] ∖ p = []
  (record { δ-p = δ-p ; δ-α = δ-α ; δ-β = δ-β } ∷ Δ) ∖ p with p ≡-? δ-p
  ... | yes _ = Δ
  ... | no _ = Δ ∖ p
 