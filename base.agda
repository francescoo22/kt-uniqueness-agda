open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import grammar
open import Relation.Nullary
open import Data.Product

module base where
  data _∉_ : path → Ctx → Set where
    ∉-base : (p : path) → p ∉ []
    ∉-rec  : {p : path} {d : δ} {Δ : Ctx} → 
             ¬ (p ≡ δ.δ-p d) → 
             p ∉ Δ →
             p ∉ (d ∷ Δ)

  data valid-ctx : Ctx → Set where
    valid-ctx-base : valid-ctx []
    valid-ctx-rec  : {Δ : Ctx} {d : δ} →
                     valid-ctx Δ →
                     (δ.δ-p d) ∉ Δ →
                     valid-ctx (d ∷ Δ)

  root : path → path
  root (var x) = var x
  root (p ∙ f) = root p

  -- TODO: add default
  _⟨_⟩ : Ctx → path → α × β
  [] ⟨ p ⟩ = {!   !}
  (record { δ-p = δ-p ; δ-α = δ-α ; δ-β = δ-β } ∷ Δ) ⟨ p ⟩ with p == δ-p
  ... | true = δ-α ,′ δ-β
  ... | false = Δ ⟨ p ⟩

  _∖_ : Ctx → path → Ctx
  [] ∖ p = []
  (record { δ-p = δ-p ; δ-α = δ-α ; δ-β = δ-β } ∷ Δ) ∖ p with p == δ-p
  ... | true = Δ
  ... | false = Δ ∖ p
 