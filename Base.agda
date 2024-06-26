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

  postulate _∉-?_ : (p : Path) → (Δ : Ctx) → Dec (p ∉ Δ) -- TODO: prove it

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

  -- information known by the compiler, not relevant to be defined here
  postulate default-annotation : Path → kt-property-name → α-f

  _⟨_⟩ : Ctx → Path → αβ
  [] ⟨ var x ⟩ = ⊤ , ∘ -- Note: this case cannot happen in a well typed kt program, for now it is ok to leave it as it is
  [] ⟨ p ∙ f ⟩ = αf→α (default-annotation p f) , ∘
  ((δ-p ∶ δ-α * δ-β) ∷ Δ) ⟨ p ⟩ with p ≡-? δ-p
  ... | yes _ = δ-α , δ-β
  ... | no _ = Δ ⟨ p ⟩

  _∖_ : Ctx → Path → Ctx
  [] ∖ p = []
  ((δ-p ∶ δ-α * δ-β) ∷ Δ) ∖ p with p ≡-? δ-p
  ... | yes _ = Δ
  ... | no _ = (δ-p ∶ δ-α * δ-β) ∷ Δ ∖ p
 