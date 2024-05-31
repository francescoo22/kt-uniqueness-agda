open import Grammar
open import Agda.Builtin.List
open import Data.List.NonEmpty
open import Data.Product

module Relations where
  data _≼_ : αβ → αβ → Set where
    ≼-id       : (r : αβ) → r ≼ r
    ≼-trans    : (r₁ r₂ r₃ : αβ) → r₁ ≼ r₂ → r₂ ≼ r₃ → r₁ ≼ r₃
    ≼-♭-shared : (shared , ♭) ≼ (⊤ , ∘)
    ≼-shared   : (shared , ∘) ≼ (shared , ♭)
    ≼-♭-unique : (unique , ♭) ≼ (shared , ♭)
    ≼-unique₁  : (unique , ∘) ≼ (shared , ∘)
    ≼-unique₂  : (unique , ∘) ≼ (unique , ♭)

  data _⇝_⇝_ : αβ → αβ → αβ → Set where
    ⇝-unique : (unique , ∘) ⇝ (unique , ∘) ⇝ (⊤ , ∘)
    ⇝-shared : (α₁ : α) → (α₁ , ∘) ≼ (shared , ∘) → (α₁ , ∘) ⇝ (shared , ∘) ⇝ (shared , ∘)
    ⇝-♭      : (α₁ α₂ : α) → (β₁ : β) → (α₁ , β₁) ≼ (α₂ , ♭) → (α₁ , β₁) ⇝ (α₂ , ♭) ⇝ (α₁ , β₁)

  _⊔-α_ : α → α → α 
  a ⊔-α ⊤ = ⊤
  unique ⊔-α shared = shared
  shared ⊔-α shared = shared
  ⊤ ⊔-α shared = ⊤
  a ⊔-α unique = a

  _⊔-β_ : β → β → β
  b ⊔-β ♭ = ♭
  ∘ ⊔-β ∘ = ∘
  ♭ ⊔-β ∘ = ♭

  -- NOTE: Here also a ⊤ ♭ may exists, but it should be ok
  _⊔-αβ_ : αβ → αβ → αβ
  (a , b) ⊔-αβ (a₁ , b₁) = (a ⊔-α a₁) , (b ⊔-β b₁)

  ⨆ : List⁺ αβ → αβ
  ⨆ (r ∷ []) = r
  ⨆ (r ∷ rs) = ⨆-aux r rs
    where
    ⨆-aux : αβ → List αβ → αβ
    ⨆-aux r [] = r
    ⨆-aux r (r₁ ∷ rs) = ⨆-aux (r ⊔-αβ r₁) rs

