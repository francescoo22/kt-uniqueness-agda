open import Agda.Builtin.List
-- open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import grammar

module base where
  data _∉_ : path → Δ → Set where
    ∉-base : (p : path) → p ∉ []
    ∉-rec : 