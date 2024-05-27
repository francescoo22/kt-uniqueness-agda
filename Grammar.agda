open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Data.Bool.Base using (_∧_)
-- open import Relation.Nullary.Decidable using (⌊_⌋)
-- open import Relation.Binary using (Decidable)
open import Agda.Builtin.Equality using (_≡_)
import Data.String.Properties as Str

module Grammar where
  data α-f : Set where
    unique-f : α-f
    shared-f : α-f

  data α : Set where
    unique : α
    shared : α
    ⊤ : α

  data β : Set where
    ♭ : β
    ¬♭ : β

  data kt-property-name : Set where
    property-name : String → kt-property-name

  data kt-var-name : Set where
    var-name : String → kt-var-name

  data kt-method-name : Set where
    method-name : String → kt-method-name

  data kt-class-name : Set where
    class-name : String → kt-class-name

  record kt-property : Set where
    field
      name : kt-property-name
      annotation₁ : α-f

  record kt-argument : Set where
    field
      name : kt-var-name
      annotation₁ : α-f
      annotation₂ : β

  record kt-class : Set where
    field
      name : kt-class-name
      properties : List kt-property

  record kt-method : Set where
    field
      name : kt-method-name
      args : List kt-argument
      return : α-f

  data path : Set where
    var : kt-var-name → path
    _∙_ : path → kt-property-name → path

  _==_ : path → path → Bool
  var (var-name x) == var (var-name y) = x Str.== y
  var x == (p₂ ∙ x₁) = false
  (p₁ ∙ f) == var x = false
  (p₁ ∙ property-name x) == (p₂ ∙ property-name y) = (p₁ == p₂) ∧ (x Str.== y)

  data exp : Set where
    null : exp
    path-e : path → exp
    call-e : kt-method-name → List path → exp

  data stmt : Set where
    decl : kt-var-name → stmt
    assign : (lh : path) → (rh : exp) → stmt
    if_==_then_else_ : path → path → List stmt → List stmt → stmt
    call-s : kt-method-name → List path → stmt

  record δ : Set where
    field
      δ-p : path
      δ-α : α
      δ-β : β

  Ctx = List δ
