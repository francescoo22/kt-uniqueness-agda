open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Data.Bool.Base using (_∧_)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.String.Properties as Str
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂)

module Grammar where
  data α-f : Set where
    unique-f : α-f
    shared-f : α-f

  data α : Set where
    unique : α
    shared : α
    ⊤ : α

  αf→α : α-f → α
  αf→α unique-f = unique
  αf→α shared-f = shared

  data β : Set where
    ♭ : β
    ∘ : β

  αβ = α × β

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
      name        : kt-property-name
      annotation₁ : α-f

  record kt-argument : Set where
    field
      name        : kt-var-name
      annotation₁ : α-f
      annotation₂ : β

  record kt-class : Set where
    field
      name       : kt-class-name
      properties : List kt-property

  record kt-method : Set where
    field
      name   : kt-method-name
      args   : List kt-argument
      return : α-f

  data Path : Set where
    var : kt-var-name → Path
    _∙_ : Path → kt-property-name → Path

  path-var-inj₁ : {x y : String} → var (var-name x) ≡ var (var-name y) → x ≡ y
  path-var-inj₁ refl = refl

  path-var-inj₂ : {x y : String} {p₁ p₂ : Path} → p₁ ∙ (property-name x) ≡ p₂ ∙ (property-name y) → x ≡ y
  path-var-inj₂ refl = refl

  path-var-inj₃ : {x y : String} {p₁ p₂ : Path} → p₁ ∙ (property-name x) ≡ p₂ ∙ (property-name y) → p₁ ≡ p₂
  path-var-inj₃ refl = refl

  _≡-?_ : (p₁ p₂ : Path) → Dec (p₁ ≡ p₂)
  (var (var-name x)) ≡-? (var (var-name y)) with x Str.≟ y
  ... | yes x≡y = yes (cong (λ z → var (var-name z)) x≡y)
  ... | no ¬x≡y = no λ eq → ¬x≡y (path-var-inj₁ eq)
  (p₁ ∙ f) ≡-? (var x) = no (λ ())
  (var x) ≡-? (p₂ ∙ f) = no (λ ())
  (p₁ ∙ property-name x) ≡-? (p₂ ∙ property-name y) with x Str.≟ y
  ... | no ¬x≡y = no λ eq → ¬x≡y (path-var-inj₂ eq)
  ... | yes x≡y with p₁ ≡-? p₂
  ... | yes p₁≡p₂ = yes (cong₂ (λ z z₁ → z ∙ property-name z₁) p₁≡p₂ x≡y)
  ... | no ¬p₁≡p₂ = no λ eq → ¬p₁≡p₂ (path-var-inj₃ eq)

  data exp : Set where
    null   : exp
    pathₑ  : Path → exp
    callₑ  : kt-method-name → List Path → exp

  data Stmt : Set where
    decl             : kt-var-name → Stmt
    _:=_             : (lh : Path) → (rh : exp) → Stmt
    if_==_then_else_ : Path → Path → List Stmt → List Stmt → Stmt
    callₛ            : kt-method-name → List Path → Stmt
    seq              : List Stmt → Stmt

  record δ : Set where
    constructor _∶_*_
    field
      δ-p : Path
      δ-α : α
      δ-β : β

  -- TODO valid by construction (List δ → Set where mk : xs → valid xs)
  Ctx = List δ
 