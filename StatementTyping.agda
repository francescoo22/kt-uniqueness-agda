open import Grammar
open import SubPaths
open import Paths
open import Unification
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Data.Empty using (⊥)
open import Data.List.Base using (_++_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_ ; _,_)

module StatementTyping (m-type : kt-method-name → (List (α-f × β)) × α-f) where
  m-ret-type : kt-method-name → α-f
  m-ret-type m with m-type m
  ... | fst , snd = snd

  data _⊢_⊣_ : Ctx → Stmt → Ctx → Set where
    t-decl : (Δ : Ctx) → (x : kt-var-name) → Δ ⊢ decl x ⊣ ((var x ∶ ⊤ * ∘) ∷ Δ)
    
    t-block₁ : (Δ : Ctx) → Δ ⊢ block [] ⊣ Δ
    t-block₂ : {Δ Δ₁ Δ' : Ctx} {stmt : Stmt} {stmts : List Stmt} →
             Δ ⊢ stmt ⊣ Δ₁ →
             Δ₁ ⊢ block stmts ⊣ Δ' →
             Δ ⊢ block (stmt ∷ stmts) ⊣ Δ'

    t-assign-null : (Δ : Ctx) → (p : Path) →
                    Δ ⊢ p := null ⊣ (Δ [ p ↦ unique , ∘ ])

    t-assign-unique : {p p' : Path} {Δ Δ' : Ctx} →
                      ¬ (p' ⊑ p) →
                      (Δ ⟦ p' ⟧) ≡ (unique , ∘) →
                      Δ ⊢ p := pathₑ p' ⊣ (Δ [ p' ↦ ⊤ , ∘ ] [ p ↦ unique , ∘ ] ++ sub-paths-replaced Δ p' p)

    t-assign-shared : {p p' : Path} {Δ Δ' : Ctx} {αₚ : α} →
                      ¬ (p' ⊑ p) →
                      (Δ ⟦ p ⟧) ≡ (αₚ , ∘) →
                      (Δ ⟦ p' ⟧) ≡ (shared , ∘) →
                      Δ ⊢ p := pathₑ p' ⊣ (Δ [ p ↦ shared , ∘ ] ++ sub-paths-replaced Δ p' p)

    t-assign-call : {Δ Δ₁ Δ' : Ctx} {p : Path} {m : kt-method-name} {args : List Path} →
                    Δ ⊢ callₛ m args ⊣ Δ' →
                    Δ ⊢ p := callₑ m args ⊣ (Δ' [ p ↦ αf→α (m-ret-type m) , ∘ ])

    t-if : {p₁ p₂ : Path} {s₁ s₂ : Stmt} {Δ Δ₁ Δ₂ : Ctx} →
           (Δ ⟦ p₁ ⟧ ≡ (⊤ , ∘) → ⊥) →
           (Δ ⟦ p₂ ⟧ ≡ (⊤ , ∘) → ⊥) →
           Δ ⊢ s₁ ⊣ Δ₁ →
           Δ ⊢ s₂ ⊣ Δ₂ →
           Δ ⊢ if p₁ == p₂ then s₁ else s₂ ⊣ (unify Δ Δ₁ Δ₂)
    -- TODO: assign-borrowed-field after deciding how it works
    -- TODO: call, return, begin
      