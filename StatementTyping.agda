open import Grammar
open import SubPaths
open import Paths
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_ ; _,_)

module StatementTyping where
  data _⊢_⊣_ : Ctx → Stmt → Ctx → Set where
    t-decl : (Δ : Ctx) → (x : kt-var-name) → Δ ⊢ decl x ⊣ ((var x ∶ ⊤ * ∘) ∷ Δ)
    
    t-seq₁ : (Δ : Ctx) → Δ ⊢ seq [] ⊣ Δ
    t-seq₂ : {Δ Δ₁ Δ' : Ctx} {stmt : Stmt} {stmts : List Stmt} →
             Δ ⊢ stmt ⊣ Δ₁ →
             Δ₁ ⊢ seq stmts ⊣ Δ' →
             Δ ⊢ seq (stmt ∷ stmts) ⊣ Δ'

    t-assign-null : (Δ : Ctx) → (p : Path) →
                    Δ ⊢ p := null ⊣ (Δ [ p ↦ unique , ∘ ])

    t-assign-unique : {p p' : Path} {Δ Δ' : Ctx} →
                      ¬ (p' ⊑ p) →
                      (Δ ⟦ p' ⟧) ≡ (unique , ∘) →
                      Δ [ p' ↦ ⊤ , ∘ ] [ p ↦ unique , ∘ ] ≡ Δ' →
                      -- TODO: subpaths replacing
                      Δ ⊢ p := pathₑ p' ⊣ Δ'

    t-assign-shared : {p p' : Path} {Δ Δ' : Ctx} {αₚ : α} →
                      ¬ (p' ⊑ p) →
                      (Δ ⟦ p ⟧) ≡ (αₚ , ∘) →
                      (Δ ⟦ p' ⟧) ≡ (shared , ∘) →
                      Δ [ p ↦ shared , ∘ ] ≡ Δ' →
                      -- TODO: subpaths replacing
                      Δ ⊢ p := pathₑ p' ⊣ Δ'

    -- TODO: if after defining unification
    -- TODO: assign-borrowed-field after deciding how it works
    -- TODO: call, return, begin
    