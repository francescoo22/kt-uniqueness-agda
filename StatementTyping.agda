open import Grammar
open import SubPaths
open import Paths
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Data.List.Base using (_++_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_ ; _,_)

module StatementTyping (m-type : kt-method-name → (List (α-f × β)) × α-f) where
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
                      Δ ⊢ p := pathₑ p' ⊣ (Δ [ p' ↦ ⊤ , ∘ ] [ p ↦ unique , ∘ ] ++ sub-paths-replaced Δ p' p)

    t-assign-shared : {p p' : Path} {Δ Δ' : Ctx} {αₚ : α} →
                      ¬ (p' ⊑ p) →
                      (Δ ⟦ p ⟧) ≡ (αₚ , ∘) →
                      (Δ ⟦ p' ⟧) ≡ (shared , ∘) →
                      Δ ⊢ p := pathₑ p' ⊣ (Δ [ p ↦ shared , ∘ ] ++ sub-paths-replaced Δ p' p)

    -- TODO: if after defining unification
    -- TODO: assign-borrowed-field after deciding how it works
    -- TODO: call, return, begin
    