import Mathlib.Tactic

noncomputable section

open Module
open LinearMap
open LinearMap (BilinForm)


variable  {k V₁ V₂ :Type} [Field k] 
  [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

structure Isometries
  (β₁:BilinForm k V₁) 
  (β₂:BilinForm k V₂)
  where
    equiv : V₁ ≃ₗ[k] V₂
    compat : ∀ (x y : V₁), β₁ x y = β₂ (equiv v₁) (equiv v₂) 

notation:100 lhs:100 "≃[" field:100 "," lhb:100 "," rhb:100 "]" rhs:100 => 
  Isometries (k:= field) (V₁ := lhs) (V₂ := rhs) lhb rhb

theorem equiv_via_matrices {ι:Type} [Fintype ι] [DecidableEq ι]
  (β₁ : BilinForm k V₁)   (β₂ : BilinForm k V₂) 
  (b₁ : Basis ι k V₁)
  :  Nonempty (V₁ ≃[k,β₁,β₂] V₂)  ↔  ∃ b₂:Basis ι k V₂,
    (BilinForm.toMatrix b₁ β₁) =  (BilinForm.toMatrix b₂ β₂) := by sorry


def alternate_iso {B₁: BilinForm k V₁} (B₂: BilinForm k V₂) 
  (balt₁: IsAlt B₁) (balt₂: IsAlt B₂)
  (hd₁: B₁.Nondegenerate) (hd₂: B₂.Nondegenerate) 
  [FiniteDimensional k V₁] [FiniteDimensional k V₂]
  (h: Module.finrank k V₁ = Module.finrank k V₂) : V₁ ≃[k,B₁,B₂] V₂ := by sorry


theorem refl_is_alt_or_symm {B: BilinForm k V₁} (h: B.IsRefl) [FiniteDimensional k V₁] :
    B.IsAlt ∨ B.IsSymm := by sorry
