
import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open LinearMap (BilinForm)
open LinearMap

noncomputable section

variable {k V:Type} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

variable {β:BilinForm k V}

example : β.Nondegenerate ↔ ker β = ⊥ := by
  exact LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot 

-- variable (ι:Type) [DecidableEq ι] [Fintype ι]

example (ι:Type) [DecidableEq ι] [Fintype ι] 
 (b:Basis ι k V) : β.Nondegenerate ↔ ((BilinForm.toMatrix b) β).det ≠ 0:= by
  apply LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
  
def OrthoSubspace (β:BilinForm k V) 
  (W₁ W₂ : Submodule k V) : Prop := ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, IsOrtho β w₁ w₂

-- prodEquivOfIsCompl
example (W₁ W₂ : Submodule k V) (hc:IsCompl W₁ W₂) :
( W₁ × W₂) ≃ₗ[k] V := by 
   apply Submodule.prodEquivOfIsCompl _ _ hc
   
open Basis
def compat_basis {W₁ W₂ : Submodule k V} (hc:IsCompl W₁ W₂) 
  {ι₁ ι₂ : Type}
  (b₁:Basis ι₁ k W₁) (b₂:Basis ι₂ k W₂):
  Basis (ι₁ ⊕ ι₂) k V :=
  Basis.map (Basis.prod b₁ b₂) (Submodule.prodEquivOfIsCompl _ _ hc) 


def block {ι₁ ι₂ : Type} (M:Matrix (ι₁⊕ι₂) (ι₁⊕ι₂) k) : Prop :=
  ∀ (i:ι₁), ∀ (j:ι₂), M (Sum.inl i) (Sum.inr j) = 0


example {ι₁ ι₂ : Type} (i : ι₁) : ι₁ ⊕ ι₂ := Sum.inl i

example (W₁ W₂ : Submodule k V) (hc:IsCompl W₁ W₂) 
  {ι₁ ι₂ : Type}
   [Fintype ι₁] [Fintype ι₂]
   [DecidableEq ι₁] [DecidableEq ι₂]
  (b₁:Basis ι₁ k W₁) (b₂:Basis ι₂ k W₂)
  (ho:OrthoSubspace β W₁ W₂) : block (BilinForm.toMatrix 
     (compat_basis hc b₁ b₂) β) := by sorry
