
import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

import VERSEIM2025.Subspaces

-- Katherine and Clea, I think you can prove various things using the
-- "basis of internal direct sum" theorem that Katherine finished
-- proving.

-- suppose that (V,β) is a space with a non-degenerate bilinear from
-- and that W is a subspace of V

open LinearMap (BilinForm)
open LinearMap

variable {k V:Type} [Field k] [AddCommGroup V] [Module k V]

variable {β:BilinForm k V}
variable {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]


-- let's make a precidicate for subspaces on which the form is
-- non-degenerate (I think Sahan must have some version of this, but I
-- looked in his code and in mathlib and didn't see exactly what I
-- wanted...)

def Nondeg_subspace (β : BilinForm k V) (W:Submodule k V) : Prop :=
  BilinForm.Nondegenerate (BilinForm.restrict β W)

-- we want to prove: if W is a non-degenerate subspace, then also its
-- orthogonal complement is non-degenerate

-- I think previously I had given a def/construction for orthogonal
-- complement, but it is actually already in Mathlib, as
-- `LinearMap.BilinForm.orthogonal`


def p (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]: ι₁ ⊕ ι₂ → Prop := by
  intro i
  exact (∃ (y : ι₁), i = Sum.inl y)


theorem finrank_sup_eq_neg_finrank_inf_add {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  (s t : Submodule K V) [FiniteDimensional K ↥s] [FiniteDimensional K ↥t] :
  Module.finrank K ↥(s ⊔ t) = Module.finrank K ↥s + Module.finrank K ↥t - (Module.finrank K ↥(s ⊓ t)) := by
    rw[Nat.sub_eq_of_eq_add']
    rw[← Submodule.finrank_sup_add_finrank_inf_eq]
    rw[add_comm]


lemma left_mem_basis_direct_sum {ι₁ ι₂ :Type}
              (W₁ W₂ : Submodule k V)
              (B₁ : Basis ι₁ k W₁)
              (B₂ : Basis ι₂ k W₂)
              [FiniteDimensional k V] [Fintype ι₁] [DecidableEq ι₁]
              [Fintype ι₂]  [DecidableEq ι₂]
        (hspan : W₁ ⊔ W₂ = (⊤: Submodule k V))
        (hindep : W₁ ⊓ W₂ = (⊥:Submodule k V)) (i:ι₁) :
        (basis_of_direct_sum W₁ W₂ B₁ B₂ hspan hindep) (Sum.inl i) ∈ W₁ := by
        unfold basis_of_direct_sum
        unfold Sum.elim
        simp

lemma right_mem_basis_direct_sum {ι₁ ι₂ :Type}
              (W₁ W₂ : Submodule k V)
              (B₁ : Basis ι₁ k W₁)
              (B₂ : Basis ι₂ k W₂)
              [FiniteDimensional k V] [Fintype ι₁] [DecidableEq ι₁]
              [Fintype ι₂]  [DecidableEq ι₂]
        (hspan : W₁ ⊔ W₂ = (⊤: Submodule k V))
        (hindep : W₁ ⊓ W₂ = (⊥:Submodule k V)) (i:ι₂) :
        (basis_of_direct_sum W₁ W₂ B₁ B₂ hspan hindep) (Sum.inr i) ∈ W₂ := by
        unfold basis_of_direct_sum
        unfold Sum.elim
        simp

lemma not_left_in_right {s₁ s₂ : Type} (i : s₁ ⊕ s₂) (h : ¬ ∃ y:s₁, i = Sum.inl y)
  [DecidableEq s₁] [DecidableEq s₂] : ∃ z:s₂, i = Sum.inr z := by
  match i with
  | Sum.inr x => use x
  | Sum.inl y =>
     exfalso
     apply h
     use y

lemma not_p_inr (x : ι₂) : ¬ p ι₁ ι₂ (Sum.inr x:ι₁⊕ι₂) := by
  unfold p
  by_contra h
  rcases h with ⟨y,hy⟩
  apply_fun Sum.isRight at hy
  simp at hy

def eq (ι₁ ι₂ : Type) [Fintype ι₁] [DecidableEq ι₁]
        [Fintype ι₂]  [DecidableEq ι₂]
        : { i : ι₁ ⊕ ι₂ // ¬ p ι₁ ι₂ i } ≃ ι₂ where
  toFun := by
    intro ⟨i,hᵢ⟩
    match i with
    | Sum.inr z => exact z
    | Sum.inl y =>
       exfalso
       apply hᵢ
       use y
  invFun i := ⟨Sum.inr i, not_p_inr i⟩
  left_inv := by
    intro ⟨ i,hᵢ ⟩
    rcases (not_left_in_right i hᵢ) with ⟨j,hj⟩
    unfold p at hᵢ
    simp
    subst hj
    simp_all only
  right_inv := by
    intro i
    exact rfl


lemma direct_sum_basis_right_eq_basis {ι₁ ι₂ : Type} (W₁ W₂ : Submodule k V)
              (B₁ : Basis ι₁ k W₁)
              (B₂ : Basis ι₂ k W₂)
              [FiniteDimensional k V] [Fintype ι₁] [DecidableEq ι₁]
              [Fintype ι₂]  [DecidableEq ι₂]
        (hspan : W₁ ⊔ W₂ = (⊤: Submodule k V))
        (hindep : W₁ ⊓ W₂ = (⊥:Submodule k V)) (i:ι₂)
         :
        (basis_of_direct_sum W₁ W₂ B₁ B₂ hspan hindep) (Sum.inr i) = B₂ i := by
          unfold basis_of_direct_sum
          simp

lemma eq_eq_not_p {ι₁ ι₂ : Type} (W₁ W₂ : Submodule k V)
              (B₁ : Basis ι₁ k W₁)
              (B₂ : Basis ι₂ k W₂)
              [FiniteDimensional k V] [Fintype ι₁] [DecidableEq ι₁]
              [Fintype ι₂]  [DecidableEq ι₂]
        (hspan : W₁ ⊔ W₂ = (⊤: Submodule k V))
        (hindep : W₁ ⊓ W₂ = (⊥:Submodule k V)) (i: ι₁ ⊕ ι₂) (h: ¬p ι₁ ι₂ i)
        : (basis_of_direct_sum W₁ W₂ B₁ B₂ hspan hindep) ( i) = B₂ (eq ι₁ ι₂ ⟨i, h ⟩ ) := by
        unfold basis_of_direct_sum
        simp only [Basis.mk_apply]
        cases i with
        | inl i₁ =>
          exfalso
          exact h (by simp [p])
        | inr i₂ =>
          simp [Sum.elim, eq]

theorem ortho_complement_nondeg (β:BilinForm k V) [FiniteDimensional k V]
  (bnd : BilinForm.Nondegenerate β)
  (W :Submodule k V) (wnd : Nondeg_subspace β W) (href : β.IsRefl)
  [DecidableEq ↑(Basis.ofVectorSpaceIndex k ↥W)] [DecidableEq (BilinForm.orthogonal β W)]
  [DecidablePred (p ↑(Basis.ofVectorSpaceIndex k ↥W) ↑(Basis.ofVectorSpaceIndex k ↥(BilinForm.orthogonal β W)))]
  {brefl : LinearMap.BilinForm.IsRefl β }:
  Nondeg_subspace β (BilinForm.orthogonal β W) := by
    let ι₁ := (Basis.ofVectorSpaceIndex k ↥W)
    let ι₂ := (Basis.ofVectorSpaceIndex k ↥(BilinForm.orthogonal β W))
    have k₀ : W ⊓ (BilinForm.orthogonal β W) = ⊥ := by
      rw[IsCompl.inf_eq_bot]
      exact (BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal brefl).mp wnd
    have k₁ : W ⊔ (BilinForm.orthogonal β W) = ⊤ := by
      ext x
      constructor
      · simp
      · simp
        let Wplus := W ⊔ β.orthogonal W
        have k₁₀ : Wplus = W ⊔ β.orthogonal W := by
            rfl
        have k₁₁ : Module.finrank k (Wplus) = Module.finrank k V := by
          rw[k₁₀, finrank_sup_eq_neg_finrank_inf_add, k₀]
          simp
          rw[LinearMap.BilinForm.finrank_orthogonal]
          · rw[← add_comm]
            refine Nat.sub_add_cancel ?_
            apply Submodule.finrank_le
          · exact bnd
          · exact href
        apply Submodule.eq_top_of_finrank_eq at k₁₁
        rw[← k₁₀]
        rw[k₁₁]
        simp
    let b₁ : Basis ι₁ k W := Basis.ofVectorSpace k W
    let b₂ : Basis ι₂ k (BilinForm.orthogonal β W) := Basis.ofVectorSpace k (BilinForm.orthogonal β W)
    let B : Basis (ι₁ ⊕ ι₂) k V := by
      apply basis_of_direct_sum
      · exact b₁
      · exact b₂
      · exact k₁
      · exact k₀
    let M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k := BilinForm.toMatrix B β
    let M₁ := (M.toSquareBlockProp (p ↑ι₁ ↑ι₂))
    let M₂ := (M.toSquareBlockProp fun i ↦ ¬p (↑ι₁) (↑ι₂) i)
    let Mdiag := Matrix.fromBlocks M₁ 0 0 M₂
    have k₂ : ∀ i, ¬(p ι₁ ι₂) i → ∀ j , (p ι₁ ι₂) j → M i j = 0 := by
      intro x j₀ y j₁
      unfold p at j₀
      unfold p at j₁
      unfold M
      have g₀ : B y ∈ W := by
        unfold B
        rcases j₁ with ⟨ y₁, hy₁ ⟩
        rw[hy₁]
        apply left_mem_basis_direct_sum W (BilinForm.orthogonal β W) b₁ b₂ k₁ k₀
      have g₁ : B x ∈ (BilinForm.orthogonal β W) := by
        unfold B
        have g₁₀ : ∃ z, x = Sum.inr z := by
          exact not_left_in_right x j₀
        rcases g₁₀ with ⟨ x₁, hx₁ ⟩
        rw[hx₁]
        apply right_mem_basis_direct_sum W (BilinForm.orthogonal β W) b₁ b₂ k₁ k₀
      rw[LinearMap.BilinForm.mem_orthogonal_iff] at g₁
      rw[BilinForm.toMatrix_apply]
      exact href (B y) (B x) (href (B x) (B y) (href (B y) (B x) (g₁ (B y) g₀)))
    have k₃ : M.det = M₁.det * M₂.det := by
      rw[Matrix.twoBlockTriangular_det M (p ι₁ ι₂) k₂]
    have k₄ : ∀ i, ∀ j, (M₂ i j = (BilinForm.toMatrix b₂ (β.restrict (BilinForm.orthogonal β W))) (eq  ι₁ ι₂ i) (eq ι₁ ι₂ j)) := by
      intro x₀ y₀
      unfold M₂ Matrix.toSquareBlockProp M BilinForm.toMatrix
      simp
      refine DFunLike.congr ?_ ?_
      · ext v
        unfold B
        rw[eq_eq_not_p]
      · unfold B
        rw[eq_eq_not_p]
    have k₅ : M₂.det ≠ 0 := by
      intro h
      rw[h] at k₃
      rw[mul_zero] at k₃
      have k₅₀ : M.det ≠ 0 := by
        exact (BilinForm.nondegenerate_iff_det_ne_zero B).mp bnd
      exact k₅₀ k₃
    unfold Nondeg_subspace
    have k₆ : ((Matrix.reindex (eq ι₁ ι₂) (eq ι₁ ι₂) M₂) = (BilinForm.toMatrix b₂ (β.restrict (BilinForm.orthogonal β W)))) := by
      exact Matrix.ext fun i j ↦ k₄ ((eq ↑ι₁ ↑ι₂).symm i) ((eq ↑ι₁ ↑ι₂).symm j)
    have k₇ : M₂.det = (BilinForm.toMatrix b₂ (β.restrict (BilinForm.orthogonal β W))).det := by
      rw[← k₆]
      exact Eq.symm (Matrix.det_reindex_self (eq ↑ι₁ ↑ι₂) M₂)
    rw[k₇] at k₅
    apply Matrix.nondegenerate_of_det_ne_zero at k₅
    exact (BilinForm.nondegenerate_toMatrix_iff b₂).mp k₅
