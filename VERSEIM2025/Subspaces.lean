
--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import VERSEIM2025.BilinearForms

-- the next lemma says that for a vector space over a field k of
-- characteristic different from 2, for v in V the equation `2v=0`
-- implies that `v=0`.

--------------------------------------------------------------------------------

def disjointUnion_funs {ι κ X: Type} ( f₁:ι → X) (f₂:κ → X) (u:ι ⊕ κ) : X :=
   match u with
    | Sum.inl x => f₁ x
    | Sum.inr y => f₂ y


def fin_disjoint_fin_equiv_fin (n m: ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m) where
  toFun := fun i =>
    match i with
    | Sum.inl x => Fin.castAdd m x
    | Sum.inr x => by
        rw [ add_comm ]
        exact Fin.castAdd n x
  invFun := by
    rintro ⟨i,_⟩
    if h : i < n then
       have : NeZero n := NeZero.mk (by linarith)
       exact Sum.inl (Fin.ofNat n i)
    else
       have : NeZero m := NeZero.mk (by linarith)
       exact Sum.inr (Fin.ofNat m (n-i))
  left_inv := by sorry
  right_inv := by sorry


--------------------------------------------------------------------------------

theorem lin_indep_by_transverse_subspaces
   (k V : Type) [Field k] [AddCommGroup V] [Module k V] (I₁ I₂ : Type)
   [Fintype I₁] [Fintype I₂]
   (b₁ : I₁ → V) (b₂ : I₂ → V)
   (b1_indep : LinearIndependent k b₁)
   (b2_indep : LinearIndependent k b₂)
   (W₁ W₂ : Submodule k V)
   (h_int : W₁ ⊓ W₂ = ⊥)
   (hbw1 : ∀ i, b₁ i ∈ W₁)
   (hbw2 : ∀ i, b₂ i ∈ W₂)
   [DecidableEq I₁] [DecidableEq I₂]
   : LinearIndependent k (disjointUnion_funs b₁ b₂) := by
    rw[linearIndependent_iff'']
    intro s a g h₁ t
    have k₀ : ∑ i ∈ s, a i • disjointUnion_funs b₁ b₂ i = ∑ i : (I₁ ⊕ I₂), a i • disjointUnion_funs b₁ b₂ i := by
      rw[h₁]
      have k₀₀ : Disjoint s sᶜ := by
        unfold Disjoint
        intro r
        simp
        intro y₀ y₁
        ext x
        simp
        intro hx
        have xnotins : x ∈ Finset.univ \ s := y₁ hx
        simp at xnotins
        exact xnotins (y₀ hx)
      have k₀₁ : s ∪ sᶜ = (⊤ : Finset (I₁ ⊕ I₂)) := by
        simp
      have k₀₂ : (⊤: Finset (I₁ ⊕ I₂)) = Finset.univ := by
        simp
      rw[k₀₂] at k₀₁
      rw[ ← k₀₁]
      rw[Finset.sum_union k₀₀]
      rw[h₁]
      have k₀₃ : ∀ i ∈ sᶜ, a i = 0 := by
        intro i h
        rw[g]
        intro p
        rw[Finset.mem_compl] at h
        exact h p
      simp
      rw[Finset.sum_eq_zero]
      intro x₀ h
      rw[k₀₃]
      simp
      exact h
    have eq_h : ∑ a₁, a (Sum.inl a₁) • disjointUnion_funs b₁ b₂ (Sum.inl a₁) +
    ∑ a₂, a (Sum.inr a₂) • disjointUnion_funs b₁ b₂ (Sum.inr a₂) =
    ∑ i, (a (Sum.inl i)) • (b₁ i) + ∑ j, (a (Sum.inr j)) • (b₂ j) := by
      unfold disjointUnion_funs
      simp
    have k₁ : ∑ i, (a (Sum.inl i)) • (b₁ i) = - ∑ j, (a (Sum.inr j)) • (b₂ j)  := by
      rw[k₀] at h₁
      simp at h₁
      rw[eq_h] at h₁
      rw[add_eq_zero_iff_eq_neg'] at h₁
      rw[h₁]
      simp
    have k₂ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₁ ⊓ W₂ := by
      simp
      have k₂₀ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₁ := by
        exact Submodule.sum_smul_mem W₁ (fun i ↦ a (Sum.inl i)) fun c a ↦ hbw1 c
      have k₂₁ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₂ := by
        rw[k₁]
        apply Submodule.neg_mem
        exact Submodule.sum_smul_mem W₂ (fun i ↦ a (Sum.inr i)) fun c a ↦ hbw2 c
      constructor
      · exact k₂₀
      · exact k₂₁
    have k₃ : - ∑ j, (a  (Sum.inr j)) • (b₂ j) ∈ W₁ ⊓ W₂ := by
      rw[k₁] at k₂
      exact k₂
    rw[linearIndependent_iff''] at b1_indep
    rw[linearIndependent_iff''] at b2_indep
    rw[h_int] at k₂
    rw[h_int] at k₃
    simp at k₂
    simp at k₃
    apply b1_indep at k₂
    apply b2_indep at k₃
    match t with
      | Sum.inl x =>
        rw[k₂]
      | Sum.inr x =>
        rw[k₃]
    · simp
    · simp



--------------------------------------------------------------------------------

variable { k V : Type } [AddCommGroup V] [Field k] [Module k V]

def f {n m:ℕ} {W₁ W₂ : Submodule k V} (s₁:Fin n →  W₁) (s₂: Fin m → W₂) :
  (Fin n) ⊕ (Fin m) → V := by
    intro i
    match i with
     | Sum.inl x => exact ↑(s₁ x)
     | Sum.inr y => exact ↑(s₂ y)

lemma union_span (n m:ℕ) (W₁ W₂ : Submodule k V) (s₁:Fin n →  W₁) (s₂: Fin m → W₂)
      (h₁:(⊤:Submodule k W₁) = Submodule.span k (s₁ '' ⊤))
      (h₂:(⊤:Submodule k W₂) = Submodule.span k (s₂ '' ⊤))
      (h₃:⊤ = W₁ ⊔ W₂)
    : (⊤:Submodule k V) = Submodule.span k ((f s₁ s₂) '' ⊤)  := by sorry




lemma union_span' (n m :ℕ) (W₁ W₂ : Submodule k V) (s₁ s₂ : Set V)
  (h₁:∀ x∈ s₁, s ∈ W₁) (h₂:∀ x∈s₂, s∈ W₂)
  (hs₁: W₁ = Submodule.span k s₁)
  (hs₂: W₂ = Submodule.span k s₂)
  (hw: ⊤ = W₁ ⊔ W₂)
  : ⊤ = Submodule.span k (s₁ ∪ s₂) := by  sorry
