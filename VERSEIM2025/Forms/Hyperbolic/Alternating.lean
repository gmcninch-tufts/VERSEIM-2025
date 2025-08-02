--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.Forms.Hyperbolic.Basics

/-
  Major results (Completed)
  - Any nondegenerate alternating bilinear form is hyperbolic (`alternating_is_hyperbolic`)
    - Corollary: Nondegenerate alternating bilinear form is dimension 2n (`alternate_is_even_dimension`)
  - - Corollary: Nondegenerate alternating bilinear forms of equal (finite) dimension
      are isomorphic (as bilinear form spaces)  (`alternate_iso`)
-/

namespace Alternating


variable {k V V': Type} [AddCommGroup V][AddCommGroup V'] [Field k] [Module k V] [Module k V']


open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Forms.Hyperbolic.BilinearForms
open Hyperbolic -- This is the namespace in VERSEIM2025.Forms.Hyperbolic.BilinearForms
open scoped Isometries


lemma ex_nonzero (h: Module.finrank k V > 0) : ∃(v: V), v ≠ 0  := by
  contrapose! h
  suffices Module.finrank k V=0 from Nat.le_zero.mpr this
  refine Module.finrank_eq_zero_of_rank_eq_zero ?_
  exact rank_zero_iff_forall_zero.mpr h

noncomputable def alternating_is_hyperbolic {B: BilinForm k V} (balt: IsAlt B) (hd: B.Nondegenerate) [FiniteDimensional k V]:
  Hypspace B := by
  suffices ∀ n, n=Module.finrank k V → Hypspace_pred B from Hypspace_of_Hypspace_pred (this (Module.finrank k V) rfl)
  intro n hn
  induction' n using Nat.strong_induction_on with n h generalizing V
  have hr : IsRefl B := IsAlt.isRefl balt
  case h =>
  match n with
  | 0 =>
    refine Hypspace_pred_of_Hypspace ?_
    refine Hypspace_zero ?_
    symm at hn
    exact finrank_zero_iff_forall_zero.mp hn
  | 1 =>
    have: Module.finrank k V = 1 := by exact id (Eq.symm hn)
    have ⟨v, vnonzero, vspan⟩ := finrank_eq_one_iff'.mp this
    contrapose! vnonzero
    apply hd v
    intro w
    have ⟨c, hc⟩ := vspan w
    rw[<- hc, smul_right_of_tower c v v, balt v, smul_zero c]
  | m+2 =>
    have: ∃ (e: V), e ≠ 0 := by
      have: m+2 > 0 := by exact Nat.zero_lt_succ (m + 1)
      rw[hn] at this
      exact ex_nonzero this
    let ⟨e, he⟩ := this
    let ⟨f, hef⟩ := hyp_pair_exists_alt balt hd he
    let H : Hypsubspace B := Hypsubspace_two hef
    let W' := B.orthogonal H.toSubmodule
    have hHW' : is_orthog_direct_sum B H.toSubmodule W' := hyp2_decomp_refl B hr hef
    have hpredW' : Hypspace_pred (B.restrict W') := by
      have hmm2: m < m+2 := Nat.lt_add_of_pos_right (Nat.zero_lt_two)
      have hbW'IsGoodProp: (B.restrict W').IsAlt := fun x ↦ balt (W'.subtype x)
      have hIsComplW'H: IsCompl H.toSubmodule W'  := by
          exact BilinearForms.isCompl_orthogonal_of_restrict_nondegenerate B H.toSubmodule
            (hyp2_nondeg_refl B (hr) hef)
      have hWrankeqm: m = Module.finrank k ↥W' := by
        have: Module.finrank k ↥W' + Module.finrank k H.toSubmodule = Module.finrank k V := by
          rw[add_comm]
          exact Submodule.finrank_add_eq_of_isCompl hIsComplW'H
        rw[Hypsubspace_two_finrank_2,<- hn] at this
        exact (Nat.add_right_cancel this).symm
      have hBW'Nondegenerate: (B.restrict W').Nondegenerate := by
        apply (restrict_nondegenerate_iff_isCompl_orthogonal hr).mpr
        rw[orthogonal_orthogonal hd (hr) H.toSubmodule]
        exact id (IsCompl.symm hIsComplW'H)
      exact h m hmm2 hbW'IsGoodProp hBW'Nondegenerate hWrankeqm
    have ⟨H', _⟩ := Hypsubspace_of_Hypspace_pred_restrict hpredW'
    have h: is_orthog_direct_sum B H.toSubmodule H'.toSubmodule := by
      simp_all
    exact Hypspace_pred_of_Hypspace (Hypspace_of_orthog_direct_sum' h)


theorem alternate_is_even_dimension {B: BilinForm k V} (balt: IsAlt B) (hd: B.Nondegenerate):
  Even (Module.rank k V) := by
  by_cases FiniteDimensional k V
  . have h := (alternating_is_hyperbolic balt hd).is_even_dimension
    suffices Module.finrank k V = Module.rank k V from ?_
    . let ⟨r,hr⟩ := h
      rw[<- this]
      use r
      simp[hr]
    exact Module.finrank_eq_rank k V
  . have ⟨s, ⟨b⟩ ⟩ := Basis.exists_basis k V
    have: Module.rank k V = Cardinal.mk s := by exact Eq.symm (Basis.mk_eq_rank'' b)
    rw[this]
    have: Cardinal.aleph0 ≤ Cardinal.mk s := by
      refine Cardinal.infinite_iff.mp ?_
      refine not_finite_iff_infinite.mp ?_
      intro h
      have: FiniteDimensional k V := by exact Module.Finite.of_basis b
      contradiction
    use (Cardinal.mk s)
    exact Eq.symm (Cardinal.add_eq_self this)

noncomputable def alternate_iso {B: BilinForm k V} {B': BilinForm k V'} (balt: IsAlt B) (b'alt: IsAlt B')
  (hd: B.Nondegenerate) (hd': B'.Nondegenerate) [FiniteDimensional k V] [FiniteDimensional k V']
  (h: Module.finrank k V = Module.finrank k V'): V ≃[k, B, B'] V' := by
    let H := alternating_is_hyperbolic balt hd
    let H' := alternating_is_hyperbolic b'alt hd'
    apply H.iso_from_iso_index H' (iso_index_from_rank_eq H H' h)
    intro i
    let i' := iso_index_from_rank_eq H H' h i
    show (B (H.basis (Sum.inr i))) (H.basis (Sum.inl i)) =
      (B' (H'.basis (Sum.inr i')) (H'.basis (Sum.inl i')))
    let bskew := skew_of_alt B balt
    let b'skew := skew_of_alt B' b'alt
    rw[bskew]
    rw[b'skew]
    simp

end Alternating
