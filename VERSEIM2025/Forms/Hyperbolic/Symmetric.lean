--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

-- import Mathlib.LinearAlgebra.QuadraticForm.Basic
-- import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import VERSEIM2025.Forms.Hyperbolic.Basics

/-
  The main results in this file should hold only for symmetric forms.

  Major results (Completed):
  - Symmetric bilinear form has orthogonal basis (from Mathlib)
  - Any nondegenerate symmetric bilinear form is the direct sum of a
    hyperbolic and anisotropic (definite) form

  Major results (Planned - Aspirational!) (These are listed in arbitrary order, and may not be correct)
  - Isomorphism classes of nondegenerate symmetric bilinear forms
  - Let the psuedo rank of a symmetric bilinear form be the maximal dimension
    of any anisotropic (definite) subspace. Prove that any two symmetric bilinear forms
    with the same dimension and psuedo rank are isomorphic.
  - Prove some sort of uniqueness of the hyperbolic + anisotropic (definite) decomposition
  - - I do not know if the subspaces are unique; if not then (if possible)
      prove if the dimensions are at least invariant.
 -/

namespace Symmetric

variable {k V V': Type} [AddCommGroup V][AddCommGroup V'] [Field k] [Module k V] [Module k V']

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Forms.Hyperbolic.BilinearForms
open Hyperbolic -- This is the namespace in VERSEIM2025.Forms.Hyperbolic.BilinearForms
open scoped Isometries

-- symmetric bilinear form has orthogonal basis, from Mathlib
example {V : Type u} {K : Type v}
   [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
   [hK : Invertible (2: K)] {B : LinearMap.BilinForm K V} (hB₂ : IsSymm B) :
    ∃ (v : Basis (Fin (Module.finrank K V)) K V), LinearMap.IsOrthoᵢ B ⇑v := by
      exact LinearMap.BilinForm.exists_orthogonal_basis hB₂

-- TODO: Remove redundancy with Symmetric
lemma ex_nonzero (h: Module.finrank k V > 0) : ∃(v: V), v ≠ 0  := by
  contrapose! h
  suffices Module.finrank k V=0 from Nat.le_zero.mpr this
  refine Module.finrank_eq_zero_of_rank_eq_zero ?_
  exact rank_zero_iff_forall_zero.mpr h

structure AnisotropicSubspace (B: BilinForm k V) where
  submodule : Submodule k V
  pred : ∀ v ∈ submodule, (B v v = 0 → v=0)

structure FooSymm {B: BilinForm k V} (bsymm: IsSymm B) where
  orthog : Hypsubspace B
  anisotropic : AnisotropicSubspace B
  compl : is_orthog_direct_sum B orthog.toSubmodule anisotropic.submodule

noncomputable def iso_FooSymm {B: BilinForm k V} {bsymm: IsSymm B} (H: FooSymm bsymm):
  V ≃[k, B, B.prod_subspaces _ _] H.orthog.toSubmodule × H.anisotropic.submodule :=
    (Isometries.from_is_orthog_direct_sum _ _ H.compl).symm

noncomputable def iso_orthog_FooSymm_equal_dim
  {B: BilinForm k V} {bsymm: IsSymm B}  {B': BilinForm k V} {bsymm': IsSymm B'}
  (H: FooSymm bsymm) (H': FooSymm bsymm') [FiniteDimensional k V] [FiniteDimensional k V']
  (h: Module.finrank k H.orthog.toSubmodule = Module.finrank k H'.orthog.toSubmodule):
  H.orthog.toSubmodule ≃[k, B.restrict _, B'.restrict _] H'.orthog.toSubmodule :=
    Hypsubspace.iso_from_iso_index_symm H.orthog H'.orthog
    (iso_index_from_rank_eq' _ _ h) bsymm bsymm'

noncomputable def iso_from_FooSymm_iso
  {B: BilinForm k V} {bsymm: IsSymm B}  {B': BilinForm k V'} {bsymm': IsSymm B'}
  (H: FooSymm bsymm) (H': FooSymm bsymm')
  (π₁: H.orthog.toSubmodule ≃[k, B.restrict _, B'.restrict _] H'.orthog.toSubmodule)
  (π₂: H.anisotropic.submodule ≃[k, B.restrict _, B'.restrict _] H'.anisotropic.submodule)
  : V ≃[k, B, B'] V' :=
    Isometries.trans (iso_FooSymm H) (Isometries.trans (π₁.prod π₂) (iso_FooSymm H').symm)

def FooSymm.mk' {B: BilinForm k V} (bsymm: IsSymm B) (orthog : Hypsubspace B)
  (anisotropic : AnisotropicSubspace B) (span: ⊤ ≤ orthog.toSubmodule ⊔ anisotropic.submodule)
  (mutually_orthog: OrthogSubspacesWeak B orthog.toSubmodule anisotropic.submodule)
  : FooSymm bsymm := by
  have compl: is_orthog_direct_sum B orthog.toSubmodule anisotropic.submodule := by
    refine is_orthog_direct_sum_of_is_orthog_direct_sum_weak_refl ?_ bsymm.isRefl
    constructor
    . constructor
      . suffices orthog.toSubmodule ⊓ anisotropic.submodule ≤  ⊥ from ?_
        . exact (Submodule.eq_bot_iff (orthog.toSubmodule ⊓ anisotropic.submodule)).mpr this
        intro a ⟨ha1, ha2⟩
        show a=0
        suffices B a a =0 from ?_
        . exact anisotropic.pred a ha2 this
        simp_all only [Hypsubspace.toSubmodule, Hypsubspace.toSubmodule,
           top_le_iff, OrthogSubspacesWeak,
          Hypsubspace.toSubmodule.eq_1, Subtype.forall,
          SetLike.mem_coe]
      . exact Submodule.eq_top_iff'.mpr fun x ↦ span trivial
    . exact mutually_orthog
  exact { orthog := orthog, anisotropic := anisotropic, compl := compl }

@[simp]
def ZeroHypSubspace (B: BilinForm k V): Hypsubspace B where
  I := Empty
  coe := fun _ ↦ 0
  pred :=
    { isotropic_left := by exact fun i j ↦ zero_left 0,
      isotropic_right := by exact fun i j ↦ zero_left 0,
      orthog1 := by exact fun i j a ↦ zero_left 0,
      orthog2 := by exact fun i j a ↦ zero_left 0,
      unital_corr := by
        intro i
        contradiction
    }



abbrev FooSymmPred {B: BilinForm k V} (bsymm: IsSymm B):= Nonempty (FooSymm bsymm)

def FooSymm_of_anisotropic {B: BilinForm k V} {bsymm: IsSymm B} (h: ∀ v, (B v v = 0) → v=0):
  FooSymmPred bsymm := by

  let anisotropicanisotropic: AnisotropicSubspace B :=
    {
      submodule := ⊤
      pred := by
        intro v _ hv
        exact h v hv
    }
  let zerohypsubspace:= ZeroHypSubspace B
  have zerohypsubspaceSubmodule: zerohypsubspace.toSubmodule  = ⊥ := by
    suffices zerohypsubspace.toSubmodule ≤ ⊥ from ?_
    . exact (Submodule.eq_bot_iff zerohypsubspace.toSubmodule).mpr this
    show Submodule.span k (Set.range zerohypsubspace.coe) ≤ ⊥
    suffices (Set.range zerohypsubspace.coe) ≤ (⊥: Submodule k V) from ?_
    . exact Submodule.span_le.mpr this
    rintro x ⟨i, rfl⟩
    exfalso
    have: IsEmpty zerohypsubspace.I := by
      show IsEmpty Empty
      exact Empty.instIsEmpty
    have: IsEmpty (zerohypsubspace.I ⊕zerohypsubspace.I)  := by
      exact instIsEmptySum
    exact IsEmpty.false i
  constructor
  exact {
    orthog := zerohypsubspace
    anisotropic := anisotropicanisotropic
    compl := by
      apply is_orthog_direct_sum_of_is_orthog_direct_sum_weak_refl _ bsymm.isRefl
      constructor
      . constructor
        . rw[zerohypsubspaceSubmodule]
          simp
        . show zerohypsubspace.toSubmodule ⊔ ⊤ = ⊤
          simp
      . intro a ha b hb
        rw[zerohypsubspaceSubmodule] at ha
        have: a = 0 := ha
        rw[this]
        simp
  }

noncomputable def FooSymmOfZeroSpace {B: BilinForm k V} (bsymm: IsSymm B) (h: ∀ (v: V), v = 0):
  FooSymmPred bsymm := by
  apply FooSymm_of_anisotropic
  exact fun v a ↦ h v

theorem SymmRestrict {B: BilinForm k V} (bsymm: IsSymm B) (W: Submodule k V): IsSymm (B.restrict W) := by
  intro x y
  dsimp
  exact bsymm ↑x ↑y


@[simp]
abbrev HypsubspaceRemoveFormRestriction {B: BilinForm k V} {W: Submodule k V}
  (H: Hypsubspace (B.restrict W)): Hypsubspace B where
  I := H.I
  coe := fun i => (H.coe i)
  pred := by
    constructor
    . intro i j
      have := H.pred.isotropic_left i j
      simp_all
    . intro i j
      have := H.pred.isotropic_right i j
      simp_all
    . intro i j h
      have := H.pred.orthog1 i j h
      simp_all
    . intro i j h
      have := H.pred.orthog2 i j h
      simp_all
    . intro i
      have := H.pred.unital_corr i
      simp_all

theorem HypsubspaceRemoveFormRestriction_WorksWell {B: BilinForm k V} {W: Submodule k V}
  (H: Hypsubspace (B.restrict W)): (HypsubspaceRemoveFormRestriction H).toSubmodule
     = H.toSubmodule.map W.subtype := by
    ext x
    constructor
    . intro hx
      dsimp at hx
      suffices Submodule.span k (Set.range fun i ↦ ↑(H.coe i)) ≤ Submodule.map W.subtype H.toSubmodule from ?_
      . exact this hx
      suffices (Set.range fun i ↦ (↑(H.coe i): V)) ≤ Submodule.map W.subtype H.toSubmodule from ?_
      . exact Submodule.span_le.mpr this
      intro x ⟨i, hix⟩
      dsimp at hix
      rw[<- hix]
      have: H.coe i ∈ H.toSubmodule := by exact Hypsubspace.contained H i
      use H.coe i
      constructor
      . exact this
      exact rfl
    . intro hx
      simp only [Hypsubspace.toSubmodule, HypsubspaceRemoveFormRestriction] at *
      rw[Submodule.map_span] at hx
      suffices ⇑W.subtype '' Set.range H.coe=Set.range fun i ↦ ↑(H.coe i) from ?_
      . rw[<- this]
        exact hx
      exact Eq.symm (Set.range_comp' Subtype.val H.coe)

theorem foo_helper1 {B: BilinForm k V} {W: Submodule k V} {x: V} {H: Hypsubspace (B.restrict W)}
  (hx: x ∈ (HypsubspaceRemoveFormRestriction H).toSubmodule): ∃(h: x ∈ W), ⟨x,h⟩ ∈ H.toSubmodule := by
    rw[HypsubspaceRemoveFormRestriction_WorksWell H] at hx
    simp_all

set_option pp.proofs true

lemma OrthogSubspacesMonotonicity {W₁ W₃: Submodule k V} {B: BilinForm k V}
  (W₂: Submodule k V) (h: OrthogSubspaces B W₁ W₂) (h': W₃ ≤ W₂): OrthogSubspaces B W₁ W₃ := by
  constructor
  . intro x hx y hy
    have hy': y ∈ W₂ := h' hy
    exact h.1 x hx y hy'
  . intro x hx y hy
    have hx': x ∈ W₂ := h' hx
    exact h.2 x hx' y hy


theorem FooSymmPredExpand {B: BilinForm k V} (bsymm: IsSymm B) (H: Hypsubspace B)
  (horthog: orthog_direct_sum B (H.toSubmodule)) (hsymmpredorthog: FooSymmPred
  (SymmRestrict bsymm (B.orthogonal H.toSubmodule))):
  FooSymmPred bsymm := by
    let ⟨⟨orthog, anisotropic, ⟨⟨spanOld, interOld⟩, ⟨comp21, comp22⟩ ⟩⟩⟩ := hsymmpredorthog
    let W := (B.orthogonal H.toSubmodule)
    let U := anisotropic.submodule
    let orthog_new: Hypsubspace B :=
      let horthogpartlynew: OrthogSubspaces B H.toSubmodule (HypsubspaceRemoveFormRestriction orthog).toSubmodule := by
        rw[HypsubspaceRemoveFormRestriction_WorksWell orthog]
        apply OrthogSubspacesMonotonicity (B.orthogonal H.toSubmodule) _  _
        . exact horthog.orthog
        . exact Submodule.map_subtype_le (B.orthogonal H.toSubmodule) orthog.toSubmodule
      let hinterpartlynew: H.toSubmodule ⊓ (HypsubspaceRemoveFormRestriction orthog).toSubmodule = (⊥: Submodule k V)  := by
        rw[HypsubspaceRemoveFormRestriction_WorksWell orthog]
        have hsdf: Submodule.map (B.orthogonal H.toSubmodule).subtype orthog.toSubmodule ≤ B.orthogonal H.toSubmodule := by
          exact Submodule.map_subtype_le (B.orthogonal H.toSubmodule) orthog.toSubmodule
        suffices H.toSubmodule ⊓ Submodule.map (B.orthogonal H.toSubmodule).subtype orthog.toSubmodule ≤ ⊥ from ?_
        . exact (Submodule.eq_bot_iff
                (H.toSubmodule ⊓
                  Submodule.map (B.orthogonal H.toSubmodule).subtype orthog.toSubmodule)).mpr
            this
        calc
          H.toSubmodule ⊓ Submodule.map (B.orthogonal H.toSubmodule).subtype orthog.toSubmodule ≤
             H.toSubmodule ⊓ B.orthogonal H.toSubmodule := by
           apply inf_le_inf_left _ hsdf
          _ = ⊥ := by
            apply horthog.ds.zero
      let his_orthog_indpartlynew : is_orthog_ind B H.toSubmodule (HypsubspaceRemoveFormRestriction orthog).toSubmodule := by
        exact { ind := hinterpartlynew, orthog := horthogpartlynew }
      Hypsubspace_of_orthog_ind his_orthog_indpartlynew
    let anisotropic_new: AnisotropicSubspace B :=
      {
      submodule := U.map W.subtype,
      pred := by
        rintro v h h'
        have ⟨u, huU, huv⟩ := Submodule.mem_map.mp h
        suffices u=0 from ?_
        . have: W.subtype u = 0 := by exact
          (AddSubmonoid.mk_eq_zero (B.orthogonal H.toSubmodule).toAddSubmonoid).mp this
          rw[<- huv,this]
        suffices B (W.subtype u) (W.subtype u) = 0 from ?_
        . apply anisotropic.pred
          . exact huU
          rw[<- this]
          simp
        rw[huv]
        exact h'
      }

    have anisotropic_new_anisotropic_compatible: (anisotropic.submodule).map (B.orthogonal H.toSubmodule).subtype = anisotropic_new.submodule := by
      exact rfl

    have span: ⊤ ≤ orthog_new.toSubmodule ⊔ anisotropic_new.submodule := by
      unfold orthog_new
      rw[Hypsubspace_of_direct_sum_Hypsubspaces]
      rw[sup_assoc]
      have : ((HypsubspaceRemoveFormRestriction orthog).toSubmodule ⊔ anisotropic_new.submodule) = B.orthogonal H.toSubmodule := by
        rw[HypsubspaceRemoveFormRestriction_WorksWell orthog]
        rw[<- anisotropic_new_anisotropic_compatible]
        rw [← @Submodule.map_sup]
        rw [interOld]
        rw [@Submodule.map_subtype_top]
      rw[this]
      rw[horthog.ds.span]
    have mutually_orthog: OrthogSubspacesWeak B orthog_new.toSubmodule anisotropic_new.submodule := by
      unfold OrthogSubspacesWeak
      rw[Hypsubspace_of_direct_sum_Hypsubspaces]
      intro x hx y hy
      have hyuw : y ∈ U.map W.subtype := hy
      have: ∃ x₁ ∈ H.toSubmodule, ∃ x₂ ∈ ((HypsubspaceRemoveFormRestriction orthog).toSubmodule),
        x₁ + x₂ = x := by exact Submodule.mem_sup.mp hx
      have ⟨x₁, hx₁, x₂, hx₂, hx1x2x⟩ := this
      show B x y = 0
      rw[<- hx1x2x]
      suffices B x₁ y = 0 ∧ B x₂ y = 0 from ?_
      . have ⟨h1,h2⟩ := this
        rw[map_add, LinearMap.add_apply, h1, h2, add_zero]
      constructor
      have hyW: y ∈ W := by
          have ⟨⟨u, hu⟩ , huy1, huy2⟩ := hyuw
          rw[<- huy2]
          exact hu
      . apply hyW
        exact hx₁
      . have hyW: y ∈ W := by
          have ⟨⟨u, hu⟩ , huy1, huy2⟩ := hyuw
          rw[<- huy2]
          exact hu
        have ⟨⟨u, hu⟩ , huy1, huy2⟩ := hyuw
        rw[<- huy2]
        have h1: OrthogSubspaces (B.restrict (B.orthogonal H.toSubmodule)) orthog.toSubmodule
          anisotropic.submodule := ⟨comp21, comp22⟩
        have h2: OrthogSubspacesWeak (B.restrict (B.orthogonal H.toSubmodule)) orthog.toSubmodule
          anisotropic.submodule := comp21
        have ⟨hx₂, hx₂proof⟩ := foo_helper1 hx₂
        have: (B.restrict (B.orthogonal H.toSubmodule)) ⟨x₂, hx₂⟩ ⟨u, hu⟩ = B x₂ (W.subtype ⟨u, hu⟩) := by
          simp
        rw[<- this]
        apply h2
        . exact hx₂proof
        exact huy1
    exact Nonempty.intro <| FooSymm.mk' bsymm orthog_new anisotropic_new span mutually_orthog

theorem OneDegNonDegenerateIsAnisotropic {B: BilinForm k V} (hrank: Module.finrank k V = 1) (hf: Nondegenerate B)
  : ∀ v, (B v v = 0) → v=0 := by
    intro v hv
    by_contra h
    have: ∀ w, ∃ (c: k), c • v = w := by
      exact fun w ↦ exists_smul_eq_of_finrank_eq_one hrank h w
    contrapose! hf
    have: ∀ w, B v w = 0 := by
      intro w
      have ⟨c, hc⟩ := this w
      rw[<- hc]
      simp[hv]
    exact fun a ↦ h (a v this)

theorem OneDimIsFooSymm {B: BilinForm k V} (bsymm: IsSymm B) (hrank: Module.finrank k V = 1)
  (hd: Nondegenerate B):
  FooSymmPred bsymm := by
  have := OneDegNonDegenerateIsAnisotropic  hrank hd
  apply FooSymm_of_anisotropic this

protected theorem symmetric_is_FooSymmPred (p: ℕ)  (B: BilinForm k V) (bsymm: IsSymm B) [FiniteDimensional k V]
 (hd: B.Nondegenerate) [CharP k p] (hn2 : p ≠ 2): FooSymmPred bsymm  := by
  suffices ∀ n, (hn: n = Module.finrank k V) → FooSymmPred bsymm from this (Module.finrank k V) rfl
  intro n hn
  induction' n using Nat.strong_induction_on with n h generalizing V
  have hr : IsRefl B := IsSymm.isRefl bsymm
  case h =>
  match n with
  | 0 =>
    have: ∀ (v: V), v = 0 := by
      symm at hn
      exact finrank_zero_iff_forall_zero.mp hn
    exact FooSymmOfZeroSpace bsymm this
  | 1 =>
    have: Module.finrank k V = 1 := by exact id (Eq.symm hn)
    exact OneDimIsFooSymm bsymm this hd
  | m+2 =>
    by_cases h':(∃ (e: V), e ≠ 0 ∧ B e e =0)
    . have ⟨e, he_nonzero, he_isotropic⟩ := h'
      let ⟨f, hef⟩ := hyp_pair_exists_symm p bsymm hd he_nonzero he_isotropic hn2
      let H : Hypsubspace B := Hypsubspace_two hef
      let W' := B.orthogonal H.toSubmodule
      have hHW' : is_orthog_direct_sum B H.toSubmodule W' := hyp2_decomp_refl B hr hef
      have hpredW' : FooSymmPred (SymmRestrict bsymm W') := by
        have hmm2: m < m+2 := Nat.lt_add_of_pos_right (Nat.zero_lt_two)
        have hbW'IsGoodProp: (B.restrict W').IsSymm := fun x ↦ fun y ↦ bsymm (W'.subtype x) (W'.subtype y)
        have hIsComplW'H: IsCompl H.toSubmodule W' := by
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
        exact h m hmm2 (B.restrict W') hbW'IsGoodProp hBW'Nondegenerate hWrankeqm
      exact FooSymmPredExpand bsymm H hHW' hpredW'
    . have: ∀ (v: V), (B v v = 0 → v=0) := by
        intro v h
        contrapose! h'
        use v
      exact FooSymm_of_anisotropic this


noncomputable def FooSymm_of_FooSymmPred {B: BilinForm k V} {bsymm: IsSymm B} (h: FooSymmPred bsymm): FooSymm bsymm := by
    apply Classical.choice
    have ⟨H⟩ := h
    constructor
    exact H


noncomputable def symmetric_is_FooSymm  (p: ℕ)  {B: BilinForm k V} (bsymm: IsSymm B) (hd: B.Nondegenerate) [FiniteDimensional k V]
  [CharP k p] (hn2 : p ≠ 2):
  FooSymm bsymm :=
    FooSymm_of_FooSymmPred <| Symmetric.symmetric_is_FooSymmPred p B bsymm hd hn2

-- lemma exists_bilin_one_strong {e: V} {B: BilinForm k V} (enz: e ≠ 0)
  -- (hn: Nondegenerate B): True := sorry


theorem isotropic_IsAlgClosed {B: BilinForm k V}  (hs: IsSymm B) (hd: Module.finrank k V ≥ 2)
  [IsAlgClosed k]: ∃ v, B v v = 0 ∧ v ≠ 0 := by
  have :=   Basis.ofVectorSpace k V
  obtain ⟨f, hf⟩  := exists_linearIndependent_of_le_finrank hd
  let v := f 0
  let w := f 1
  have hw_neq_zero: w ≠ 0 := sorry
  let p: Polynomial k :=
    Polynomial.monomial 0 (B v v)
    + Polynomial.monomial 1 (B v w)
    + Polynomial.monomial 2 (B w w)
  by_cases hw: B w w = 0
  . use w
  sorry

theorem degree_Anisotropic_IsAlgClosed {B: BilinForm k V}  (hs: IsSymm B)
  (H: AnisotropicSubspace B) [IsAlgClosed k]: Module.finrank k H.submodule ≤ 1 := by
  obtain ⟨W, pred⟩ := H
  simp only
  contrapose! pred
  have pred: Module.finrank k W ≥ 2 := by omega
  have: IsSymm (B.restrict W) := fun x y ↦ hs (W.subtype x) (W.subtype y)
  have := isotropic_IsAlgClosed this pred
  obtain ⟨⟨w, hw⟩, h1, h2⟩ := this
  use w
  constructor
  . exact hw
  constructor
  . simpa using h1
  . simpa using h2

theorem FooSymmPred_rank_sum {B: BilinForm k V} {bsymm: IsSymm B} (H: FooSymm bsymm)
  [FiniteDimensional k V]: Module.finrank k V = Module.finrank k (H.orthog.toSubmodule) +
    Module.finrank k (H.anisotropic.submodule)
    := by
  rw [← @Submodule.finrank_sup_add_finrank_inf_eq, H.compl.ds.span,H.compl.ds.zero]
  simp

lemma arithmetic_lemma (a b c d: ℕ) (ha: a =0 ∨ a=1) (hb: b=0 ∨ b=1) (h: a+c=b+d)
  (hc: Even c) (hd: Even d): a=b ∧ c=d := by
  rcases ha with ha_zero | ha_one
  . rcases hb with hb_zero | hb_one
    . omega
    . exfalso
      have h1: Odd (b+d) := by
        rw[hb_one]
        exact Even.one_add hd
      have h2: Even (b+d) := by
        rw[<- h, ha_zero, zero_add]
        exact hc
      rw[<- Nat.not_odd_iff_even] at h2
      exact h2 h1
  . rcases hb with hb_zero | hb_one
    . exfalso
      have h1: Odd (b+d) := by
        rw[<- h, ha_one]
        exact Even.one_add hc
      have h2: Even (b+d) := by
        rw[hb_zero, zero_add]
        exact hd
      rw[<- Nat.not_odd_iff_even] at h2
      exact h2 h1
    . omega


noncomputable def symm_iso {B: BilinForm k V} (bsymm: IsSymm B) (hn: B.Nondegenerate)
{B': BilinForm k V'} (bsymm': IsSymm B') (hn': B'.Nondegenerate)
(hk: ringChar k ≠ 2) [FiniteDimensional k V] [FiniteDimensional k V']
(hd: Module.finrank k V = Module.finrank k V') [IsAlgClosed k]: V ≃[k, B, B'] V' := by

  have H: FooSymm bsymm := symmetric_is_FooSymm (ringChar k) bsymm hn hk
  have H': FooSymm bsymm' := symmetric_is_FooSymm (ringChar k) bsymm' hn' hk

  have h1: Module.finrank k H.anisotropic.submodule ≤ 1 :=
    degree_Anisotropic_IsAlgClosed bsymm H.anisotropic
  have h2: Module.finrank k H'.anisotropic.submodule ≤ 1 :=
    degree_Anisotropic_IsAlgClosed bsymm' H'.anisotropic

  have h3: Module.finrank k H.orthog.toSubmodule + Module.finrank k H.anisotropic.submodule
      =  Module.finrank k H'.orthog.toSubmodule + Module.finrank k H'.anisotropic.submodule
      := by rw[<- FooSymmPred_rank_sum, <- FooSymmPred_rank_sum, hd]

  have: Module.finrank k H.anisotropic.submodule = Module.finrank k H'.anisotropic.submodule ∧
   Module.finrank k H.orthog.toSubmodule = Module.finrank k H'.orthog.toSubmodule
     := by
      apply arithmetic_lemma
      . omega
      . omega
      . rw[add_comm, h3, add_comm]
      . exact H.orthog.is_even_dimension
      . exact H'.orthog.is_even_dimension
  obtain ⟨h5, h4⟩  :=  this

  have π₁: H.orthog.toSubmodule ≃[k, B.restrict _, B'.restrict _] H'.orthog.toSubmodule := by
    apply H.orthog.iso_from_iso_index H'.orthog (iso_index_from_rank_eq' H.orthog H'.orthog h4)
    intro i
    let i' := iso_index_from_rank_eq' H.orthog H'.orthog h4 i
    show (B (H.orthog.basis (Sum.inr i))) (H.orthog.basis (Sum.inl i)) =
      (B' (H'.orthog.basis (Sum.inr i')) (H'.orthog.basis (Sum.inl i')))
    have h1 : B (H.orthog.basis (Sum.inr i)) (H.orthog.basis (Sum.inl i))
      = B (H.orthog.basis (Sum.inl i)) (H.orthog.basis (Sum.inr i)):= bsymm _ _
    have h2: B' (H'.orthog.basis (Sum.inr i')) (H'.orthog.basis (Sum.inl i'))
      = B' (H'.orthog.basis (Sum.inl i')) (H'.orthog.basis (Sum.inr i')):= bsymm' _ _
    rw[h1 ]
    rw[h2]
    simp

  have π₂: H.anisotropic.submodule ≃[k, B.restrict _, B'.restrict _] H'.anisotropic.submodule := by
    by_cases hHd: Module.finrank k H.anisotropic.submodule=0
    . have hHd': Module.finrank k H'.anisotropic.submodule=0 := by rw[<- h5, hHd]
      exact Isometries.from_zero_dim hHd hHd'
    . have hHd: Module.finrank k H.anisotropic.submodule=1 := by omega
      have hHd': Module.finrank k H'.anisotropic.submodule=1 := by rw[<- h5, hHd]
      refine Isometries.from_one_dim hHd hHd' ?_ ?_
      . rintro ⟨v, hv⟩
        simp only [restrict_apply, LinearMap.domRestrict_apply, Submodule.mk_eq_zero]
        exact H.anisotropic.pred v hv
      . rintro ⟨v, hv⟩
        simp only [restrict_apply, LinearMap.domRestrict_apply, Submodule.mk_eq_zero]
        exact H'.anisotropic.pred v hv
  exact iso_from_FooSymm_iso H H' π₁ π₂


end Symmetric
