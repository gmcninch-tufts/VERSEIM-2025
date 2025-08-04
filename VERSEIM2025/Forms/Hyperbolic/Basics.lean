--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.Forms.Isometries


/-
  This file states definitions for Hyperbolic forms and theorems
  relating the different viewpoints together.
-/

namespace Hyperbolic

variable {k V: Type} [AddCommGroup V][Field k][Module k V]

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms
open scoped Isometries

@[simp]
abbrev isotropic (B: BilinForm k V) (e: V) := B e e = 0

/-- left for *e*, right for *f*, i.e.
      eᵢ = Sum.inl i
      fᵢ = Sum.inr i
    Essentially each Span (eᵢ, fᵢ) is a hyperbolic 2-space and the span of b
      is a direct sum of these 2-spaces.
 -/
@[ext]
structure Hypspace_fun_pred {I: Type} (B: BilinForm k V) (b: I ⊕ I → V) where
  isotropic_left : ∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0
  isotropic_right : ∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0 -- B fᵢ fⱼ = 0 ∀ i j
  orthog1: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inl i)) (b (Sum.inr j)) = 0 -- B eᵢ fⱼ = 0 for i ≠ j
  orthog2: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inr i)) (b (Sum.inl j)) = 0 -- B fᵢ eⱼ = 0 for i ≠ j
  unital_corr: ∀ i, B (b (Sum.inl i)) (b (Sum.inr i)) = 1 -- B eᵢ fᵢ = 1 ∀ i

/-- There exists a basis such that `Hypspace_fun_pred` holds. -/
def Hypspace_pred (B: BilinForm k V): Prop
  := ∃(I: Type), ∃ (b: Basis (I ⊕ I)  k V), Hypspace_fun_pred B b

/-- A Hyperbolic Space

  Contains a basis which satisfies `Hypspace_fun_pred`-/
@[ext]
structure Hypspace (B: BilinForm k V) where
  I: Type
  basis : Basis (I ⊕ I) k V
  pred: Hypspace_fun_pred B basis

/-- The zero vector space is Hyperbolic. -/
noncomputable def Hypspace_zero {B: BilinForm k V} (h: ∀ (v: V), v=0): Hypspace B where
  I := Empty
  basis := by
    have h': Module.rank k V =0 := rank_zero_iff_forall_zero.mpr h
    exact Basis.ofRankEqZero h'
  pred := {
    isotropic_left := fun i => by contradiction,
    isotropic_right := fun i => by contradiction,
    orthog1 := fun i => by contradiction,
    orthog2 := fun i => by contradiction,
    unital_corr := fun i => by contradiction }

/-- The basis index type `H.I ⊕ H.I` for `H: Hypspace`.

    Created to maintain standard with `OddHyperbolic` and `GeneralizedHyperbolic` in
    `OddHyperbolicForms.lean`-/
@[simp]
abbrev Hypspace.basis_index {B: BilinForm k V} (H: Hypspace B) := H.I ⊕ H.I

/-- Noncomputably yields a `Hypspace` from `Hypspace_pred`-/
noncomputable def Hypspace_of_Hypspace_pred {B: BilinForm k V} (h: Hypspace_pred B): Hypspace B := by
    apply Classical.choice
    have ⟨H⟩: Nonempty (Hypspace B) := by
      have ⟨I, b, hbI⟩ := h
      constructor
      exact Hypspace.mk I b hbI
    constructor
    exact H

/-- The Bilinear form associated to a `Hypspace` satisfies `Hypspace_pred`-/
theorem Hypspace_pred_of_Hypspace {B: BilinForm k V} (H: Hypspace B):
  Hypspace_pred B:= by
    use H.I
    use H.basis
    exact H.pred


@[ext]
structure Hypsubspace (B: BilinForm k V) where
  I: Type
  coe : I ⊕ I → V
  pred: Hypspace_fun_pred B coe

@[simp]
abbrev Hypsubspace.basis_index {B: BilinForm k V} (H: Hypsubspace B) := H.I ⊕ H.I


@[simp]
theorem HypsubspacePred_isotropic_left {I: Type} {B: BilinForm k V} (b: I ⊕ I → V) (hb: Hypspace_fun_pred B b) (i j: I):
  B (b (Sum.inl i)) (b (Sum.inl j))=0 := hb.isotropic_left i j

@[simp]
theorem HypsubspacePred_isotropic_right {I: Type} {B: BilinForm k V} (b: I ⊕ I → V) (hb: Hypspace_fun_pred B b) (i j: I):
  B (b (Sum.inr i)) (b (Sum.inr j))=0 := hb.isotropic_right i j

@[simp]
theorem HypsubspacePred_orthog1 {I: Type} {B: BilinForm k V} (b: I ⊕ I → V) (hb: Hypspace_fun_pred B b) (i j: I) (h: i ≠ j):
  B (b (Sum.inl i)) (b (Sum.inr j)) = 0 := hb.orthog1 i j h

@[simp]
theorem HypsubspacePred_orthog2 {I: Type} {B: BilinForm k V} (b: I ⊕ I → V) (hb: Hypspace_fun_pred B b) (i j: I) (h: i ≠ j):
  B (b (Sum.inr i)) (b (Sum.inl j)) = 0 := hb.orthog2 i j h

@[simp]
theorem HypsubspacePred_orthog {I: Type} {B: BilinForm k V} (b: I ⊕ I → V) (hb: Hypspace_fun_pred B b) (i: I) {x: I ⊕ I} (hxi: x ≠ Sum.inl i):
  B (b x) (b (Sum.inr i)) = 0 :=
  match x with
  | Sum.inl j => by simp_all
  | Sum.inr j => by simp_all

@[simp]
theorem HypsubspacePred_orthog' {I: Type} {B: BilinForm k V} (b: I ⊕ I → V) (hb: Hypspace_fun_pred B b) (i: I) {x: I ⊕ I} (hxi: x ≠ Sum.inr i):
  B (b (Sum.inl i)) (b x) = 0 :=
  match x with
  | Sum.inl j => by simp_all
  | Sum.inr j => by
    symm at hxi
    simp_all

@[simp]
theorem HypsubspacePred_unital_corr {I: Type} {B: BilinForm k V} (b: I ⊕ I → V) (hb: Hypspace_fun_pred B b) (i: I):
  B (b (Sum.inl i)) (b (Sum.inr i)) = 1 := hb.unital_corr i

@[simp]
theorem Hypspace_isotropic_left {B: BilinForm k V} (H: Hypspace B) (i j: H.I):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inl j))=0 := H.pred.isotropic_left i j

@[simp]
theorem Hypspace_isotropic_right {B: BilinForm k V} (H: Hypspace B) (i j: H.I):
  B (H.basis (Sum.inr i)) (H.basis (Sum.inr j))=0 := H.pred.isotropic_right i j

@[simp]
theorem Hypspace_orthog1 {B: BilinForm k V} (H: Hypspace B) (i j: H.I) (h: i ≠ j):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inr j)) = 0 := H.pred.orthog1 i j h

@[simp]
theorem Hypspace_orthog2 {B: BilinForm k V} (H: Hypspace B) (i j: H.I) (h: i ≠ j):
  B (H.basis (Sum.inr i)) (H.basis (Sum.inl j)) = 0 := H.pred.orthog2 i j h

@[simp]
theorem Hypspace_unital_corr {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inr i)) = 1 := H.pred.unital_corr i


@[simp]
theorem Hypsubspace_isotropic_left {B: BilinForm k V} (H: Hypsubspace B) (i j: H.I):
  B (H.coe (Sum.inl i)) (H.coe (Sum.inl j))=0 := H.pred.isotropic_left i j

@[simp]
theorem Hypsubspace_isotropic_right {B: BilinForm k V}  (H: Hypsubspace B) (i j: H.I):
  B (H.coe (Sum.inr i)) (H.coe (Sum.inr j))=0 := H.pred.isotropic_right i j

@[simp]
theorem Hypsubspace_orthog1 {B: BilinForm k V} (H: Hypsubspace B) (i j: H.I) (h: i ≠ j):
  B (H.coe (Sum.inl i)) (H.coe (Sum.inr j)) = 0 := H.pred.orthog1 i j h

@[simp]
theorem Hypsubspace_orthog2 {B: BilinForm k V} (H: Hypsubspace B) (i j: H.I) (h: i ≠ j):
  B (H.coe (Sum.inr i)) (H.coe (Sum.inl j)) = 0 := H.pred.orthog2 i j h

@[simp]
theorem Hypsubspace_unital_corr {B: BilinForm k V} (H: Hypsubspace B) (i: H.I):
  B (H.coe (Sum.inl i)) (H.coe (Sum.inr i)) = 1 := H.pred.unital_corr i

@[simp]
theorem Hypsubspace_orthog {B: BilinForm k V} (H: Hypsubspace B) (i: H.I) {x: H.I ⊕ H.I} (hxi: x ≠ Sum.inl i):
  B (H.coe x) (H.coe (Sum.inr i)) = 0 :=
  match x with
  | Sum.inl j => by simp_all
  | Sum.inr j => by simp_all

@[simp]
theorem Hypsubspace_orthog' {B: BilinForm k V} (H: Hypsubspace B) (i: H.I) {x: H.I ⊕ H.I} (hxi: x ≠ Sum.inr i):
  B (H.coe (Sum.inl i)) (H.coe x) = 0 :=
  match x with
  | Sum.inl j => by simp_all
  | Sum.inr j => by
    symm at hxi
    simp_all

lemma bilin_commute_lincomb_nice {I: Type} {B: BilinForm k V} (g : I → V) (f: I →₀ k) (v: V):
  (B ((Finsupp.linearCombination k g) f)) v
       = Finsupp.linearCombination k (fun j => B (g j) v) f := by
  simp [Finsupp.linearCombination_apply, map_finsuppSum]

lemma lincomb_single_nice {I: Type} (i: I) (f: I →₀ k) :
  (Finsupp.linearCombination k ⇑(Finsupp.single i 1)) f = f i := by
  rw [@Finsupp.linearCombination_apply]
  simp[Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    suffices ((Finsupp.single i 1) j : k)=0 from ?_
    . rw[this]
      ring
    exact Finsupp.single_eq_of_ne (id (Ne.symm hj))
  · intro hi
    have: f i = 0 := by
      exact Finsupp.notMem_support_iff.mp hi
    exact mul_eq_zero_of_left this ((Finsupp.single i 1) i)

theorem Hypspace_repr_left {I: Type} {B: BilinForm k V} (coe : I ⊕ I → V) (f: I ⊕ I →₀ k)
  (pred: Hypspace_fun_pred B coe) (i: I):
  B (Finsupp.linearCombination k coe f) (coe (Sum.inr i))= f (Sum.inl i) := by

    have: (B ((Finsupp.linearCombination k coe) f)) (coe (Sum.inr i))
       = Finsupp.linearCombination k (fun (j: I ⊕ I) => B (coe j) (coe (Sum.inr i)) ) f := by
       rw[bilin_commute_lincomb_nice]
    rw[this]
    have: (fun (j: I ⊕ I) ↦ B ((coe j)) (coe (Sum.inr i)) ) = Finsupp.single (Sum.inl i: I ⊕ I) 1 := by
      ext x
      by_cases h:x=Sum.inl i
      . rw [h]
        rw [pred.unital_corr i]
        exact Eq.symm Finsupp.single_eq_same
      . have: Sum.inl i ≠ x := by exact fun a ↦ h (id (Eq.symm a))
        simp_all[Finsupp.single_eq_of_ne,this]
    rw[this]
    exact lincomb_single_nice _ f

theorem Hypspace_repr_right {I: Type} {B: BilinForm k V} (coe : I ⊕ I → V) (f: I ⊕ I →₀ k)
  (pred: Hypspace_fun_pred B coe) (i: I):
  B (coe (Sum.inl i)) (Finsupp.linearCombination k coe f) = f (Sum.inr i) := by
    have: (B (coe (Sum.inl i)) ((Finsupp.linearCombination k coe) f))
       = Finsupp.linearCombination k (fun (j: I ⊕ I) => B  (coe (Sum.inl i)) (coe j) ) f := by
      simp [Finsupp.linearCombination_apply, map_finsuppSum]
    rw[this]
    have: (fun (j: I ⊕ I) ↦ B (coe (Sum.inl i)) ((coe j))  ) = Finsupp.single (Sum.inr i: I ⊕ I) 1 := by
      ext x
      by_cases h:x=Sum.inr i
      . rw [h]
        simp_all
      . have: Sum.inr i ≠ x := by exact fun a ↦ h (id (Eq.symm a))
        simp_all[Finsupp.single_eq_of_ne,this]
    rw[this]
    exact lincomb_single_nice _ f


theorem Hypsubspace.linind {B: BilinForm k V} (H: Hypsubspace B):
  LinearIndependent k H.coe := by
  rw[linearIndependent_iff]
  intro f hf
  have hleft: ∀ i, f (Sum.inl i) = 0 := by
    intro i
    rw[<- Hypspace_repr_left H.coe f H.pred]
    rw[hf]
    exact zero_left (H.coe (Sum.inr i))
  have hright: ∀ i, f (Sum.inr i) = 0 := by
    intro i
    rw[<- Hypspace_repr_right H.coe f H.pred]
    rw[hf]
    exact zero_right (H.coe (Sum.inl i))
  have: ∀ i, f i = 0 := fun i =>
    match i with
    | Sum.inl i => hleft i
    | Sum.inr i => hright i
  exact Finsupp.ext this

@[simp]
theorem Hypsubspace.contained' {B: BilinForm k V} (H: Hypsubspace B) (i: H.I ⊕ H.I):
  H.coe i ∈ (Submodule.span k (Set.range H.coe)) := by
    suffices H.coe i ∈ Set.range H.coe from Submodule.mem_span_of_mem this
    exact Set.mem_range_self i

@[simp]
def Hypsubspace.toSubmodule {B: BilinForm k V} (H : Hypsubspace B) : Submodule k V :=
  Submodule.span k (Set.range H.coe)

theorem Hypsubspace.contained {B: BilinForm k V} (H: Hypsubspace B) (i: H.I ⊕ H.I):
  H.coe i ∈ H.toSubmodule := H.contained' i

lemma compatible_submodule_sum {I: Type} (W: Submodule k V) (coe: I → V) (hcoe: ∀ i, coe i ∈ W)
  (f: I →₀ k):
  (Finsupp.linearCombination k fun i ↦ coe i) f = (Finsupp.linearCombination k fun i ↦
      ((⟨coe i, hcoe i⟩): W) ) f := by
    have h0: (((Finsupp.linearCombination k fun i ↦ ((⟨coe i, hcoe i⟩): W) ) f): V)
      = W.subtype ((Finsupp.linearCombination k fun i ↦ ((⟨coe i, hcoe i⟩): W) ) f) := by
      exact rfl
    rw[h0]
    rw[LinearMap.map_finsupp_linearCombination]
    exact rfl

lemma linear_independence_submodule {I: Type} (W: Submodule k V) (coe: I → V) (hcoe: ∀ i, coe i ∈ W)
  (hlin: LinearIndependent k coe): LinearIndependent k (fun i => (⟨coe i, hcoe i⟩: W) ) := by
    intro f g hfgsumeq
    have (func: I →₀ k): (Finsupp.linearCombination k fun i ↦ coe i) func = (Finsupp.linearCombination k fun i ↦
      ((⟨coe i, hcoe i⟩): W) ) func
      := by
      exact compatible_submodule_sum W coe (fun i => hcoe i) func
    have: (Finsupp.linearCombination k fun i ↦ coe i) f
       = (Finsupp.linearCombination k fun i ↦ coe i) g := by
      rw[this f, this g, hfgsumeq]
    have: Finsupp.linearCombination k coe f = Finsupp.linearCombination k coe g
      := by exact this
    apply hlin this

lemma span_top_submodule {I: Type} (coe: I → V):
  (⊤: Submodule k (Submodule.span k (Set.range coe))) ≤ Submodule.span k (Set.range
  (fun i => ⟨coe i, Submodule.mem_span_of_mem (Set.mem_range_self i)⟩ )) := by
    rintro ⟨v, hv ⟩  _
    rw[Finsupp.mem_span_range_iff_exists_finsupp]
    rw[Finsupp.mem_span_range_iff_exists_finsupp] at hv
    have ⟨c, hc⟩ := hv
    have: (c.sum fun i a ↦ a • coe i) = Finsupp.linearCombination k coe c := rfl
    have hc: Finsupp.linearCombination k coe c =v := hc
    use c
    simp_rw[<- hc]
    rw[<- Finsupp.linearCombination_apply]
    have := compatible_submodule_sum (Submodule.span k (Set.range coe)) coe (?_) c
    simp[this]
    intro i
    suffices coe i ∈ Set.range coe from Submodule.mem_span_of_mem this
    exact Set.mem_range_self i


@[simp]
noncomputable def Hypsubspace.basis {B: BilinForm k V} (H : Hypsubspace B) : Basis H.basis_index k H.toSubmodule := by
  apply Basis.mk
  case v => exact (fun i => ⟨H.coe i, Submodule.mem_span_of_mem (Set.mem_range_self i)⟩ )
  case hli =>
    refine linear_independence_submodule H.toSubmodule H.coe ?_ ?_
    exact H.linind
  case hsp =>
    apply span_top_submodule

noncomputable def Hypsubspace_of_Hypspace_submodule {B: BilinForm k V} {W: Submodule k V}
 (H : Hypspace (B.restrict W)) : Hypsubspace B where
 I := H.I
 coe := fun i => H.basis i
 pred := by
  constructor
  . intro i j
    have:= H.pred.isotropic_left i j
    simpa using this
  . intro i j
    have:= H.pred.isotropic_right i j
    simpa using this
  . intro i j h
    have := H.pred.orthog1 i j h
    simpa using this
  . intro i j h
    have := H.pred.orthog2 i j h
    simpa using this
  . intro i
    have := H.pred.unital_corr i
    simpa using this


lemma span_range_submodule_basis_eq_submodule (W: Submodule k V) {I: Type*} (b: Basis I k W):
  Submodule.span k (Set.range (fun i ↦ (b i: V) )  ) = W := by
  convert congr(Submodule.map W.subtype $b.span_eq)
  · rw [Submodule.map_span]; congr 1; ext; simp
  · simp



def Hypsubspace_of_Hypspace_submodule_toSubmodule_agrees {B: BilinForm k V} {W: Submodule k V}
 (H : Hypspace (B.restrict W)) : (Hypsubspace_of_Hypspace_submodule H).toSubmodule = W := by
  simp[Hypsubspace_of_Hypspace_submodule]
  exact span_range_submodule_basis_eq_submodule W H.basis


theorem Hypsubspace_of_Hypspace_pred_restrict {B: BilinForm k V} {W: Submodule k V}
 (h: Hypspace_pred <| B.restrict W): ∃ (H: Hypsubspace B), H.toSubmodule = W := by
    let H' := Hypspace_of_Hypspace_pred h
    use Hypsubspace_of_Hypspace_submodule H'
    exact Hypsubspace_of_Hypspace_submodule_toSubmodule_agrees H'

@[simp]
noncomputable def Hypsubspace.toHypspace {B: BilinForm k V} (H: Hypsubspace B):
  Hypspace (B.restrict H.toSubmodule) where
  I := H.I
  basis := H.basis
  pred := by
    constructor
    repeat simp_all

theorem Hypsubspace_basis_compatible {B: BilinForm k V} (H: Hypsubspace B):
  H.toHypspace.basis = H.basis := rfl

@[simp]
abbrev sum_iso {I I': Type} (π: I ≃ I') : I ⊕ I ≃ I' ⊕ I' := π.sumCongr π

noncomputable def Hypspace.iso_from_iso_index {V': Type} {B: BilinForm k V} [AddCommGroup V']
  [Module k V'] {B': BilinForm k V'} (H: Hypspace B) (H': Hypspace B') (π: H.I ≃ H'.I)
  (h: ∀ i, B (H.basis <| Sum.inr i) (H.basis <| Sum.inl i) = B' (H'.basis <| Sum.inr <| π i) (H'.basis <| Sum.inl <| π i) ) :
  V ≃[k, B, B'] V' := by
    have (i: H.basis_index) (j: H.basis_index):  B (H.basis i) (H.basis j) = B' (H'.basis <| sum_iso π i) (H'.basis <| sum_iso π j) :=
      match i with
      | Sum.inl i => match j with
        | Sum.inl j => by simp_all
        | Sum.inr j => by
          by_cases h':(i = j)
          . simp[h']
          . simp[h']
      | Sum.inr i =>  match j with
        | Sum.inl j => by
          by_cases h':(i = j)
          . simp[h',h]
          . simp[h']
        | Sum.inr j => by simp_all
    exact Isometries.from_basis_equiv (sum_iso π) this

noncomputable def Hypsubspace.iso_from_iso_index {V': Type} {B: BilinForm k V} [AddCommGroup V']
  [Module k V'] {B': BilinForm k V'} (H: Hypsubspace B) (H': Hypsubspace B') (π: H.I ≃ H'.I)
  (h: ∀ i, B (H.basis <| Sum.inr i) (H.basis <| Sum.inl i) = B' (H'.basis <| Sum.inr <| π i) (H'.basis <| Sum.inl <| π i) ) :
  H.toSubmodule ≃[k, B.restrict _, B'.restrict _] H'.toSubmodule := by
    have (i: H.basis_index) (j: H.basis_index):  B (H.basis i) (H.basis j) = B' (H'.basis <| sum_iso π i) (H'.basis <| sum_iso π j) :=
      match i with
      | Sum.inl i => match j with
        | Sum.inl j => by simp_all
        | Sum.inr j => by
          by_cases h':(i = j)
          . simp[h']
          . simp[h']
      | Sum.inr i =>  match j with
        | Sum.inl j => by
          by_cases h':(i = j)
          . rw[h']
            simp only [toSubmodule, basis_index, basis, Basis.coe_mk] at h
            simp[h]
          . simp[h']
        | Sum.inr j => by simp_all
    exact Isometries.from_basis_equiv (sum_iso π) this

noncomputable def Hypsubspace.iso_from_iso_index_symm {V': Type} {B: BilinForm k V} [AddCommGroup V']
  [Module k V'] {B': BilinForm k V'} (H: Hypsubspace B) (H': Hypsubspace B') (π: H.I ≃ H'.I)
  (hb: IsSymm B) (hb': IsSymm B') :
  H.toSubmodule ≃[k, B.restrict _, B'.restrict _] H'.toSubmodule := by
    refine Hypsubspace.iso_from_iso_index H H' π ?_
    intro i
    rw[<- hb]
    rw[<- hb']
    simp

theorem Hypspace_rank {B: BilinForm k V} (H: Hypspace B):
  Module.rank k V=2*Cardinal.mk H.I := by
  have: 2*Cardinal.mk H.I = Cardinal.mk (H.I ⊕ H.I ) := by
    have: Cardinal.mk H.I + Cardinal.mk H.I = 2*Cardinal.mk H.I := by
      exact Eq.symm (two_mul (Cardinal.mk H.I))
    rw[<- this]
    rfl
  rw[this]
  exact Eq.symm (Basis.mk_eq_rank'' H.basis)

theorem Hypspace_finrank {B: BilinForm k V} (H: Hypspace B) [Fintype H.I] :
  Module.finrank k V=2*Fintype.card H.I := by
  have: 2*Fintype.card H.I = Fintype.card (H.I ⊕ H.I ) := by
    have: Fintype.card H.I + Fintype.card H.I = 2*Fintype.card H.I := by
      exact Eq.symm (Nat.two_mul (Fintype.card H.I))
    rw[<- this]
    exact Eq.symm Fintype.card_sum
  rw[this]
  exact Module.finrank_eq_card_basis H.basis

theorem Hypspace_finrank_Fin_n {n: ℕ} {B: BilinForm k V} (H: Hypspace B) (h: H.I=Fin n):
  Module.finrank k V=2*n := by
  have : Fintype H.I := by
    suffices Finite H.I from by exact Fintype.ofFinite H.I
    rw[h]
    exact Finite.of_fintype (Fin n)
  rw[Hypspace_finrank H]
  have: Fintype.card H.I = n := by
    rw[<- Fintype.card_fin n]
    exact Fintype.card_congr' h
  rw[this]

noncomputable instance {B: BilinForm k V}[FiniteDimensional k V] (H: Hypspace B): Fintype H.I := by
    have: Finite H.I := by
      refine @Finite.sum_left H.I H.I ?_
      have := H.basis
      refine Fintype.finite ?_
      exact FiniteDimensional.fintypeBasisIndex this
    exact Fintype.ofFinite H.I

-- Note: I would prefer to make this an instance but lean doesn't accept it
def Hypspace.FiniteDimensionalVS {B: BilinForm k V} (H: Hypspace B) [Fintype H.I] : (FiniteDimensional k V) := by
  suffices Finite (H.basis_index) from Module.Finite.of_basis H.basis
  infer_instance

instance  {B: BilinForm k V} (H: Hypsubspace B) [Fintype H.I]: Fintype H.toHypspace.I :=
  have: Fintype H.I := inferInstance
  this

instance Hypsubspace.FiniteDimensionalVS {B: BilinForm k V} (H: Hypsubspace B) [Fintype H.I] : (FiniteDimensional k H.toSubmodule) := by
  exact Hypspace.FiniteDimensionalVS H.toHypspace

noncomputable instance {B: BilinForm k V}[FiniteDimensional k V] (H: Hypsubspace B):
  Fintype H.toHypspace.I := inferInstance

theorem Hypspace.is_even_dimension {B: BilinForm k V}  [FiniteDimensional k V] (H: Hypspace B):
  Even (Module.finrank k V) := by
  rw[Hypspace_finrank H]
  exact even_two_mul (Fintype.card H.I)

theorem Hypsubspace.is_even_dimension {B: BilinForm k V}  [FiniteDimensional k V] (H: Hypsubspace B):
  Even (Module.finrank k H.toSubmodule) := Hypspace.is_even_dimension H.toHypspace

-- This should be provable without finiteness requirement, however proving
-- 2 * Cardinal.mk α = 2 * Cardinal.mk β  → Cardinal.mk α = Cardinal.mk β will involve splitting
-- into cases on α or β infinite anyway
noncomputable def iso_index_from_rank_eq {V': Type} {B: BilinForm k V} [AddCommGroup V'] [Module k V']
  {B': BilinForm k V'} (H: Hypspace B) (H': Hypspace B') (h: Module.finrank k V = Module.finrank k V')
  [FiniteDimensional k V][FiniteDimensional k V']:
  H.I ≃ H'.I := by
  apply Classical.choice
  have: 2*Fintype.card H.I=2*Fintype.card H'.I := by
    rw[<- Hypspace_finrank H,<- Hypspace_finrank H',h]
  have: Fintype.card H.I=Fintype.card H'.I := by
    omega
  exact Fintype.card_eq.mp this

noncomputable def iso_index_from_rank_eq' {V': Type} {B: BilinForm k V} [AddCommGroup V'] [Module k V']
  {B': BilinForm k V'} (H: Hypsubspace B) (H': Hypsubspace B')
  (h: Module.finrank k H.toSubmodule = Module.finrank k H'.toSubmodule)
  [FiniteDimensional k V][FiniteDimensional k V']: H.I ≃ H'.I :=
    iso_index_from_rank_eq H.toHypspace H'.toHypspace h

protected def Basis_repr_left{B: BilinForm k V} (H: Hypspace B) (i: H.I):
  V →ₗ[k] k where
  toFun := fun v ↦ (H.basis.repr v) (Sum.inl i)
  map_add' := by simp
  map_smul' := by simp

protected noncomputable def Basis_form_right {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  V →ₗ[k] k where
  toFun := fun v ↦ B v (H.basis (Sum.inr i))
  map_add' := by simp
  map_smul' := by simp

protected theorem Basis_repr_left_eq_Basis_form_right {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  Hyperbolic.Basis_repr_left H i = Hyperbolic.Basis_form_right H i := by
    apply  Basis.ext H.basis
    intro j
    match j with
    | Sum.inl j =>
      dsimp[Hyperbolic.Basis_repr_left,Hyperbolic.Basis_form_right]
      by_cases h:i = j
      . simp[h]
      . have: j ≠ i := by exact fun a ↦ h (id (Eq.symm a))
        simp_all
    | Sum.inr j =>
      dsimp[Hyperbolic.Basis_repr_left,Hyperbolic.Basis_form_right]
      by_cases h:i = j
      . simp[h]
      . simp_all

theorem Hypspace_repr_left' {B: BilinForm k V} (H: Hypspace B) (v: V) (i: H.I):
  (H.basis.repr v) (Sum.inl i) = B v (H.basis (Sum.inr i)) := by
    have hleft: (H.basis.repr v) (Sum.inl i) = Hyperbolic.Basis_repr_left H i v := by
      simp[Hyperbolic.Basis_repr_left]
    have hright: B v (H.basis (Sum.inr i)) = Hyperbolic.Basis_form_right H i v:= by
      simp[Hyperbolic.Basis_form_right]
    rw[hleft, hright]
    rw[Hyperbolic.Basis_repr_left_eq_Basis_form_right H i]

protected def Basis_repr_left2 {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  V →ₗ[k] k where
  toFun := fun v ↦ (H.basis.repr v) (Sum.inr i)
  map_add' := by simp
  map_smul' := by simp

protected noncomputable def Basis_form_right2 {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  V →ₗ[k] k where
  toFun := fun v ↦ B (H.basis (Sum.inl i)) v
  map_add' := by simp
  map_smul' := by simp

protected theorem Basis_repr_left_eq_Basis_form_right2 {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  Hyperbolic.Basis_repr_left2 H i = Hyperbolic.Basis_form_right2 H i := by
    apply  Basis.ext H.basis
    intro j
    match j with
    | Sum.inl j =>
      dsimp[Hyperbolic.Basis_repr_left2,Hyperbolic.Basis_form_right2]
      by_cases h:i = j
      . simp[h]
      . have: j ≠ i := by exact fun a ↦ h (id (Eq.symm a))
        simp_all
    | Sum.inr j =>
      dsimp[Hyperbolic.Basis_repr_left2,Hyperbolic.Basis_form_right2]
      by_cases h:i = j
      . simp[h]
      . have: j ≠ i := by exact fun a ↦ h (id (Eq.symm a))
        simp_all

theorem Hypspace_repr_right' {B: BilinForm k V} (H: Hypspace B) (v: V) (i: H.I):
  (H.basis.repr v) (Sum.inr i) = B (H.basis (Sum.inl i)) v  := by
    have hleft: (H.basis.repr v) (Sum.inr i) = Hyperbolic.Basis_repr_left2 H i v := by
      simp[Hyperbolic.Basis_repr_left2]
    have hright: B (H.basis (Sum.inl i)) v = Hyperbolic.Basis_form_right2 H i v:= by
      simp[Hyperbolic.Basis_form_right2]
    rw[hleft, hright]
    rw[Hyperbolic.Basis_repr_left_eq_Basis_form_right2 H i]

-- Probably build off Hypspace_of_orthog_direct_sum' instead
noncomputable def Hypsubspace_of_orthog_ind {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_ind B H₁.toSubmodule  H₂.toSubmodule):
  Hypsubspace B where
  I := H₁.I ⊕ H₂.I
  coe :=
    fun i =>
    match i with
    | Sum.inl (Sum.inl j) => H₁.coe (Sum.inl j)
    | Sum.inl (Sum.inr j) => H₂.coe (Sum.inl j)
    | Sum.inr (Sum.inr j) => H₂.coe (Sum.inr j)
    | Sum.inr (Sum.inl j) => H₁.coe (Sum.inr j)
  pred := by
    constructor
    . intro i j
      match i,j with
      | Sum.inl i, Sum.inl j => simp
      | Sum.inr i, Sum.inl j => simp[h.orthog]
      | Sum.inl i, Sum.inr j => simp[h.orthog]
      | Sum.inr i, Sum.inr j => simp
    . intro i j
      match i,j with
      | Sum.inl i, Sum.inl j => simp
      | Sum.inr i, Sum.inl j => simp[h.orthog]
      | Sum.inl i, Sum.inr j => simp[h.orthog]
      | Sum.inr i, Sum.inr j => simp
    . intro i j h'
      match i,j with
      | Sum.inl i, Sum.inl j => simp_all
      | Sum.inr i, Sum.inl j => simp[h.orthog]
      | Sum.inl i, Sum.inr j => simp[h.orthog]
      | Sum.inr i, Sum.inr j => simp_all
    . intro i j h'
      match i,j with
      | Sum.inl i, Sum.inl j => simp_all
      | Sum.inr i, Sum.inl j => simp[h.orthog]
      | Sum.inl i, Sum.inr j => simp[h.orthog]
      | Sum.inr i, Sum.inr j => simp_all
    . intro i
      match i with
      | Sum.inl i => simp_all
      | Sum.inr i => simp_all

@[simp]
theorem Hypsubspace_of_direct_sum_Hypsubspaces {B: BilinForm k V}
  {H₁: Hypsubspace B} {H₂: Hypsubspace B} (h: is_orthog_ind B H₁.toSubmodule
  H₂.toSubmodule): (Hypsubspace_of_orthog_ind h).toSubmodule = H₁.toSubmodule ⊔ H₂.toSubmodule := by
    have h1: (Hypsubspace_of_orthog_ind h).toSubmodule ≤ H₁.toSubmodule ⊔ H₂.toSubmodule := by
      unfold Hypsubspace.toSubmodule
      suffices (Set.range (Hypsubspace_of_orthog_ind h).coe) ≤ H₁.toSubmodule ⊔ H₂.toSubmodule from ?_
      . exact Submodule.span_le.mpr this
      rintro _ ⟨i, rfl⟩
      match i with
      | Sum.inl (Sum.inl i) =>
        have h1: (Hypsubspace_of_orthog_ind h).coe (Sum.inl (Sum.inl i)) ∈ H₁.toSubmodule := by
          exact Hypsubspace.contained' H₁ (Sum.inl i)
        have h2: H₁.toSubmodule ≤ H₁.toSubmodule ⊔ H₂.toSubmodule := le_sup_left
        exact h2 h1
      | Sum.inr (Sum.inl i) =>
        have h1: (Hypsubspace_of_orthog_ind h).coe (Sum.inr (Sum.inl i)) ∈ H₁.toSubmodule := by
          exact Hypsubspace.contained H₁ (Sum.inr i)
        have h2: H₁.toSubmodule ≤ H₁.toSubmodule ⊔ H₂.toSubmodule := le_sup_left
        exact h2 h1
      | Sum.inl (Sum.inr i) =>
        have h1: (Hypsubspace_of_orthog_ind h).coe (Sum.inl (Sum.inr i)) ∈ H₂.toSubmodule := by
          exact Hypsubspace.contained' H₂ (Sum.inl i)
        have h2: H₂.toSubmodule ≤ H₁.toSubmodule ⊔ H₂.toSubmodule := le_sup_right
        exact h2 h1
      | Sum.inr (Sum.inr i) =>
        have h1: (Hypsubspace_of_orthog_ind h).coe (Sum.inr (Sum.inr i)) ∈ H₂.toSubmodule := by
          exact Hypsubspace.contained' H₂ (Sum.inr i)
        have h2: H₂.toSubmodule ≤ H₁.toSubmodule ⊔ H₂.toSubmodule := le_sup_right
        exact h2 h1

    have h2:  H₁.toSubmodule ≤ (Hypsubspace_of_orthog_ind h).toSubmodule := by
      unfold Hypsubspace.toSubmodule
      suffices (Set.range (H₁.coe)) ⊆ Submodule.span k (Set.range (Hypsubspace_of_orthog_ind h).coe) from ?_
      . exact Submodule.span_le.mpr this
      rintro x ⟨i, rfl⟩
      match i with
      | Sum.inl i =>
        have:  H₁.coe (Sum.inl i) = (Hypsubspace_of_orthog_ind h).coe (Sum.inl (Sum.inl i)) := by
          rfl
        rw[this]
        simp
      | Sum.inr i =>
        have:  H₁.coe (Sum.inr i) = (Hypsubspace_of_orthog_ind h).coe (Sum.inr (Sum.inl i)) := by
          rfl
        rw[this]
        simp
    have h3:  H₂.toSubmodule ≤ (Hypsubspace_of_orthog_ind h).toSubmodule := by
      unfold Hypsubspace.toSubmodule
      suffices (Set.range (H₂.coe)) ⊆ Submodule.span k (Set.range (Hypsubspace_of_orthog_ind h).coe) from ?_
      . exact Submodule.span_le.mpr this
      rintro x ⟨i, rfl⟩
      match i with
      | Sum.inl i =>
        have:  H₂.coe (Sum.inl i) = (Hypsubspace_of_orthog_ind h).coe (Sum.inl (Sum.inr i)) := by
          rfl
        rw[this]
        simp
      | Sum.inr i =>
        have:  H₂.coe (Sum.inr i) = (Hypsubspace_of_orthog_ind h).coe (Sum.inr (Sum.inr i)) := by
          rfl
        rw[this]
        simp
    have h4: H₁.toSubmodule ⊔ H₂.toSubmodule ≤ (Hypsubspace_of_orthog_ind h).toSubmodule := by
      exact sup_le h2 h3
    exact le_antisymm h1 h4


noncomputable def Hypsubspace_of_orthog_ind' {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_ind_weak B H₁.toSubmodule  H₂.toSubmodule) (hr: IsRefl B):
  Hypsubspace B :=
    Hypsubspace_of_orthog_ind (is_orthog_ind_of_is_orthog_ind_weak_refl h hr)

theorem Hypsubspace_of_direct_sum_Hypsubspaces' {B: BilinForm k V}
  {H₁: Hypsubspace B} {H₂: Hypsubspace B} (h: is_orthog_ind_weak B H₁.toSubmodule
  H₂.toSubmodule) (hr: IsRefl B): (Hypsubspace_of_orthog_ind' h hr).toSubmodule = H₁.toSubmodule ⊔ H₂.toSubmodule := by
    simp only [Hypsubspace_of_orthog_ind',Hypsubspace_of_direct_sum_Hypsubspaces]

noncomputable def Hypspace_of_orthog_direct_sum' {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_direct_sum B H₁.toSubmodule  H₂.toSubmodule):
  Hypspace B where
  I := H₁.I ⊕ H₂.I
  basis :=
       ((H₁.basis.prod H₂.basis).map (H₁.toSubmodule.prodEquivOfIsCompl _
      (((direct_sum_iff_iscompl (H₁.toSubmodule) H₂.toSubmodule).mp h.ds)))).reindex
      (Equiv.sumSumSumComm H₁.I H₁.I H₂.I H₂.I)

  pred := by
    constructor
    . intro i j
      match i with
      | Sum.inl i =>
        match j with
        | Sum.inl j => simp_all
        | Sum.inr j =>
          apply h.orthog.1
          repeat simp
      | Sum.inr i =>
        match j with
        | Sum.inl j =>
          apply h.orthog.2
          repeat simp
        | Sum.inr j => simp
    . intro j i
      match i with
      | Sum.inl i =>
        match j with
        | Sum.inl j => simp_all
        | Sum.inr j =>
          apply h.orthog.2
          repeat simp
      | Sum.inr i =>
        match j with
        | Sum.inl j =>
          apply h.orthog.1
          repeat simp
        | Sum.inr j => simp
    . intro i j h'
      match i,j with
      | Sum.inl i, Sum.inl j => simp_all
      | Sum.inr i, Sum.inl j =>
        apply h.orthog.2
        repeat simp
      | Sum.inl i, Sum.inr j =>
        apply h.orthog.1
        repeat simp
      | Sum.inr i, Sum.inr j => simp_all
    . intro i j h'
      match i,j with
      | Sum.inl i, Sum.inl j => simp_all
      | Sum.inr i, Sum.inl j =>
        apply h.orthog.2
        repeat simp
      | Sum.inl i, Sum.inr j =>
        apply h.orthog.1
        repeat simp
      | Sum.inr i, Sum.inr j => simp_all
    . intro i
      match i with
      | Sum.inl i => simp
      | Sum.inr i => simp

noncomputable def Hypspace_of_orthog_direct_sum {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_direct_sum_weak B H₁.toSubmodule  H₂.toSubmodule) (hr: IsRefl B):
  Hypspace B := Hypspace_of_orthog_direct_sum' (is_orthog_direct_sum_of_is_orthog_direct_sum_weak_refl h hr)

def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1


abbrev singleton := PUnit

@[simp]
def Hypsubspace_two {B: BilinForm k V} {e f: V} (h: hyp_pair B e f): Hypsubspace B
   where
   I := singleton
   coe := Sum.elim (fun _ ↦ e) (fun _ ↦ f)
   pred := by
    have ⟨h1,h2,h3⟩ := h
    constructor
    . intro i j
      simp[*]
    . intro i j
      simp[*]
    . intro i j h
      contrapose! h
      rfl
    . intro i j h
      contrapose! h
      rfl
    . intro i
      simp[*]

instance {B: BilinForm k V} {e f: V} (h: hyp_pair B e f):
  Fintype (Hypsubspace_two h).toHypspace.I := by
    simp only [Hypsubspace_two, Hypsubspace.toSubmodule, Hypsubspace.toHypspace, Hypsubspace.basis]
    exact inferInstance

instance {B: BilinForm k V} {e f: V} (h: hyp_pair B e f):
  Fintype (Hypsubspace_two h).basis_index:= by
    simp only [Hypsubspace_two, Hypsubspace.toSubmodule, Hypsubspace.toHypspace, Hypsubspace.basis]
    exact inferInstance

theorem Hypsubspace_two_finrank_2 {B: BilinForm k V} {e f: V} (h: hyp_pair B e f):
  Module.finrank k ((Hypsubspace_two h).toSubmodule)=2 := by
  rw[Hypspace_finrank (Hypsubspace_two h).toHypspace]
  simp

-- Better name?
-- Note: This definition seems irrelevant; could be worth removing
def foo_equiv (I: Type): I ⊕ I ≃ I × (singleton ⊕ singleton) where
  toFun
  | Sum.inl i => (i,Sum.inl 0)
  | Sum.inr i => (i,Sum.inr 0)
  invFun
  | (i,Sum.inl 0) => Sum.inl i
  | (i,Sum.inr 0) => Sum.inr i
  left_inv
  | Sum.inl i => by simp
  | Sum.inr i => by simp
  right_inv
  | (i,Sum.inl 0) => by simp
  | (i,Sum.inr 0) => by simp




/- The below proves that a hyspace is a direct sum of Hypsubspace_two's, in the sense of
  `is_orthog_direct_sum`, that it is a direct sum as vector spaces and elements
   of differing subspaces are orthogonal.
  - Make use of (planned) theorem reducing to proving basis equivalence.

  This could be formulated in the sense of isomorphism of bilinear forms. This
  would rely on things in BilinearFormIsomorphisms not yet created.
-/

def Hypspace.hyp_pair {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  hyp_pair B (H.basis (Sum.inl i)) (H.basis (Sum.inr i)) := by
    constructor
    . simp_all
    constructor
    repeat simp_all

abbrev OrthogIndexedSubspaces {ι: Type} (B:BilinForm k V) (W: ι → Submodule k V) : Prop :=
  ∀ i j, (i ≠ j) → ∀ w ∈ W i, ∀ w' ∈ W j, B w w' = 0

structure is_orthog_indexed_direct_sum {ι: Type} [DecidableEq ι]  (B: BilinForm k V) (W: ι → Submodule k V) where
  ds : DirectSum.IsInternal W
  orthog : OrthogIndexedSubspaces B W

@[simp]
def Hypspace.Hypspace_two_collection {B: BilinForm k V} (H: Hypspace B):
  H.I → Submodule k V := fun i => (Hypsubspace_two <| H.hyp_pair i ).toSubmodule

lemma Hypspace.in_hyp_pair {B: BilinForm k V} (H: Hypspace B) {i: H.I} {w: V} (hiw: w ∈ H.Hypspace_two_collection i):
  ∃(a b: k), w = a • (H.basis (Sum.inl i))+ b • (H.basis (Sum.inr i)) := by
    have hiw: w ∈ (Hypsubspace_two <| H.hyp_pair i ).toSubmodule := hiw
    simp at hiw
    have ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hiw
    use b, a
    rw[add_comm]
    exact h.symm

theorem Hypspace.is_orthog_indexed_direct_sum_Hypsubspace_two (B: BilinForm k V)
(H: Hypspace B) [DecidableEq H.I]: is_orthog_indexed_direct_sum B H.Hypspace_two_collection where
  ds := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    . refine iSupIndep_def.mpr ?_
      intro i
      suffices (H.Hypspace_two_collection i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), H.Hypspace_two_collection j)=⊥ from ?_
      . exact disjoint_iff.mpr this
      suffices (H.Hypspace_two_collection i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), H.Hypspace_two_collection j) ≤ ⊥ from ?_
      . exact
        (Submodule.eq_bot_iff
              (H.Hypspace_two_collection i ⊓ ⨆ j, ⨆ (_ : j ≠ i), H.Hypspace_two_collection j)).mpr
          this
      let W := (H.Hypspace_two_collection i)
      let E := {ind: H.I ⊕ H.I| ind ≠ (Sum.inl i) ∧ ind ≠ (Sum.inr i)}
      let U := Submodule.span k (H.basis '' E)
      have hWU: W ⊓ U ≤  ⊥ := by
        let F: Set (H.I ⊕ H.I) := {Sum.inl i, Sum.inr i}
        have hW: W ≤  Submodule.span k (H.basis '' F) := by
          show Submodule.span k (Set.range (Hypsubspace_two <| H.hyp_pair i ).coe) ≤ Submodule.span k (H.basis '' F)
          suffices  Set.range (Hypsubspace_two <| H.hyp_pair i ).coe ≤ Submodule.span k (H.basis '' F) from ?_
          . exact Submodule.span_le.mpr this
          rintro _ ⟨j, rfl⟩
          match j with
          | Sum.inl j => simp[F]
          | Sum.inr j => simp[F]
        have hU: U ≤  Submodule.span k (H.basis '' E) := by
          rfl
        have interzero: Submodule.span k (H.basis '' F) ⊓  Submodule.span k (H.basis '' E) =⊥  := by
          suffices Disjoint ( Submodule.span k (H.basis '' F) ) (Submodule.span k (H.basis '' E) ) from ?_
          . exact disjoint_iff.mp this
          apply LinearIndependent.disjoint_span_image H.basis.linearIndependent
          rw[disjoint_iff]
          show F ∩ E = ∅
          suffices F ∩ E ⊆ ∅ from by exact Set.subset_eq_empty this rfl
          intro a ⟨hf, he⟩
          have: a = Sum.inl i ∨ a=Sum.inr i := by
            unfold F at hf
            exact hf
          rcases this with h'|h'
          . exfalso
            apply he.1 h'
          . exfalso
            apply he.2 h'
        rw[<- interzero]
        apply inf_le_inf hW hU
      have hCollectionU: (⨆ j, ⨆ (_ : j ≠ i), H.Hypspace_two_collection j) ≤ U := by
        suffices ∀ j, (⨆ (_ : j ≠ i), H.Hypspace_two_collection j ≤ U) from ?_
        . simp_all
        intro j
        suffices ∀ (_ : j ≠ i), H.Hypspace_two_collection j ≤ U from ?_
        . simp_all
        intro h
        intro x hx
        have ⟨a, b, hab⟩ := H.in_hyp_pair hx
        rw[hab]
        have hleft: H.basis ((Sum.inl j)) ∈ U := by
          suffices H.basis (Sum.inl j) ∈ Set.image H.basis E from ?_
          . exact Submodule.mem_span_of_mem this
          have: Sum.inl j ∈ E := by
            constructor
            . simp[h]
            . exact Sum.inl_ne_inr
          exact Set.mem_image_of_mem (⇑H.basis) this
        have hleft: a • (H.basis ((Sum.inl j))) ∈ U := by
          exact Submodule.smul_mem U a hleft
        have hright: H.basis ((Sum.inr j)) ∈ U := by
          suffices H.basis (Sum.inr j) ∈ Set.image H.basis E from ?_
          . exact Submodule.mem_span_of_mem this
          have: Sum.inr j ∈ E := by
            constructor
            . exact Sum.inr_ne_inl
            . simp[h]
          exact Set.mem_image_of_mem (⇑H.basis) this

        have hright: b • (H.basis ((Sum.inr j))) ∈ U := by
          exact Submodule.smul_mem U b hright
        exact Submodule.add_mem U hleft hright
      calc
        W ⊓ (⨆ j, ⨆ (_ : j ≠ i), H.Hypspace_two_collection j) ≤ W ⊓ U := by
          apply inf_le_inf_left
          exact hCollectionU
        _ ≤  ⊥ := by exact hWU
    . suffices ⊤ ≤ iSup H.Hypspace_two_collection from ?_
      . exact Submodule.eq_top_iff'.mpr fun x ↦ this trivial
      have: Submodule.span k (Set.range H.basis) = ⊤ := by
        exact Basis.span_eq H.basis
      rw[<- this]
      suffices (Set.range ⇑H.basis) ≤ iSup H.Hypspace_two_collection from ?_
      . exact Submodule.span_le.mpr this
      rintro _ ⟨i,rfl⟩
      match i with
      | Sum.inl i =>
        have h1: H.Hypspace_two_collection i ≤ ↑(iSup H.Hypspace_two_collection) := by
          exact le_iSup_iff.mpr fun b a ↦ a i
        have h2: H.basis (Sum.inl i) ∈ H.Hypspace_two_collection i  := by
          simp[Submodule.mem_span_of_mem]
        exact h1 h2
      | Sum.inr i =>
        have h1: H.Hypspace_two_collection i ≤ ↑(iSup H.Hypspace_two_collection) := by
          exact le_iSup_iff.mpr fun b a ↦ a i
        have h2: H.basis (Sum.inr i) ∈ H.Hypspace_two_collection i  := by
          simp[Submodule.mem_span_of_mem]
        exact h1 h2
  orthog := by
    intro i j h wi hwi wj hwj
    have ⟨ai,bi,habi⟩ := H.in_hyp_pair hwi
    have ⟨aj,bj,habj⟩ := H.in_hyp_pair hwj
    rw[habi, habj]
    simp_all

/- The theorem `Hypspace_of_orthog_direct_sum` earlier proves the direct sum
    of two Hypsubspaces is a Hypspace. The below results prove this again
    in more generality.
-/

-- TODO: Move this to a better file.
@[simp]
def hyp_basis_iso {J: Type} (I: J → Type):
  (j: J)× (I j ⊕ (I j)) ≃ ((j : J) × I j ⊕ (j : J) × I j) := by
  exact Equiv.sigmaSumDistrib I I

@[simp]
noncomputable def Hypspace_from_orthog_indexed_direct_sum_Hypsubspace {J: Type} [DecidableEq J]
(B: BilinForm k V) (W: J → Hypsubspace B)
(h: is_orthog_indexed_direct_sum B (fun j => (W j).toSubmodule)):
Hypspace B where
  I := (j: J) × (W j).I
  basis :=
    Basis.reindex (DirectSum.IsInternal.collectedBasis (h.ds) (fun j => (W j).basis)) (hyp_basis_iso (fun j ↦ (W j).I))
  pred := by
    constructor
    . intro i j
      obtain ⟨ia, indi⟩ := i
      obtain ⟨ja, indj⟩ := j
      simp[Sigma.map]
      by_cases h': ia=ja
      . show (B ((W ia).coe (Sum.inl indi))) ((W ja).coe (Sum.inl indj)) = 0
        have: ((W ja).coe (Sum.inl indj)) = (W ia).coe (Sum.inl (h' ▸ indj))  := by
          have: W ja  = W ia := by rw[h']
          congr
          simp
        rw[this]
        simp
      . have := h.orthog ia ja
        simp_all[this]
    . intro i j
      obtain ⟨ia, indi⟩ := i
      obtain ⟨ja, indj⟩ := j
      simp[Sigma.map]
      by_cases h': ia=ja
      . show (B ((W ia).coe (Sum.inr indi))) ((W ja).coe (Sum.inr indj)) = 0
        have: ((W ja).coe (Sum.inr indj)) = (W ia).coe (Sum.inr (h' ▸ indj))  := by
          congr
          . exact h'.symm
          . exact h'.symm
          . exact h'.symm
          . simp
        rw[this]
        simp
      . have := h.orthog ia ja
        simp_all[this]
    . intro i j hij
      obtain ⟨ia, indi⟩ := i
      obtain ⟨ja, indj⟩ := j
      simp[Sigma.map]
      by_cases h': ia=ja
      . show (B ((W ia).coe (Sum.inl indi))) ((W ja).coe (Sum.inr indj)) = 0
        have hij': indi ≠ (h' ▸ indj) := by
          intro hindij
          simp_all
        have: ((W ja).coe (Sum.inr indj)) = (W ia).coe (Sum.inr (h' ▸ indj))  := by
          congr
          . exact h'.symm
          . exact h'.symm
          . exact h'.symm
          . simp
        rw[this]
        simp[hij']
      . have := h.orthog ia ja
        simp_all[this]
    . intro i j hij
      obtain ⟨ia, indi⟩ := i
      obtain ⟨ja, indj⟩ := j
      simp[Sigma.map]
      by_cases h': ia=ja
      . show (B ((W ia).coe (Sum.inr indi))) ((W ja).coe (Sum.inl indj)) = 0
        have hij': indi ≠ (h' ▸ indj) := by
          intro hindij
          simp_all
        have: ((W ja).coe (Sum.inl indj)) = (W ia).coe (Sum.inl (h' ▸ indj))  := by
          congr
          . exact h'.symm
          . exact h'.symm
          . exact h'.symm
          . simp
        rw[this]
        simp[hij']
      . have := h.orthog ia ja
        simp_all[this]
    . intro i
      obtain ⟨ia, indi⟩ := i
      simp[Sigma.map]

-- Specialization of Hypspace_from_orthog_indexed_direct_sum_Hypsubspace'
@[simp]
protected noncomputable def Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
Hypspace B :=
  Hypspace_from_orthog_indexed_direct_sum_Hypsubspace B (fun (i: I) => (Hypsubspace_two (h i))) h'

-- The prior definition yields a space with index type ((_: I) × singleton)
protected theorem Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux_basis {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
(Hyperbolic.Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux h').I = ((_: I) × singleton) := rfl

-- We will use the below theorems to create a space with a nicer index type (namely I)
@[simp]
def Hypspace.index_change {J: Type} {B: BilinForm k V} (H: Hypspace B)
  (f: H.I ≃ J): Hypspace B where
  I := J
  basis := H.basis.reindex (sum_iso f)
  pred := by
    constructor
    repeat simp_all

@[simp]
def index_iso_singleton' (I: Type): (_: I) × singleton ≃ I :=
  Equiv.sigmaUnique I fun _ ↦ singleton

@[simp]
noncomputable def Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
Hypspace B := (Hyperbolic.Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux h').index_change (index_iso_singleton' I)

-- Our new definition does indeed have index type I
@[simp]
theorem Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_I {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
(Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two h').I = I := rfl


/-
  TODO: State (and prove) some theorem about recovering the hyperbolic 2 subspaces from
  Hypspace_from_orthog_direct_sum_Hypsubspace_two.

  This has to be done after the definition for Hypspace_from_orthog_direct_sum_Hypsubspace is
  created.
-/

theorem Hypspace.Nondegenerate {B:BilinForm k V}
  (H: Hypspace B) (brefl : IsRefl B) :
  Nondegenerate B := by
    intro v hv
    let b := H.basis
    have hleft: ∀ i, (b.repr v) (Sum.inl i) = 0 := by
      intro i
      rw[Hypspace_repr_left' H v i]
      exact hv _
    have hright: ∀ i, (b.repr v) (Sum.inr i) = 0 := by
      intro i
      rw[Hypspace_repr_right' H v i]
      rw[brefl]
      exact hv _
    have h: ∀ i, (b.repr v) i = 0
    |  Sum.inl i => hleft i
    |  Sum.inr i => hright i
    exact (Basis.forall_coord_eq_zero_iff b).mp h

-- TODO: Move to a better file location
theorem IsRefl_restrict {B: BilinForm k V} (brefl: IsRefl B) (W: Submodule k V):
  IsRefl (B.restrict W) := fun x y ↦ brefl (W.subtype x) (W.subtype y)

theorem Hypsubspace.NondegenerateOn {B:BilinForm k V}
  (brefl : IsRefl B) (H: Hypsubspace B) :
  NondegenerateOn B H.toSubmodule :=
    H.toHypspace.Nondegenerate (IsRefl_restrict brefl H.toSubmodule)

theorem hyp2_nondeg_refl (β:BilinForm k V)
  (brefl : IsRefl β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (Hypsubspace_two h2).toSubmodule :=
    (Hypsubspace_two h2).NondegenerateOn brefl


theorem hyp2_nondeg_symm (β:BilinForm k V)
  (bsymm : IsSymm β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (Hypsubspace_two h2).toSubmodule  := by
  have brefl: IsRefl β := IsSymm.isRefl bsymm
  exact hyp2_nondeg_refl β brefl h2

theorem hyp2_nondeg_alt (β:BilinForm k V)
  (balt : IsAlt β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (Hypsubspace_two h2).toSubmodule  := by
  have brefl: IsRefl β := IsAlt.isRefl balt
  exact hyp2_nondeg_refl β brefl h2

-- using `orthog_decomp` from BilinearForms, we get

def hyp2_decomp_refl (β:BilinForm k V) [FiniteDimensional k V] (brefl : IsRefl β) {e f : V} (h2:hyp_pair β e f)
  : orthog_direct_sum β (Hypsubspace_two h2).toSubmodule :=
  (orthog_decomp β (Hypsubspace_two h2).toSubmodule (hyp2_nondeg_refl  β brefl h2)) brefl

def hyp2_decomp_symm (β:BilinForm k V) [FiniteDimensional k V] (bsymm : IsSymm β) {e f : V} (h2:hyp_pair β e f)
  : orthog_direct_sum β (Hypsubspace_two h2).toSubmodule :=
  hyp2_decomp_refl β bsymm.isRefl h2

def hyp2_decomp_alt (β:BilinForm k V) [FiniteDimensional k V] (balt : IsAlt β) {e f : V} (h2:hyp_pair β e f)
  : orthog_direct_sum β (Hypsubspace_two h2).toSubmodule :=
  hyp2_decomp_refl β balt.isRefl h2


lemma exists_bilin_one {e: V} {B: BilinForm k V} (enz: e ≠ 0)
  (hn: Nondegenerate B): ∃f, B e f =1 := by
    have: ∃ f, B e f ≠ 0 := by
      contrapose! enz
      exact hn e enz
    have ⟨f, hf⟩ := this
    let a := B e f
    use a⁻¹ • f
    calc
      (B e) (a⁻¹ • f) = a⁻¹ * (B e f) := by simp only [map_smul, smul_eq_mul]
      _ = a⁻¹ * a := rfl
      _ = 1 := inv_mul_cancel₀ hf


theorem hyp_pair_exists_symm {e: V} (p: ℕ) {β:BilinForm k V} (bsymm : IsSymm β) (hn: Nondegenerate β) (enz : e ≠ 0)
  (eiso : β e e  = 0) [CharP k p] (hn2 : p ≠ 2):
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_bilin_one enz hn
    let c := - 2⁻¹ * β v v
    let v' := v+c • e
    use v'
    constructor
    . exact eiso
    constructor
    . unfold v' c
      have : β v e = 1 := by
        rw[<- bsymm]
        exact hv
      have: (2: k) ≠ 0 := by
        apply Ring.two_ne_zero
        rw [ ringChar.eq k p ]
        exact hn2
      field_simp[*]
      ring
    . unfold v' c
      simp_all


theorem hyp_pair_exists_alt {e: V} {β:BilinForm k V} (balt : IsAlt β) (hn: Nondegenerate β) (enz : e ≠ 0) :
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_bilin_one enz hn
    use v
    constructor; . exact balt e
    constructor
    . exact balt v
    . exact hv

end Hyperbolic
