--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.Forms.Bilinear
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-
  The purpose of this file is to define an isomorphism of bilinear formed spaces

  Notable Definitions
  - Isometries

  Major Results (Completed):
  - Proof (construction) that two spaces (V,B) (V',B') over k are isomorphic from
    a bijection of bases(really type equivalence) that commutes with the bilinear form
    `from_basis_equiv`
-/

open LinearMap (BilinForm)
open LinearMap.BilinForm


/-- Equivalence of bilinear form spaces-/
@[ext]
structure Isometries {k V V': Type*} [Field k] [AddCommGroup V] [AddCommGroup V']
[Module k V] [Module k V'] (B:BilinForm k V) (B':BilinForm k V')
  where
    equiv : V ≃ₗ[k] V'      -- the linear equivalence
    compat : ∀ x y, B' (equiv x) (equiv y) = B x y -- the compatibility assertion

-- Notation so that `V₁ ≃[k,B₁,B₂] V₂` denotes `Isometries B₁ B₂`
@[inherit_doc]
scoped[Isometries] notation:26 lhs:26 "≃[" field:26 "," lhb:26 ","
  rhb:26 "]" rhs:26 =>
  Isometries (k:= field) (V := lhs) (V' := rhs) lhb rhb

namespace Isometries

variable {k V V' V'' V''': Type*} [Field k] [AddCommGroup V] [AddCommGroup V']
  [AddCommGroup V''] [AddCommGroup V''']
  [Module k V] [Module k V'] [Module k V''] [Module k V''']

variable  {B:BilinForm k V} {B':BilinForm k V'}  {B'':BilinForm k V''} {B''':BilinForm k V'''}

@[simp]
theorem apply (π: V ≃[k, B, B'] V') (x y: V): B' (π.equiv x) (π.equiv y) = B x y :=
  π.compat x y

theorem apply' {B:BilinForm k V} {B':BilinForm k V'} (π: V ≃[k, B, B'] V') (x y: V'):
  B' x y = B (π.equiv.symm x) (π.equiv.symm y) := by
  nth_rewrite 1[<- LinearEquiv.apply_symm_apply π.equiv x, <- LinearEquiv.apply_symm_apply π.equiv y]
  exact apply π _ _

variable (B) in
def refl: V ≃[k, B, B] V where
  equiv := LinearEquiv.refl k V
  compat := fun _ _ => rfl

variable (B) in
theorem refl_equiv: (refl B).equiv = LinearEquiv.refl k V := rfl

def symm (π: V ≃[k, B, B'] V'): V' ≃[k, B', B] V where
  equiv := π.equiv.symm
  compat := fun _ _ => (π.apply' _ _ ).symm

theorem symm_equiv (π: V ≃[k, B, B'] V'): π.equiv.symm = π.symm.equiv := rfl

def trans (π: V ≃[k, B, B'] V') (π': V' ≃[k, B', B''] V''): V ≃[k, B, B''] V'' where
  equiv := π.equiv.trans π'.equiv
  compat := by simp

theorem trans_equiv (π: V ≃[k, B, B'] V') (π': V' ≃[k, B', B''] V''):
  (π.trans π').equiv = π.equiv.trans π'.equiv := rfl

def from_congr (B:BilinForm k V) (π: V ≃ₗ[k] V'): V ≃[k, B, B.congr π] V' where
  equiv := π
  compat := fun _ _ => by simp

theorem congr_equals {B:BilinForm k V} {B':BilinForm k V'} (π: V ≃[k, B, B'] V'):
  B' = B.congr π.equiv := by
  ext x y
  rw [congr_apply]
  exact apply' _ _ _


instance (B: BilinForm k V) (B': BilinForm k V'): EquivLike (Isometries B B') V V' where
  coe := fun a => a.equiv.toFun
  inv := fun a => a.equiv.invFun
  left_inv := fun a => a.equiv.left_inv
  right_inv := fun a => a.equiv.right_inv
  coe_injective' := fun f g h1 h2 => by ext; simp_all


def from_basis_equiv {I I': Type*} {b: Basis I k V}
  {b': Basis I' k V'} {B: BilinForm k V} {B': BilinForm k V'} (hI: I ≃ I')
  (hB: ∀i j, B (b i) (b j) = B' (b' (hI i)) (b' (hI j)) ) : V ≃[k,B, B'] V' where
  equiv := b.equiv b' hI
  compat := by
    let C: BilinForm k V := by
      apply LinearMap.mk₂' k k (fun v w => (B' ((b.equiv b' hI) v)) ((b.equiv b' hI) w))
      repeat simp_all
    have (v w: V):(B' ((b.equiv b' hI) v)) ((b.equiv b' hI) w)= C v w := by
      rfl
    simp_rw[this]
    suffices B = C from ?_
    . exact fun _ _ => by rw[this]
    apply LinearMap.BilinForm.ext_basis b
    intro i j
    unfold C
    simp only [hB, LinearMap.mk₂'_apply, Basis.equiv_apply]


-- Better name?
theorem from_basis_equiv_align {I I': Type*} {b: Basis I k V}
  {b': Basis I' k V'} {B: BilinForm k V} {B': BilinForm k V'} (hI: I ≃ I')
  (hB: ∀i j, B (b i) (b j) = B' (b' (hI i)) (b' (hI j)) ) :
  ∀i, (from_basis_equiv hI hB) (b i) = b' (hI i) := by
    intro i
    show (b.equiv b' hI) (b i) = b' (hI i)
    simp

/-- A bilinear form on `V × V'` defined by `B.prod B' (v1, v1') (v2, v2') = B v1 v2 + B' v1' v2'`-/
def _root_.LinearMap.BilinForm.prod (B: BilinForm k V) (B': BilinForm k V'):
  BilinForm k (V × V') :=
    B.comp (LinearMap.fst k V V') (LinearMap.fst k V V')
    + B'.comp (LinearMap.snd k V V') (LinearMap.snd k V V')

@[simp]
theorem _root_.LinearMap.BilinForm.prod_apply (B: BilinForm k V) (B': BilinForm k V') (v1 v2: V) (v1' v2': V'):
  B.prod B' (v1, v1') (v2, v2') = B v1 v2 + B' v1' v2' := by simp[LinearMap.BilinForm.prod]

theorem _root_.LinearMap.BilinForm.prod_apply' (B: BilinForm k V) (B': BilinForm k V') (v w: V × V'):
  B.prod B' v w = B v.1 w.1 + B' v.2 w.2 := by simp[LinearMap.BilinForm.prod]

abbrev _root_.LinearMap.BilinForm.prod_subspaces (B: BilinForm k V) (W₁ W₂: Submodule k V): BilinForm k (W₁ × W₂)
  := (B.restrict W₁).prod (B.restrict W₂)

@[simp]
theorem _root_.LinearMap.BilinForm.prod_subspaces_apply (B: BilinForm k V)
  {W₁ W₂: Submodule k V} (v1 w1: W₁) (v2 w2: W₂): B.prod_subspaces W₁ W₂ (v1, v2) (w1, w2) =
    B v1 w1 + B v2 w2 := by simp

-- B.congr (W₁.prodEquivOfIsCompl W₂ ((BilinearForms.direct_sum_iff_iscompl W₁ W₂).mp h)).symm
-- B.comp (R := k) (LinearMap.coprod W₁.subtype W₂.subtype) (LinearMap.coprod W₁.subtype W₂.subtype)

-- naming?
noncomputable def from_is_orthog_direct_sum (W₁ W₂: Submodule k V)
  {B: BilinForm k V} (h: BilinearForms.is_orthog_direct_sum B W₁ W₂):
    (W₁ × W₂) ≃[k, B.prod_subspaces W₁ W₂, B] V where
    equiv :=
      W₁.prodEquivOfIsCompl W₂ ((BilinearForms.direct_sum_iff_iscompl W₁ W₂).mp h.ds)
    compat := by
      rintro ⟨x1, x2⟩ ⟨y1, y2⟩
      have h1: (B ↑x1) ↑y2 = 0 :=
        h.orthog.left x1 (Submodule.coe_mem x1)  y2 (Submodule.coe_mem y2)
      have h2: (B ↑x2) ↑y1= 0 :=
        h.orthog.right x2 (Submodule.coe_mem x2)  y1 (Submodule.coe_mem y1)
      simp[Submodule.coe_prodEquivOfIsCompl', h1, h2]


def prod (π: V ≃[k, B, B'] V') (π': V'' ≃[k, B'', B'''] V'''):
  V × V'' ≃[k, B.prod B'', B'.prod B'''] V' × V''' where
    equiv := LinearEquiv.prodCongr π.equiv π'.equiv
    compat := by simp

-- We should be able to prove it with a quadratically closed predicate (if it exists)
noncomputable def from_trivial (hv: ∀ (v: V), v=0) (hv': ∀ (v: V'), v=0):
  V ≃[k, B, B'] V' where
  equiv := sorry
  compat := sorry

-- We should be able to prove it with a quadratically closed predicate (if it exists)
noncomputable def from_zero_dim [FiniteDimensional k V] [FiniteDimensional k V']
  (hd: Module.finrank k V = 0) (hd': Module.finrank k V' = 0):
  V ≃[k, B, B'] V' := by
  rw[finrank_zero_iff_forall_zero] at hd hd'
  exact from_trivial hd hd'

-- We should be able to prove it with a quadratically closed predicate (if it exists)
noncomputable def from_one_dim (hd: Module.finrank k V = 1) (hd': Module.finrank k V' = 1)
 [IsAlgClosed k] (h: ∀ v, B v v = 0 → v=0) (h': ∀ v, B' v v = 0 → v=0):
  V ≃[k, B, B'] V' := sorry


end Isometries
