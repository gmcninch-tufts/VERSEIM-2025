--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import VERSEIM2025.Forms.Bilinear

#check BilinearForms.alt_is_reflexive
/-
  Proofs that any reflexive form is alternating or symmetric
-/

open LinearMap.BilinForm
open LinearMap (BilinForm)

variable {R M: Type*} [AddCommGroup M][CommRing R] [Module R M]
variable {F V: Type*} [Field F] [AddCommGroup V] [Module F V]

theorem symmetry_extend {B: BilinForm F V} {v: V} (hr: IsRefl B)
   (h: ∀ x y, B x v = 0 → B y v = 0 → B x y = B y x) (hv: B v v ≠ 0): IsSymm B := by
  have: ∀ w, ∃ (c: F), ∃ u, B u v = 0 ∧ w = c • v + u := by
    intro w
    have: w ∈ Submodule.span F {v} ⊔ B.orthogonal (Submodule.span F {v}) := by
      rw[LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top hv]
      exact trivial
    rw[Submodule.mem_sup] at this
    obtain ⟨y, hy, z, hz, hyz⟩ := this
    rw[Submodule.mem_span_singleton] at hy
    obtain ⟨c, hc⟩ := hy
    use c, z
    constructor
    . aesop
    rw[<- hyz, hc]
  intro x y; simp only [RingHom.id_apply]
  obtain ⟨cx, ux, huxv, hx⟩ := this x
  obtain ⟨cy, uy, huyv, hy⟩ := this y
  have huxy: B ux uy = B uy ux := h ux uy huxv huyv
  rw[hx, hy]
  repeat rw[add_left]
  repeat rw[add_right]
  repeat rw[smul_left]
  repeat rw[smul_right]
  rw[huyv, huxv, huxy, hr _ _ huyv, hr _ _ huxv]
  ring

example {B: BilinForm F V} (h: IsRefl B):
  IsAlt B ∨ IsSymm B := by
  by_cases ha:IsAlt B
  . left; exact ha
  have: ∃ v, B v v ≠ 0 := by
    unfold IsAlt LinearMap.IsAlt at ha
    push_neg at ha
    exact ha
  obtain ⟨v, hv⟩ := this
  by_cases hv': ∀ x y, B x v = 0 → B y v = 0 → B x y = B y x
  . right; exact  symmetry_extend h hv' hv
  have: ∃ x y, B x v = 0 ∧ B y v = 0 ∧ B x y ≠ B y x := by
    push_neg at hv'
    exact hv'
  have: ∃ x y, B x v = 0 ∧ B y v = 0 ∧ B x y ≠ B y x ∧ B x y = -B v v := by
    obtain ⟨x,y, hxv, hyv, hxy⟩ := this
    let d: F := -(B v v)* (B x y)⁻¹
    use d • x, y
    have hxy_neqzero: B x y ≠ 0 := by
      intro hxy_zero
      have: B x y = B y x := by
        rw[h _ _ hxy_zero, hxy_zero]
      exact hxy this
    constructor
    . rw [smul_left]
      simp[hxv]
    constructor
    . exact hyv
    constructor
    . intro hxyc
      apply hxy
      rw [smul_left, smul_right] at hxyc
      have: d ≠ 0 := by
        unfold d
        field_simp[hv]
      simp_all
    . rw [smul_left]
      aesop

  obtain ⟨x, y, hxv ,hyv, hxy, hxyc⟩ := this
  have h1: B (y+v) (x+v) = 0 := by
    apply h
    rw [@add_right, add_left, add_left, hxv, h _ _ hyv, hxyc]
    ring_nf
  have h2: B (y+v) (x+v) = B y x - B x y := by
    rw [@add_right, add_left, add_left, h _ _ hxv, hyv, hxyc]
    ring
  have h3: B x y = B y x := by
    have: B y x - B x y = 0 := by
      rw[<- h1,h2]
    exact (sub_eq_zero.mp this).symm
  tauto

lemma proptwopointsix {B: BilinForm F V}
(h : ∀ (u v w : V), (((B u) v) * ((B w) u)) = (((B v) u) * ((B u) w))): B.IsAlt ∨ B.IsSymm := by
  have h₁ (v w: V): ((B v) v) * (((B w) v) - ((B v) w)) = 0 := by
    rw[mul_sub_left_distrib]
    refine sub_eq_zero_of_eq ?_
    rw[h]
  have id₁ (v w : V) : (B v v)*(B w v) = (B v v)*(B v w)  :=  h v v w
  by_contra j
  simp at j
  unfold BilinForm.IsAlt LinearMap.IsAlt BilinForm.IsSymm LinearMap.IsSymm at j
  simp at j
  rcases j with ⟨⟨e, lj⟩, ⟨f, g, rj⟩⟩
  have h₂ : (B g) g = 0 := by
    have i₂ : B g g * (B f g - B g f) = 0 := by
      exact h₁ g f
    rw[mul_sub_left_distrib] at i₂
    apply eq_of_sub_eq_zero at i₂
    rw[mul_eq_mul_left_iff] at i₂
    aesop
  have h₃ : (B f) f = 0 := by
    have i₃ : B f f * (B g f - B f g) = 0 := by
      exact h₁ f g
    rw[mul_sub_left_distrib] at i₃
    apply eq_of_sub_eq_zero at i₃
    rw[mul_eq_mul_left_iff] at i₃
    aesop
  have h₄ : (B f) e = (B e) f := by
    have i₄ : B e e * (B f e - B e f) = 0 := by
      exact h₁ e f
    rw[mul_sub_left_distrib] at i₄
    apply eq_of_sub_eq_zero at i₄
    rw[mul_eq_mul_left_iff] at i₄
    aesop
  have h₅ : (B g) e = (B e) g := by
    have i₅ : B e e * (B g e - B e g) = 0 := by
      exact h₁ e g
    rw[mul_sub_left_distrib] at i₅
    apply eq_of_sub_eq_zero at i₅
    rw[mul_eq_mul_left_iff] at i₅
    aesop
  have h₆ : (B e) f = 0 := by
    have i₆ : ((B f) e) * ((B g) f) = ((B e) f) * ((B f) g) := by
      exact h f e g
    rw[← h₄] at i₆
    rw[mul_eq_mul_left_iff] at i₆
    aesop
  have h₇ : (B e) g = 0 := by
    have i₇ : ((B g) e) * ((B f) g) = ((B e) g) * ((B g) f) := by
      exact h g e f
    rw[← h₅] at i₇
    rw[mul_eq_mul_left_iff] at i₇
    aesop
  have h₈ : (B f) (e + g) = (B f) g := by
    aesop
  have h₉ : (B (e + g)) f = (B g) f := by
    aesop
  have h₁₀ : (B (e + g)) (e + g) = 0 := by
    have i₁₀ : (B (e + g)) (e + g) * ((B f (e + g)) - (B (e + g) f)) = 0 := by
      exact h₁ (e + g) f
    rw[h₈, h₉, mul_sub_left_distrib] at i₁₀
    apply eq_of_sub_eq_zero at i₁₀
    rw[mul_eq_mul_left_iff] at i₁₀
    aesop
  have h₁₁ : (B (e + g)) (e + g) = (B e) e := by
    simp
    rw[h₇]
    rw[← h₅] at h₇
    rw[h₇, h₂]
    simp
  rw[h₁₀] at h₁₁
  exact lj (_root_.id (Eq.symm h₁₁))


theorem refl_is_alt_or_symm {B: BilinForm F V} (h: B.IsRefl):
    B.IsAlt  ∨ B.IsSymm := by
    let x (u v w : V) := ((B u) v) • w - (((B u) w) •  v)
    have h₀ (u v w : V):  (B u) (x u v w) = (((B u) v) * ((B u) w)) - (((B u) w) * ((B u) v)) := by
      aesop
    have h₁ (u v w : V) : (((B u) v) * ((B u) w)) - (((B u) w) * ((B u) v)) = 0 := by
      rw[mul_comm]
      simp
    simp_rw[h₁] at h₀
    have h₂ (u v w: V) :(B (x u v w)) u =  0:= by
      exact h u (x u v w) (h (x u v w) u (h u (x u v w) (h₀ u v w)))
    have h₃ (u v w : V): B (x u v w) u = B u v * B w u - (B v u) * (B u w) := by
      have h₃₀ (u v w: V): (B (x u v w)) u = (B (((B u v) • w) - (B u w) • v)) u := by
        aesop
      simp at h₃₀
      simp_rw[h₃₀]
      rw[mul_comm (B u w)  (B v u)]
    have h₄ : ∀ (u v w : V), (((B u) v) * ((B w) u)) = (((B v) u) * ((B u) w)) := by
      intro u v w
      have h₄₀ : (B u) v * (B w) u = (B v) u * (B u) w ↔ (((B u) v) * ((B w) u)) - (((B v) u) * ((B u) w)) = 0 := by
        constructor
        · aesop
        · intro g
          apply eq_of_sub_eq_zero at g
          exact g
      rw[h₄₀]
      apply eq_of_sub_eq_zero
      simp
      simp_rw[h₂] at h₃
      exact (AddSemiconjBy.eq_zero_iff 0 (congrFun (congrArg HAdd.hAdd (h₃ u v w)) 0)).mp rfl
    apply proptwopointsix (F := F) (V := V)
    · exact h₄

theorem refl_iff_alt_or_symm {β : BilinForm F V} : β.IsRefl ↔ (β.IsAlt ∨ β.IsSymm) := by
  constructor
  · intro h
    exact refl_is_alt_or_symm h
  · intro h
    cases h with
    | inl h₁ => exact IsAlt.isRefl h₁
    | inr h₂ => exact IsSymm.isRefl h₂
