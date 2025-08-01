import Mathlib.Tactic
import Mathlib.LinearAlgebra.Charpoly.Basic

noncomputable section 

open Module
open LinearMap
open LinearMap (BilinForm)


variable  {k V₁ V₂ :Type} [Field k] 
  [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

structure equiv_of_spaces_with_form
  (β₁:BilinForm k V₁) 
  (β₂:BilinForm k V₂)
  where
    equiv : V₁ ≃ₗ[k] V₂
    compat : ∀ (x y : V₁), β₁ x y = β₂ (equiv v₁) (equiv v₂) 

notation:100 lhs:100 "≃[" field:100 "," lhb:100 "," rhb:100 "]" rhs:100 => 
  equiv_of_spaces_with_form (k:= field) (V₁ := lhs) (V₂ := rhs) lhb rhb


def anisotropicVector {V : Type} [ AddCommGroup V ] [ Module k V ] 
  (β:BilinForm k V) (v:V) : Prop := β v v ≠ 0

def anisotropic {V : Type} [ AddCommGroup V ] [ Module k V ] 
  (β:BilinForm k V) : Prop := ∀ v, v ≠ 0 → anisotropicVector β v


theorem anisotropic_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (han : anisotropic β₁) : anisotropic β₂ := by sorry

theorem symm_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (hsymm : β₁.IsSymm) : β₂.IsSymm := by sorry

theorem alt_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (halt : β₁.IsAlt) : β₂.IsAlt := by sorry


--two more results!

def equiv_of_spaces_with_form.symm {β₁:BilinForm k V₁} {β₂:BilinForm k V₂} 
  (e:V₁ ≃[k,β₁,β₂] V₂) :
  V₂ ≃[k,β₂,β₁] V₁ where
    equiv := e.equiv.symm
    compat := by sorry

variable  {V₃ :Type}
  [AddCommGroup V₃] [Module k V₃]

def equiv_of_spaces_with_form.trans  {β₁:BilinForm k V₁} {β₂:BilinForm k V₂} 
  {β₃:BilinForm k V₃} (e₁:V₁ ≃[k,β₁,β₂] V₂) (e₂:V₂ ≃[k,β₂,β₃] V₃) :
  V₁ ≃[k,β₁,β₃] V₃ where
    equiv := e₁.equiv.trans  e₂.equiv
    compat := by sorry
    
example : BilinForm k V₁ →ₗ[k] BilinForm k V₁ := lflip

example : Module.End k (BilinForm k V₁) := LinearMap.lflip^2 

theorem tsq : lflip^2 = (id:BilinForm k V₁ →ₗ[k] BilinForm k V₁) := by 
  ext β x y
  rw [ pow_two ]
  rw [ Module.End.mul_eq_comp ]
  rw [ comp_apply ]
  rw [ lflip_apply, lflip_apply ]
  simp
  

variable [ Module.Finite k V₁] in
example : Module.Finite k (BilinForm k V₁) := inferInstance

example  [Module.Finite k V₁] (h:V₂ = BilinForm k V₁) (T:V₂ →ₗ[k] V₂) : Polynomial k := charpoly T

example : Module.End k (BilinForm k V₁) := lflip

set_option pp.all true
def foo : Algebra k (Module.End k (BilinForm k V₁)) := by 
  exact inferInstance
  
#print foo 

set_option maxSynthPendingDepth 2 in
#synth Ring (Module.End k (BilinForm k V₁))


noncomputable
example : Polynomial k := minpoly k 
  (B := Module.End k (BilinForm k V₁))
  lflip


noncomputable example : Polynomial k := minpoly k (B := Module.End k (BilinForm k V₁)) lflip


theorem cp [Module.Finite k V₁] : minpoly k
  (lflip : Module.End k (BilinForm k V₁))
  = (X^2 - 1 : Polynomial k) := by 
  sorry
  
#check flip 



