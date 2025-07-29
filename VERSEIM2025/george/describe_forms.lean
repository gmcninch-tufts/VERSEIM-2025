import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Properties

noncomputable section

open Module
  
  
variable {k : Type} [ Field k ]
variable {V : Type} [ AddCommGroup V ] [ Module k V ]

variable {ι:Type} [Fintype ι]

variable {b:Basis ι k V}

open Module
open LinearMap
open LinearMap (BilinForm)




abbrev OrthogSubsets (β:BilinForm k V) (S₁ S₂ : Set V) : Prop :=
  ∀ x ∈ S₁, ∀ y ∈ S₂, β x y = 0

lemma subset_orthogonal (β:BilinForm k V) (S T₁ T₂: Set V) (hsub: T₁ ⊆ T₂) :
  OrthogSubsets β S T₂ → OrthogSubsets β S T₁ := by 
  intro h
  intro x hx y hy
  apply h
  apply hx
  apply hsub
  apply hy
  
#check Basis 

def OrthogBasis (β:BilinForm k V) {ι:Type} [Fintype ι] (b:Basis ι k V) : Prop :=
  ∀ i j, β (b i) (b j) = 0
  
/-- If β is non-degenerate, we can find vectors `v w:V` for which
`β v w ≠ 0` -/
lemma nondeg_pair (β:BilinForm k V) [Nontrivial V] (hnd : β.Nondegenerate ) 
  : ∃ v w : V, β v w ≠ 0 := by 
  have : ∃ v:V, v ≠ 0 := by exact exists_ne 0
  rcases this with ⟨v,hv⟩
  have h₁ : ker β = ⊥ := BilinForm.Nondegenerate.ker_eq_bot hnd
  have : β v ≠ 0 := by
    by_contra vker
    have : v ∈ ker β := vker
    rw [h₁] at this 
    exact hv this
  use v
  by_contra l₁
  rw [ not_exists ] at l₁
  simp at l₁
  apply this
  ext x
  simp
  exact l₁ x

-- lemma anisotropic_vector (β:BilinForm k V) [Nontrivial V] (hnd : β.Nondegenerate ) 
--   (hsymm: β.IsSymm) 
--   : ∃ v, anisotropic β v := by
--   rcases nondeg_pair β hnd with ⟨ v,w,hvw ⟩
--   by_cases h₁ : β v v = 0 
--   case neg => exact ⟨v,h₁⟩
--   case pos => 
--     by_cases h₂ : β w w = 0
--     case neg => exact ⟨w,h₂⟩
--     case pos => 
--       #check BilinForm.isSymm_def.mp hsymm v w
--       have : β (v+w) (v+w) = 2*(β v w) := by calc
--         β (v+w) (v+w) = β v (v+w) + β w (v+w) := by simp
--                    _ = β v v + β v w + β w v + β w w := by simp_all only [ne_eq, map_add, zero_add, add_zero]
--                    _ = β v w + β w v := by rw [ h₁, h₂ ] ; simp
--                    _ = 2*β v w := by 
--                                   rw [ BilinForm.isSymm_def.mp hsymm v w ] 
--                                   ring
--       use v+w
--       unfold anisotropic
--       rw [ this ]
                   


  
--theorem orthog_basis_exists (β:BilinForm k V) (W:Subspace V) 

structure OrthogSet (β:BilinForm k V) where
  carrier : Set V
  orthog : ∀ x ∈ carrier, ∀ y ∈ carrier, x ≠ y → β x y = 0
  
theorem orthog_set_is_lin_indep (β:BilinForm k V) 
  (S:OrthogSet β) : 
  LinearIndepOn k id S.carrier := by 
    rw [linearIndepOn_iff]
    intro l lsupp hlc
    ext x
    by_cases hl : x ∈ l.support
    case neg => simp_all only [ Finsupp.mem_support_iff
                              , ne_eq
                              , not_not
                              , Finsupp.coe_zero
                              , Pi.zero_apply]
    case pos => 
      sorry  
  
def diag_matrix (ι:Type) [Fintype ι] [DecidableEq ι] (f : ι → k) : Matrix ι ι k := fun i j =>
  by if h : i=j then exact f i else exact 0

    

