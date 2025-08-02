import Mathlib.Tactic

noncomputable section

variable { k V : Type } [Field k] [AddCommGroup V] [Module k V]

def dir_sum_equiv (W₁ W₂ : Submodule k V) (hspan : W₁ ⊔ W₂ = ⊤) (hint : W₁ ⊓ W₂ = ⊥) :
  (W₁ × W₂) ≃ₗ[k] V :=  by 
  apply Submodule.prodEquivOfIsCompl 
  · rw [ isCompl_iff ]
    constructor
    · apply disjoint_iff.mpr hint
    · apply codisjoint_iff.mpr hspan
  

