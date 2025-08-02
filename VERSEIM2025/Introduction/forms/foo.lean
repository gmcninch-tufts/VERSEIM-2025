import Mathlib.Tactic

import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank


variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

variable {ι:Type} [Fintype ι] [DecidableEq ι]

variable {b:Basis ι k V}

open LinearMap 
open LinearMap (BilinForm)

example (β:BilinForm k V) : Matrix.transpose (BilinForm.toMatrix b β) = 
        (LinearMap.toMatrix b (Basis.dualBasis b) β ) := by 
  ext
  rw [ LinearMap.toMatrix_apply ] 
  simp

example (β:BilinForm k V) : Module.rank k (range β) = 
        Matrix.rank (BilinForm.toMatrix b β) := by
 unfold Matrix.rank
 unfold BilinForm.toMatrix
 unfold Matrix.mulVecLin
 simp

-- example (β:BilinForm k V) : Nondegenerate β → ker β = ⊥ := by --
--   contrapose
--   intro h 
--   unfold Nondegenerate 
--   unfold SeparatingLeft 
--   unfold SeparatingRight 
--   unfold ker 
  

-- 
example (β:BilinForm k V) (y:V) : ∀ (x : V), (β x) y = 0 → y ∈ ker (β x) := by
  simp


example (β:BilinForm k V) : (∀ y ,( ∀ x , (β x) y = 0) →y = 0) → (ker β = ⊥) := by 
  contrapose
  intro h
  by_contra
  
   


