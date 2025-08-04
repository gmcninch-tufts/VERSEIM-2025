--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

variable { k V : Type } [Field k] [AddCommGroup V] [Module k V]

-- possible new notation: `LinearMap.BilinForm k V` is the same thing
-- as `V →ₗ[k] V →ₗ[k] k`

-- indeed

example : (LinearMap.BilinForm k V) = (V →ₗ[k] V →ₗ[k] k) := rfl

-- (Having typed `V →ₗ[k] V →ₗ[k] k` several times, I now agree that
-- `BilinForm k V` is probably better notation...)

-- A matrix is a bit like a vector, with two index sets (one for
-- "rows" and one for "columns").

-- An n × m matrix has the following type

variable (n m:ℕ) 
#check Matrix (Fin n) (Fin m) k 


-- but more generally you could have a matrix whose rows and columns
-- are indexed by just any type (in our case, we'll typically insist
-- that those indexing types be finite!)

variable (rows cols : Type) [Fintype rows] [Fintype cols] 
#check Matrix rows cols k

-- the type of matrices has a vector space structure

example (n m:ℕ) : Module k (Matrix (Fin n) (Fin m) k) := inferInstance

example (rows cols : Type) : Module k (Matrix rows cols k) := inferInstance

-- if you want to construct explicit matrices, you can do so using
-- notation `!![ ... ]` with commas separating entries and semicolons
-- separating rows

#check !![ 1, 1; 0, (1:ℚ)]

-- and we can see the vector space struture in action:

#eval !![ 1, 1; 0, (1:ℚ)] + (2:ℚ)•!![1,2;0,-1]

-- You can even multiply matrices (of the right sizes)

#eval !![ 1, 1; 0, (1:ℚ)] * !![ 1, 1; 0, (1:ℚ)]

-- (need for matrix multiplication is the reason for not representing
-- matrices simply as `Fin n → Fin m → k`).

-- given a matrix , you can get the ith row by evaluation, and the i j coefficient by evaluation:

#eval !![1,2,3;4,5,6] 1 

#eval !![1,2,3;4,5,6] 1 1

-- and finally you can take determinants:

example (a b:ℚ) : !![a , 1 ; 0 , b ].det = a*b := by simp


-- on the black board, we have described how to get a matrix from a bilinear form β:
-- take a basis v₁, ... , vₙ of V and form the matrix whose i,j entrie is
-- `beta vᵢ vⱼ`

-- in fact, mathlib has implemented this construction via `BilinForm.toMatrix`


variable (β:LinearMap.BilinForm k V)
variable (b : Basis (Fin n) k V)

#check BilinForm.toMatrix b β

noncomputable example : Matrix (Fin n) (Fin n) k := BilinForm.toMatrix b β

-- more precisely, in thenotation of the previous example,
-- `BilinForm.toMatrix b` is a linear equivalence:

#check LinearMap.BilinForm k V ≃ₗ[k] Matrix (Fin n) (Fin n) k

-- the mathlib theorem `BilinForm.toMatrix_apply` confirms that the
-- entries of the matrix correspond to the values of the bilinear form
-- at the corresponding basis vectors:

example (i j : Fin n) : (BilinForm.toMatrix b) β i j  = β (b i) (b j) := 
  BilinForm.toMatrix_apply b β i j

-- there is no need to only work with bases and rows/cols indexed by `Fin`s
-- (Note that the index type needs to have a `DecidableEq` instance!)

variable (ι : Type) [Fintype ι] [DecidableEq ι]

variable (c : Basis ι k V)

-- using our basis `c` we'll construct an `ι` × `ι` matrix corresponding to `β`.

#check BilinForm.toMatrix c β

noncomputable example : Matrix ι ι k := BilinForm.toMatrix c β

-- we still know that the entries of the toMatrix are as indicated:

example (i j : ι) : (BilinForm.toMatrix c) β i j  = β (c i) (c j) := 
  BilinForm.toMatrix_apply c β i j

--------------------------------------------------------------------------------
-- ** Non-degenerate bilinear forms
--------------------------------------------------------------------------------

-- recall that we've define a bilinear form to be non-degenerate
-- provide that the corresponding matrix has non-zero
-- determinant. Let's formylate that as a predicate in Lean:

-- (I'm going to include this definition and subsequent statements in
-- the file `Bilinear.lean`)

open LinearMap 
open LinearMap (BilinForm)

variable { k V : Type } [Field k] [AddCommGroup V] [Module k V]

variable { ι : Type } [Fintype ι] [DecidableEq ι]

variable { b : Basis ι k V }

def Nondeg (β : BilinForm k V) : Prop := 
  ∀ v:V, ∀ w:V, β v w = 0 → v = 0


-- We want to talk about the restriction of our bilinear form β to any
-- subspace W of V.  To warm up, let's first see how we can restrict a
-- linear map to a subspace:

-- for this we use `LinearMap.restrict` 

-- simplifying the signature for purposes of explanation, this reads

-- -- def LinearMap.restrict  (f : V →ₗ[k] V) {W  : Submodule k V} {U : Submodule R V} 
-- --   (hf : ∀ x ∈ W, f x ∈ U) :
-- --   ↥W →ₗ[k] ↥U

-- If we take `U` to be `⊤` so that `↥U` is `V` in this case, then the
-- required argument `hf` is vacuous.

-- we can apply this as follows

example (W:Subspace k V) (f:V →ₗ[k] V) : ↥W →ₗ[k] ↑(⊤:Submodule k V) := 
  LinearMap.restrict f (fun _ _ => trivial)

example (W:Subspace k V) (f:V →ₗ[k] V)  : ↥W →ₗ[k] ↥(⊤:Submodule k V) := 
  LinearMap.restrict f (fun _ _ => by trivial )

-- somewhat annoyingly, it seems that just writing `V` instead of
-- `↥(⊤:Submodule k V)` doesn't unify correctly... 


-- There is a similar restriction operation for `BilinForm`s, namely
-- `BilinForm.restrict`.  This operation doesn't perform any restrict
-- in the codomain, so it doesn't take a proof argument.

example (W:Subspace k V) (β:BilinForm k V) : BilinForm k ↥W := BilinForm.restrict β W

-- now we can extend our non-degeneracy requirement to a predicate *on
-- subspaces* of V.

def NondegOn
  (β : BilinForm k V) (W : Subspace k V) : Prop := 
  Nondeg (BilinForm.restrict β W)



theorem nondeg_conditions  (β : BilinForm k V) 
  : List.TFAE [ Nondeg β                                                 -- left-nondegenate
               , ∀ w:V, ∀ v:V, β v w = 0 → w = 0                          -- right-nondegenerate
               , ∃ (b:Basis ι k V), (BilinForm.toMatrix b β).det ≠ 0
               ] := by sorry

-- note you can prove TFAE results using the `tfae_have` and `tfae_finish` tactics
-- and it us pretty easy to *use* a TFAE results:

example {p q r s : Prop} {l:List Prop} (ll : l = [ p, q, r, s])  (h:List.TFAE l) :  
  p ↔ r :=  by
    have pl : p ∈ l := by rw [ll]; simp
    have rl : r ∈ l := by rw [ll]; simp
    exact h p pl r rl


--------------------------------------------------------------------------------
-- direct sums and orthogonal complements
-- ======================================

def is_internal_direct_sum (W₁ W₂ : Submodule k V) : Prop :=
  ⊤ = W₁ ⊔ W₂ ∧ ⊥ = W₁ ⊓ W₂

def OrthogCompl {k V:Type} [AddCommGroup V] [Field k] [Module k V] (S : Set V) 
    (β:BilinForm k V)
    : Subspace k V where
  carrier := { v | ∀ (x:S), β v x = 0 }
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

theorem orthog_decomp (W:Submodule k V) (nd : NondegOn β W) :
  is_internal_direct_sum W (OrthogCompl W β) := by sorry



--------------------------------------------------------------------------------
-- direct sums and orthogonal complements
-- ======================================

structure internal_direct_sum (W₁ W₂ : Submodule k V) where
  span : ⊤ = W₁ ⊔ W₂
  zero : ⊥ = W₁ ⊓ W₂

structure orthog_direct_sum (β:BilinForm k V) (W : Submodule k V) where
  compl : Submodule k V
  ds : internal_direct_sum W compl
  orthog : ∀ v₁ ∈ W, ∀ v₂ ∈ compl, β v₁ v₂ = 0  

def OrthogCompl {k V:Type} [AddCommGroup V] [Field k] [Module k V] (S : Set V) 
    (β:BilinForm k V)
    : Subspace k V where
  carrier := { v | ∀ (x:S), β v x = 0 }
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

def orthog_decomp (β:BilinForm k V) (W:Submodule k V) (wnd : NondegOn β W):
  orthog_direct_sum β W where
   compl := OrthogCompl W β
   ds := 
     { span := by sorry
     , zero := by sorry
     }
   orthog := by sorry

--------------------------------------------------------------------------------
-- hyperbolic subspaces
-- ====================

def Alt (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v : V, β v v = 0

def Symm (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v


def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
        β e e = 0  ∧  β f f = 0  ∧  β e f = 1

def hypsubspace (β:BilinForm k V) {e f : V} (h:hyp_pair β e f) : Subspace k V := 
  Submodule.span k {e,f}

theorem hyp2_nondeg_symm (β:BilinForm k V) 
  (bsymm : Symm β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2)  := by sorry

theorem hyp2_nondeg_alt (β:BilinForm k V) 
  (balt : Alt β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2)  := by sorry


-- using `orthog_decomp` above, we get

def hyp2_decomp_symm (β:BilinForm k V) (bsymm : Symm β) (e f : V) (h2:hyp_pair β e f) 
  : orthog_direct_sum β (hypsubspace β h2) :=
  orthog_decomp β (hypsubspace β h2) (hyp2_nondeg_symm  β bsymm h2)

def hyp2_decomp_alt (β:BilinForm k V) (balt : Alt β) (e f : V) (h2:hyp_pair β e f) 
  : orthog_direct_sum β (hypsubspace β h2) :=
  orthog_decomp β (hypsubspace β h2) (hyp2_nondeg_alt  β balt h2)


-- finally, we need

theorem hyp_pair_exists_symm (β:BilinForm k V) (bsymm : Symm β) (e:V) (enz : e ≠ 0) (eiso : β e e  = 0) 
  (hnl : ⊤ ≠ Submodule.span k {e}):
   ∃ f, hyp_pair β e f := by sorry
  
theorem hyp_pair_exists_alt (β:BilinForm k V) (bsymm : Symm β) (e:V) (enz : e ≠ 0) 
  (hnl : ⊤ ≠ Submodule.span k {e}):
   ∃ f, hyp_pair β e f := by sorry
  

  
