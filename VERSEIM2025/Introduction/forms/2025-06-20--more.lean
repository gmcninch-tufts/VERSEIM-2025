--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- recall we introduced the disjoint union

inductive DisjointUnion (ι₁ ι₂ : Type) where
 | left : ι₁ → DisjointUnion ι₁ ι₂
 | right : ι₂ → DisjointUnion ι₁ ι₂

def disjointUnion_funs {ι₁ ι₂ X: Type} ( f₁:ι₁ → X) (f₂:ι₂ → X) (u:DisjointUnion ι₁ ι₂) : X :=
   match u with
    | DisjointUnion.left x => f₁ x 
    | DisjointUnion.right y => f₂ y


-- here are some statements about disjoint_union that should be established

-- first establish an equivalence of types between the disjoint union
-- of `Fin n` and `Fin m` with the type `Fin (n+m)`

-- We define the `toFun` of our equivalence as follows:

-- terms of the form `left x` where `(x:Fin n)` is sent to `(x:Fin (n + m))`

-- and terms of the form `right x` where `(x:Fin m)` is sent to
-- `(x + n : Fin(n+m))`

-- the summation is accomplished via `Fin.castAdd`

#check Fin.castAdd

-- ** exercise ** you'll need to define the remaining components of
-- the structure determining the equivalence.

open DisjointUnion
def fin_disjoint_fin_equiv_fin (n m: ℕ) : DisjointUnion (Fin n) (Fin m) ≃ Fin (n+m) where
  toFun := fun i => 
    match i with
    | left x => Fin.castAdd m x
    | right x => by
        rw [ add_comm ] 
        exact Fin.castAdd n x 
  invFun := by 
    rintro ⟨i,_⟩
    if h : i < n then 
       have : NeZero n := NeZero.mk (by linarith)
       exact left (Fin.ofNat n i)
    else
       have : NeZero m := NeZero.mk (by linarith)
       exact right (Fin.ofNat m (n-i))
  left_inv := by sorry
  right_inv := by sorry

--------------------------------------------------------------------------------

#check Fin.ofNat 3 1
#eval Fin.ofNat 3 5

-- `i:Fin n` is a natural number, together with a proof that `i < n`

-- this result is perhaps what should be proved first before proving
-- the result I earlier described as `lin_indep_of_orthog`.

theorem lin_indep_by_transverse_subspaces 
   (k V : Type) [Field k] [AddCommGroup V] [Module k V] (I₁ I₂ : Type)
   (b₁ : I₁ → V) (b₂ : I₂ → V)
   (b1_indep : LinearIndependent k b₁) 
   (b2_indep : LinearIndependent k b₂) 
   (W₁ W₂ : Submodule k V)               
   (h_int : W₁ ⊓ W₂ = ⊥)
   (hbw1 : ∀ i, b₁ i ∈ W₁)
   (hbw2 : ∀ i, b₂ i ∈ W₂)
   : LinearIndependent k (disjointUnion_funs b₁ b₂) := by sorry



