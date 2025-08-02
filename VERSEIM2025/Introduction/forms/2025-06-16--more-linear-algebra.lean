--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- I believe I found how to use the `FiniteDimensional` typeclass.

noncomputable 
section Finite?

variable (k:Type) [Field k]
variable (V:Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

--open BigOperators ; 

-- here we show how to deduce that if V is finite dimensional, a basis is finite
-- and hence we can e.g. define the sum of all the basis vectors

example (B : Basis ι k V): V := by
  have _ : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  exact ∑ i, B i


-- here are some examples of other ways of "summing vectors indexed by
-- terms of a type";

-- possible if the type is finite - i.e. has a `FinType` instance

example (I : Type) [Fintype I] (f:I → V) : V := ∑ i, f i

-- possible if the function f has finite support -- i.e. `f i = 0` for
-- all but finitely many `i : I`. A function with finite support is
-- indicated via `f : I →₀ V`, and the type `I →₀ X` which is defined
-- whenever X has a `Zero` instance.

example (I : Type) (f:I →₀ V) : V := ∑ i ∈ f.support, f i

-- you can also sum over finite subsets of a type `I`. `Finset I` is
-- the type of all finite sets of elements of I

example (I : Type) (A : Finset I) (f:I → V) :  V := ∑ i ∈ A, f i

end Finite?


noncomputable
section Bases

-- How to form a basis? Let's see some manipulations with bases.

-- let's start with a 3-dimensional vector space. To make things
-- easier we'll work over ℚ.

-- let's start by working with the standard model of a 3 dimensional
-- ℚ-vector space, namely `Fin 3 → ℚ`

-- Now, we know that the vectors `[ 1 1 0 ]`, `[0 2 1 ]` and `[0 0 3 ]`
-- are linearly independent.

-- let's construct the matrix with those columns
w
open Matrix

@[simp]
def M : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 1, 2, 0; 0, 1, 3]

#eval M.det
#reduce M.det

#eval M *ᵥ ![1,0,0]
#eval M *ᵥ ![0,1,0]
#eval M *ᵥ ![0,0,1]

-- now our matrix M determines a linear transformation `(Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ)`

-- to get this transformation, we'll use `Matrix.toLin` which takes as arguments
-- a pair of bases and returns an equivalence `Matrix m n R ≃ₗ[R] M₁ →ₗ[R] M₂`

#check toLin

-- we will use `Pi.basisfun` for both arguments

-- see the discussion in [math-in-lean] §10.4.2 for how to get the "standard basis"
-- of `τ → ℚ` for a `Fintype` τ.

#check Pi.basisFun ℚ (Fin 3)

#check Basis

@[simp]
def TM : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) := by
  have stdbasis : Basis (Fin 3) ℚ (Fin 3 → ℚ) := Pi.basisFun _ _
  exact toLin stdbasis stdbasis M

example :  TM ![1,0,0] = M *ᵥ ![1,0,0] := by 
  unfold TM
  unfold toLin
  unfold Pi.basisFun

-- but in fact, since det M is non-zero, the linear transformation
-- determined by the matrix M is even a linear equivalence.

lemma M_lower_tri : M.BlockTriangular  ⇑OrderDual.toDual := by
  sorry

lemma Mdet : M.det = (6:ℚ) := 
  calc  
    M.det   = ∏ i, M i i        := det_of_lowerTriangular M M_lower_tri
    _       = 6                 := by 
                                    unfold M
                                    unfold Finset.prod 
                                    simp
                                    norm_num

lemma Munit : Invertible M.det := by 
  rw [ Mdet ]
  norm_num

lemma Minv : Invertible M := by
  have _ : Invertible M.det := by rw [Mdet]; norm_num
  exact (invertibleEquivDetInvertible M).mpr
  
  
@[simp]
def TMe : (Fin 3 → ℚ) ≃ₗ[ℚ] (Fin 3 → ℚ) := by
  have stdbasis : Basis (Fin 3) ℚ (Fin 3 → ℚ) := Pi.basisFun _ _
  have _ : Invertible M := by 
    (invertibleEquivDetInvertible M).mpr
  exact toLinearEquiv' M Minv
--  exact toLinearEquiv stdbasis M Minv


example : TM ![1,0,0] = ![1,1,0] := by 
  ext
  simp


  

  

  -- unfold TMe
  -- unfold M
  -- unfold toLinearEquiv
  -- simp
  -- unfold toLin
  -- unfold LinearMap.toMatrix 
  


-- So we could use following for our basis:

-- def C (b:Basis (Fin 3) k V): Fin 3 → V 
--   | 0 => b 0 + b 1
--   | 1 => b 1 + b 2
--   | 2 => b 2

-- to make a basis, we need proofs for `LinearIndependent k C` and for
-- `⊤ ≤ Submodule.span k (Set.range C)`

-- #check B.repr

#check Basis.mk

#check LinearIndependent

--lemma C_indep : LinearIndependent k (C B) := by
                   

variable {V:Type} [AddCommGroup V] [Module ℚ V]
variable {B:Basis (Fin 3) ℚ V}

-- Here we are *stipulating* that there are three basis vectors: `B 0`, `B 1` and `B 2`

-- Let's try to define a new basis.

-- We are suppose to give a basis of V as a function from some
-- indexing type to V


end Bases

noncomputable
section Bases2

variable {V:Type} [AddCommGroup V] [Module ℚ V]

variable {B: Basis (Fin 2) ℚ V}

def A  : Matrix (Fin 2) (Fin 2) ℚ := !![ 1,1;0,2]

open Matrix

@[simp]
def TA {V:Type} [AddCommGroup V] [Module ℚ V] {B:Basis (Fin 2) ℚ V} (A:Matrix (Fin 2) (Fin 2) ℚ): V →ₗ[ℚ] V := by
  exact (toLin B B).toFun A 


end Bases2
