--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/


import Mathlib.Tactic

variable (n :ℕ) [NeZero n]

-- we can use an arbitrary field, but to do computations, 
-- let's use ℚ 


-- for any field k, a standard model of a vector space is `Fin n → k`

-- we can represent elements of this space using notation like
-- `![a₀, a₁, a₂, a₃]` (where n = 3 and `aᵢ:k`).


#eval ![(1:ℚ),2,3,4] 3

#eval (![1,2,3,4]:Fin 4 → ℚ) 3


#eval ![(1:ℚ),1] + ((1:ℚ)/3)•![2,2]

example : Module ℚ (Fin 3 → ℚ) := inferInstance

-- you can systematically get the standard basis vectors using `Pi.single`

#check Pi.single

example : Fin 3 → ℚ :=  Pi.single (0:Fin 3) (1:ℚ)

#check (Pi.single (0:Fin 3) (1:ℚ): Fin 3 → ℚ)

#check (Pi.single (0:Fin 3) (1:ℚ) : Fin 3 → ℚ) (0:Fin 3)
#eval (Pi.single (0:Fin 3) (1:ℚ) : Fin 3 → ℚ) (1:Fin 3)

example : (Pi.single (0:Fin 3) (1:ℚ) : Fin 3 → ℚ) = ![1,0,0] := by trivial

-- let's try to work out what proof term the `trivial` tactic used:

example : (Pi.single (0:Fin 3) (1:ℚ) : Fin 3 → ℚ) = ![1,0,0] := by 
  exact List.ofFn_inj.mp rfl

-- what this tells us is that there is a function List.ofFn

#eval List.ofFn ![1,0,0]

#eval (fun (i:Fin 5) => i.toNat)

#eval List.ofFn (fun (i:Fin 5) => i.toNat)

-- and Lean is testing equality of the functions by testing equality
-- of the corresponding lists.

-- let's get a proof of linear independence of the standard basis vectors...

@[simp]
def sbv (n:ℕ) : Fin n → Fin n → ℚ := by
  intro i
  exact Pi.single i (1:ℚ)


def sbv' (n:ℕ) : Fin n → Fin n → ℚ := fun i => 
  Pi.single i (1:ℚ) 


-- so `sbv n 0`, `sbv n 1`, ... `sbv n (n-1)` are the standard basis vectors of
-- `Fin n → ℚ`

#eval sbv 3 

#check LinearIndependent 

-- lets try to use the theorem `linearIndependent_iff` to get linear independence


--#check linearIndependent_iff 

-- LinearIndependent k v ↔ ∀ (l : ι →₀ R), (Finsupp.linearCombination R v) l = 0 → l = 0

-- it says that for a vector-valued function `v:Fin 3 → (Fin 3 → ℚ)`
-- we can deduce linear independence by the condition

-- ∀ (l:Fin 3 → ℚ), whenever (Finsupp.linearCombination k v) l = 0, then l = 0.

variable (l:Fin n → ℚ) in
#check Fintype.linearCombination_apply ℚ (sbv n) l 

example (l:Fin n →ℚ) :  Fintype.linearCombination ℚ (sbv n) l = ∑ i:Fin n, l i • (sbv n) i := by
  rw [ ←Fintype.linearCombination_apply ℚ (sbv n) ]


lemma single_smul (n : ℕ) (l : Fin n → ℚ) : (i:Fin n) → 
  Pi.single (M:=fun _ => ℚ) i (l i • (1:ℚ)) = l i • Pi.single (M:=fun _ => ℚ) i (1:ℚ)  := by
  intro i
  apply (Pi.single_smul' i (l i) (1:ℚ))  

lemma sbv_lin_comb' (n:ℕ) (l:Fin n → ℚ) : 
   ∑ i, l i • sbv n i  = l  := by
   ext j
   unfold sbv
   rw [  ← Fintype.sum_congr _ _ (single_smul n l) ] 
   simp

-- the final `simp` in the previous proof (surely) uses `Fintype.sum_pi_single` or
-- `Fintype.sum_pi_single'`

#check Fintype.sum_pi_single' 

-- for our purposes, this says:

-- Fintype.sum_pi_single' (n:ℕ) {V : Type} [AddCommGroup V] (i : Fin n) 
-- (a : V) : ∑ j, Pi.single i a j = a

-- so `single'` is somehow playing the role of the "Kronecker delta " δ_{i,j}.

theorem sbv_lin_indep (n:ℕ) : LinearIndependent ℚ (sbv n) := by 
  apply Fintype.linearIndependent_iff.mpr  
  intro l  h 
  rw [ sbv_lin_comb' n ] at h
  intro i
  exact congrFun h i


-- to talk about spanning, we must transform the function 
-- `sbv n : Fin n → (Fin n → ℚ)` into a *subset*.

-- in general, if `f : X → Y` and `s: Set X`, the image of s via f is written
-- `image f s` or in symbols `f '' s`.

-- So the set we want to consider the span of is:

-- (sbv n) '' (⊤:Set (Fin n))


example : Set (Fin n → ℚ) := (sbv n) '' ⊤

example : Set (Fin n → ℚ) := Set.image (sbv n) ⊤

theorem sbv_span (n:ℕ) : Submodule.span ℚ (Set.image (sbv n) ⊤) = (⊤:Submodule ℚ (Fin n → ℚ)) := by 
  ext v
  have : v = ∑ j, v j • sbv n j := by 
    ext k
    unfold sbv
    rw [ ← Fintype.sum_congr _ _ (single_smul n v) ]
    simp
  sorry
  
--------------------------------------------------------------------------------

-- note that the linear independence of the standard basis is actually
-- already proved in lean (see below).

-- dimension of a finite dimensional space is known as `Module.finrank`

example : Module.finrank ℚ (Fin 5 → ℚ) = 5 := by simp  

example : Module.finrank ℝ ℂ = 2 := by 
  exact Complex.finrank_real_complex 

-- I'm not actually sure at the moment how to do this one...
example : Module.finrank ℝ (Fin 5 → ℂ) = 10 := by 
  sorry

example : Module ℚ (Matrix (Fin 4) (Fin 5) ℚ) := inferInstance

example : Module.finrank ℚ  (Matrix (Fin 4) (Fin 4) ℚ) = 16 := by 
  sorry


-- so what is a basis in mathlib?

-- there is a structure `Basis` (find it in Mathlib.LinearAlgebra.Basis.Def )

-- for a k-vector space V, a basis of V *is* the data of an linear
-- equivalence `repr`

-- between V and `ι →₀ k` for some type ι -- i.e.

-- `φ: V ≃ₗ[k] ι →₀ k`

example (k V : Type) [Field k] [AddCommGroup V] [Module k V] : Basis ι k V where
  repr := sorry -- the type of `repr` should be `V ≃ₗ[k] ι →₀ k`

-- The idea is that such a linear equivalence indeed determines 
-- basis vectors parametrized by `ι` in the usual, black-board math sense. Indeed, for a term

-- `x:ι`



  
  
