 --------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/


import Mathlib.Tactic


-- Lean has a typeclass `Lattice` for (Complete) Lattices -- see
-- [Math-in-Lean] §2.5

--   "A lattice is a structure that extends a partial order with
--   operations ⊓ and ⊔ that are analogous to min and max on the real
--   numbers"

-- type ⊓ as \glb ("greatest lower bound") and ⊔ as \lub ("least upper
-- bound")

-- a complete lattice has a "top element" denoted ⊤ (\top) and a "bottom
-- element" denoted ⊥ (\bot)

--------------------------------------------------------------------------------

-- Let's give some examples of lattices: 

-- the real numbers form a lattice with min and max
-- doesn't have  ⊤ or ⊥

example : Lattice ℝ := inferInstance

--#check (⊥:ℝ) 

--------------------------------------------------------------------------------

-- for any type `X`, `Set X` is a lattice

section Sets 

variable (X : Type) 

example : Lattice (Set X) := inferInstance


#check (⊥:Set X)
 
-- ⊥ is the emptyset 

example :  ⊥ = (∅:Set X) := rfl

-- and ⊤ is X itself

example : ⊤ = (Set.univ : Set X) := rfl


-- ⊔ is ∪ and ⊓ is ∩ 

example (A B :Set X) : A ⊓ B = A ∩ B := rfl
example (A B :Set X) : A ⊔ B = A ∪ B := rfl

end Sets
--------------------------------------------------------------------------------

-- the type `Prop` of Propositions is a lattice

noncomputable

example : Lattice Prop := inferInstance

#check False
#check True 

example : ⊥ = False := rfl
example : ⊤ = True := rfl


example (p q : Prop) : p ⊔ q = (p ∨ q) := rfl
example (p q : Prop) : p ⊓ q = (p ∧ q) := rfl

-- (Note that the parens on the RHS are needed!)

--------------------------------------------------------------------------------
-- and finally: subspaces of a vector space form a lattice

section lattice_vector_space

variable {k : Type} [Field k]

variable {V : Type} [ AddCommGroup V ] [ Module k V ]

example : Lattice (Submodule k V) := inferInstance

-- operations? ⊓ corresponds to the intersection of subspaces

example (W₁ W₂ : Submodule k V) : ↑(W₁ ⊓ W₂) = ((↑W₁ ∩ ↑W₂):Set V) := by simp

-- the symbol ↑ is a coercion, in this cases coercing a term of type
-- `Submodule k V` to a term of type `Set ↑V` where ↑V means "V viewed
-- as a set". Lean permits us to be sloppy and write `Set V` instead.

--  so `↑(W₁ ⊓ W₂)` means "the subset corresponding to the subspace
-- `W₁ ⊓ W₂`"

variable (U:Submodule k V) in
#check (U:Set V)

-- put another way, we have

example (W₁ W₂ : Submodule k V) (x : V) : x ∈ W₁ ⊓ W₂ ↔ (x ∈ W₁ ∧ x ∈ W₂) := by 
  simp
    
-- warning: ⊔ does *not* correspond (directly) to the union, since the
-- union of subspaces is usually not a subspace.

-- in fact in blackboard math, W₁ ⊔ W₂ is the sum W₁ + W₂ of the
-- subspaces, or -- what amounts to the same thing -- the span of the
-- set W₁ ∪ W₂ (there is the union!)

example (W₁ W₂ : Submodule k V) : W₁ ⊔ W₂ = Submodule.span k ( W₁ ∪ W₂ ) := by 
  rw [ Submodule.span_union (↑W₁:Set V) ↑W₂ ]
  simp    

-- ⊥ is the zero-subspace 

example : ⊥ = (Submodule.span k { (0:V) }) := by simp

-- put another way:

example (x : V) : x ∈ (⊥:Submodule k V) → x = 0 := by simp

-- and ⊤ is the whole space

example : (⊤:Submodule k V) = (Set.univ:Set V) := by simp


-- put another way:

example (x:V) : x ∈ (⊤:Submodule k V) := by simp
  
section lattice_vector_space  

--------------------------------------------------------------------------------

section exercises

-- problem 1
-- =========

section problem1

-- prove these "absorption" properties of lattices.
-- you can read more about lattices in math-in-lean §2.5

variable {α : Type*} [Lattice α]
variable (x y z : α)

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry

end problem1

-- ==============================================================================

-- now let's talk about linear algebra

variable {k : Type*} [Field k]

-- problem 2
-- =========

section problem2

variable {V : Type*} [ AddCommGroup V ] [ Module k V ]
variable {f g : V →ₗ[k] k}
open LinearMap

-- let's prove: if f is a non-zero multiple of g then f and g have the
-- same kernel

-- we can use the following. Presumably this is in the library, but ...
lemma non_zero_multiple (t:k) (hnz : t ≠ 0) (v:V) : 
  t•v = 0 → v = 0 := by 
  intro h
  have tinv_nz : t⁻¹ ≠ 0 := inv_ne_zero hnz
  rw [ ← one_smul k v ]
  rw [ ← Field.mul_inv_cancel t⁻¹ tinv_nz , inv_inv ]
  rw [ ← smul_eq_mul ]
  rw [ smul_assoc ]
  rw [ h ]
  simp
  
theorem ker_eq_of_multiple (t:k) (ht: t ≠ 0) (hfg :f = t•g) : 
  ker f = ker g := by sorry

end problem2



variable {V : Type} [ AddCommGroup V ] [ Module k V ]
variable {W : Type} [ AddCommGroup W ] [ Module k W ]
variable {X : Type} [ AddCommGroup X ] [ Module k X ]

variable {π : V →ₗ[k] W}    
variable {ψ : W →ₗ[k] X}    

-- maybe useful to draw this diagramatically, blackboard style

--     π      ψ
--  V ---> W ---> X
--


-- the kernel of the linear transformation π in blackboard math
-- is { x ∈ V ∣ π x = 0 }.

-- for example, we have

example : LinearMap.ker π = ⊤ → π = 0 :=  by simp

-- and

example : (LinearMap.ker π = ⊥) → Function.Injective π := 
  LinearMap.ker_eq_bot.mp

-- Let's avoid some typing:

open Submodule
open LinearMap

-- try to finish the proofs of the following:


-- problem 3.
-- ==========

example (hpsi :  ker ψ = ⊥) : ker (ψ ∘ₗ π) = ker π := by 
  ext 
  simp
  sorry

-- the symbol ∘ₗ stands for LinearMap.comp -- i.e. for the composition of linear maps

-- problem 4.
-- ==========

example (hpi : map π ⊤ = ⊤) : map (ψ ∘ₗ π) ⊤ = (map ψ ⊤ : Submodule k X) := by 
  ext
  simp
  sorry

variable (ι κ : Type) in
#check ι ⊕ κ 

-- here `map ψ A` is the image under the linear map `ψ` of the submodule `A:Submodule k W`
-- i.e. in blackboard math we have
-- map ψ A = { z ∈ X ∣ z = π y for some y ∈ A }.
-- see Submodule.map

-- see especially `Submodule.map.mem_map` in the API docs for a useful
-- characterization


-- problem 5.
-- ==========

-- let's work with a three dimensional ℚ vector space
-- in Lean the standard model for such a thing is `Fin 3 → k`

-- let's define some vectors


def u : Fin 3 → ℚ
    | 0 => 1
    | 1 => 1
    | 2 => 0

def v : Fin 3 → ℚ
    | 0 => 1
    | 1 => -1
    | 2 => 0

def w : Fin 3 → ℚ
    | 0 => 3  
    | 1 => 2
    | 2 => 1


-- Lean provides some easier notation. ![a,b,c] denotes the function
-- that takes value a at 0, b at 1 etc.

-- here is a (somewhat clunky) check that these notions are the same

example :  w  = ![3,2,1]  := by
  ext n
  simp [w]
  match n with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num; simp

-- and here is slicker version

example :  w  = ![3,2,1]  := by
  ext n
  simp [w]
  split; repeat norm_num ; simp
  
-- prove the linear independence of u,v,w. namely, finish the proof of the following

lemma add_eq {k:Type} [Field k] {a b c d : k} (h1 : a = b) (h2 : c = d) 
  : a + c = b + d := by
  rw [ h1, h2 ] 

lemma zero_iff_two_mul_zero (a:ℚ) : a = 0 ↔ 2*a = 0 := by
  constructor
  repeat intro h ; linarith

example (a b c : ℚ) : (a•(![1,1,0]:Fin 3 → ℚ) + b•![1,-1,0] + c•![3,2,1] = 0) → 
   (a =0 ∧ b = 0 ∧ c = 0) := by
   norm_num 
   intro h1 h2 h3 _
   sorry
  
end exercises
