--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- I had a thought yesterday evening that it is perhaps easier to
-- start with symmetric bilinear forms, despite their eventual greater
-- comlpexity.

-- e.g. you probably saw what is known as "Gram-Schmidt" in your
-- linear algebra class. So let's implement that!

-- We need some notions about bilinear forms.

-- remember that `V →ₗ[k] V →ₗ[k] k` is the type of bilinear mappings on the vector space `V`

-- lets define predicates for *symmetric* and *alternating* bilinear forms

def BilSymmetric {k V : Type} [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)  : Prop := 
  ∀ (x y : V), β x y = β y x

def BilAlternating {k V : Type} [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)  : Prop := 
  ∀ (x : V), β x x = 0


-- *for the time being* we are going to work with k = ℝ

-- we work with a real vector space:

variable {V : Type} [AddCommGroup V] [Module ℝ V ]

-- and we suppose V has a finite basis indexed by the finite type ι (\iota)

variable (b : Basis ι ℝ V) [Fintype ι]


-- Next, let β be a symmetric bilinear form on V

variable (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) 
variable (beta_symm : BilSymmetric β)

-- Finally, we are going to suppose that β is *positive definite*

def PosDef (V : Type) [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, β x x ≥ 0 ∧ x ≠ 0 → β x x > 0

-- the positive definite assumption implies that β is non-degenerate,
-- but is an "easier" assumption to reason about. That is the main
-- reason I think it is a good idea to consider this case first!

-- 

-- Our goal wil be to show that V has an orthogonal basis

-- more generally we say that for a type `I`, a function `f:I → V` is
-- orthogonal with respect to β if for each (i j : I) we have

-- `i ≠ j → β (f i) β (f j) = 0`.

-- let's make a predicate for orthogonal bases

def OrthogBasis (V : Type) [AddCommGroup V] [ Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:Basis I ℝ V) : Prop := ∀ (i j : I), i ≠ j → β (c i) (c j) = 0

-- here is our target Theorem

theorem posdef_has_orthog_basis (V : Type) [AddCommGroup V] [ Module ℝ V ] 
  ( b: Basis ι ℝ V ) [Fintype ι] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp:PosDef V β)
  : ∃ (c:Basis ι ℝ V), OrthogBasis V β c := by sorry


-- I believe the simplest way to prove this will be to use what is
-- known as the *Gram-Schmidt orthogonalization process*.

-- https://en.wikipedia.org/wiki/Gram%E2%80%93Schmidt_process

-- and see [Liesen and Hemrmann, §12.2]

--------------------------------------------------------------------------------

-- Hear are some lemmas that I believe we will need (of course, we may
-- need to massage the statements -- and perhaps especially the names!
-- --  but these are a good starting point I think).

-- some of these are general, and so I'll return to more general assumptions

section lemmas

--------------------------------------------------------------------------------

-- 1. the orthogonal complement of a `S:Set V` is a subspace of V

-- in blackboard math, the orthogonal complement of S is often written S^⟂ 


-- someone needs to give the proofs in the following definition.

def OrthogComplement {k V:Type} [AddCommGroup V] [Field k] [Module k V] (S : Set V) 
    {β:V →ₗ[k] V →ₗ[k] k} : Subspace k V where
  carrier := { v | ∀ (x:S), β v x = 0 }
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

-- you should read in [math-in-lean] §10.2 about `add_mem'` vs `add_mem` etc.

--------------------------------------------------------------------------------

-- 2. Suppoe that W₁ and W₂ are subspaces of a vector space V, and
-- suppose that W₁ and W₂ are orthogonal  to one another.

-- if we have a linearly independent subset of W₁ and a linearly
-- independent subset of W₂, we want to argue that the "union" of
-- these subsets is linearly independent.

-- Lean prefers to talk about linear independence of functions `ι → V`
-- so let's formulate it that way.

-- to start with I'm going to work over ℝ because otherwise we need to
-- assume something about non-degneracy of β on the subspaces W₁ and
-- W₂. The PosDef assumption makes this easy!

-- first, let's make a predicate for "orthogonal"

def OrthogSubspaces (k V:Type) [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)
  (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0

inductive DisjointUnion (ι₁ ι₂ : Type) where
 | left : ι₁ → DisjointUnion ι₁ ι₂
 | right : ι₂ → DisjointUnion ι₁ ι₂

def disjointUnion_funs {ι₁ ι₂ X: Type} ( f₁:ι₁ → X) (f₂:ι₂ → X) (u:DisjointUnion ι₁ ι₂) : X :=
   match u with
    | DisjointUnion.left x => f₁ x 
    | DisjointUnion.right y => f₂ y


theorem lin_indep_of_orthog (V : Type) [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (hp:PosDef V β) (W₁ W₂ : Submodule ℝ V) (ho:OrthogSubspaces ℝ V β W₁ W₂) 
  (ι₁ ι₂: Type) [Fintype ι₁] [Fintype ι₂] 
  (f₁:ι₁ → V) (f₂:ι₂ → V)
  (hi₁:LinearIndependent ℝ f₁) (hi₂:LinearIndependent ℝ f₂) : 
  LinearIndependent ℝ (disjointUnion_funs f₁ f₂) := by sorry
   


--------------------------------------------------------------------------------

-- 3.  direct sum

-- If W₁ and W₁ are subspaces of a vector space, we want to give
-- conditions under which V is the *direct sum*. I believe (hope) that
-- [Liesen and Hemrmann] defines the notion. (I'll check!)

theorem direct_sum_unique_repr (k V : Type) [Field k] [AddCommGroup V] [Module k V] 
  (W₁ W₂ : Submodule k V) (h_span : V = W₁ ⊔ W₂) (h_int : ⊥ = W₁ ⊓ W₂) 
  (x₁ x₂ y₁ y₂ : V) (h₁ : x₁ ∈ W₁ ∧ y₁ ∈ W₁) (h₂ : x₂ ∈ W₂ ∧ y₂ ∈ W₂ ) :
  x₁ + x₂ = y₁ + y₂ → x₁ = y₁ ∧ x₂ = y₂ := by sorry

