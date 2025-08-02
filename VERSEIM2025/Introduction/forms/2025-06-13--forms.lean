 --------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic


-- Let's get started trying to formalize some results in linear algebra
-- about bilinear forms!

-- As a first step, we should formalize the proof that there is -- up to
-- the right notion of conjugacy -- only one non-degenerate alternating
-- form on an even dimensional vector space (and that no such form exists
-- on any odd dimensional vector space). This statement is true for any
-- field whatsoever.  (Corresponding statements for symmetric forms are
-- more complicated -- in particular, the description of conjugacy
-- classes of symmetric forms depends on the field -- so the alternating
-- case seems a good place to start).

-- We are going to work with a finite vector space over a field \(k\):

variable (k : Type) [ Field k ]
variable (V : Type) [ AddCommGroup V ] [ Module k V ]
                    [ FiniteDimensional k V ]

variable (W : Type) [ AddCommGroup W ] [ Module k W ]
                    [ FiniteDimensional k W ]


-- You can read about the `FiniteDimensional` typeclass in §12 of [Math
-- in Lean].

-- You should read about how Lean represents a basis of our vector space(s):

variable {ι : Type} (B : Basis ι k V) [DecidableEq ι] [Fintype ι] 

-- terms i:ι index the basis vectors `B i`

noncomputable
example (i:ι) : V := B i

-- B i is a vector in V 

variable {μ : Type} (C : Basis μ k W) [DecidableEq μ] [Fintype μ]

-- Read this as: "`B` is a basis for the `k`-vector space `V` with
-- index set `ι`".

noncomputable
example : Fintype ι := FiniteDimensional.fintypeBasisIndex B



-- Bilinear forms are precisely terms of type `V →ₗ[k] V →ₗ[k] k`

-- think this through!!

-- **task**

-- prove something like the following:



-- One goal: show that the for the basis `B`, give a bilinear form
-- `β:V →ₗ[k] V →ₗ[k] k` is the same as to give an `ι` by `ι` matrix
-- `M`

-- and once we do that, we can give the definition that β is
-- non-degenerate just in case `M` is `Invertible` (there is an
-- `Invertible` typeclass you can read about in §10.4.1 of
-- [Math-in-lean].

-- Before trying to prove that, we should understand the similar
-- statement that to give a linear mapping `T:V →ₗ[k] V` is the same
-- as to give an `ι` by `ι` matrix.

-- For types `I` and `J`, an `I` by `J` matrix over `k` is essentially
-- a term of type `I → J → k`, though there is actually a type
-- `Matrix`

-- here is the type of n × m matrices for natural numbers n,m

example (m n : ℕ) : Type := Matrix (Fin n) (Fin m) k

-- under the hood this is just `Fin n → Fin m → k` but having a new
-- name lets `Matrix (Fin n) (Fin m)` have possibly-different
-- instances than `Fin n → Fin m → k`

-- for types I and J, here is the type of I × J matrices with
-- coefficients in our field k

example (I J : Type) : Type := Matrix I J k


-- We need a good understanding of what it means that `B.constr k` (or
-- `Basis.constr B k`) gives a linear equivalence between `ι → W` and
-- `V →ₗ[k] W`

noncomputable
example : (ι → W) ≃ₗ[k] V →ₗ[k] W := B.constr k

-- On top of this construction, there is a linear equivalence


open LinearMap

noncomputable
example : (V →ₗ[k] W) ≃ₗ[k] Matrix μ ι k := toMatrix B C

#check (LinearMap.toMatrix B C : (V →ₗ[k] W) ≃ₗ[k] Matrix μ ι k)


-- this should be read " the vector space of linear maps V → W is
-- equivalent to the vector space of μ × ι matrices ".

-- the desired isomorphism between "bilinear forms on V" and square
-- matrices should be defined in essentially the same way as
-- `Basis.constr` (or maybe: *using* `Basis.const` somehow).


-- Let's make a definition (mainly to avoid typing all the arrows).

@[simp]
def Bilinear (V:Type) (k:Type) [Field k] [AddCommGroup V] [Module k V] : Type 
  := V →ₗ[k] V →ₗ[k] k 

-- Task 1.
-- ======

-- given a basis B of V, we want to define

-- a mapping

-- def Bilinear.toMatrix (V:...) (k:...) (B: ...) (β:Bilinear V k) : Matrix ι ι k := ...

-- and eventually we want to prove this mapping "is" a linear
-- equivalence. 

-- Task 2. 
-- ======

-- formulate theorems confirming the linearity properties of our
-- Bilinear terms

-- (it looks to me like the simplifier tactic can prove them).

--  β.toFun (t•x + y) z = t•β.toFun x z + β.toFun y z 

-- and

--  β.toFun x (t•y + z) = t•β.toFun x y + β.toFun x z 

-- Task 3.
-- ======

-- define predicates

def Alternating (β:Bilinear V k) : Prop := sorry

-- and

def Alternating' (β:Bilinear V k): Prop := sorry

-- for alternating (i.e. anti-symmetric, also called skew-symmetric)
-- where the first one stipulates β x x = 0 for all x and the second
-- requires β x y = - β y x for all x, y.

-- Give a formalized proof that `Alternating β → Alternating' β`


-- Task 4.
-- ======

-- formulate and prove the theorem that

-- β x x = 0 → β x y = - β y x

-- we also need to show that if the characteristic of k is not 2, the
-- converse holds. We'll need to read about the characteristic to do
-- this, but the above implication should work without knowing about
-- this...


-- Task 5.
-- ======

-- define a predicate "Nondegenerate" for bilinear forms.  

def Nondeg (β:Bilinear V k): Prop := sorry

-- One says
-- that a bilinear form β is non-degenerate if we have the implication

-- (*)
-- ∀ x, (∀ y, β x y = 0 → x = 0)

-- in words: "for a fixed x, if β x y = 0 for every y, then x = 0".


-- On the other hand, we could formulate this non-degeneracy "in the
-- other variable", like this:

-- (**)
-- ∀ y, (∀ x, β x y = 0 → y = 0)

-- in words: "for a fixed y, if β x y = 0 for every x, then y = 0".


-- onece we have the matrix representation of β we'll be able to prove
-- that (*) ↔ (**)

-- meanwhile, give a formalized proof of this for β satisfying the
-- Alternating predicate
