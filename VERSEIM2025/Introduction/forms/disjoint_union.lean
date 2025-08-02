
import Mathlib.Tactic

import Mathlib.Data.FinEnum

-- THere are (at least) four different parts of Mathlib that define a
-- notion of cardinality.


-- Nat.card
-- Fintype.card
-- FinEnum.card
-- Finset.card

-- Sometimes (as below) we have to "convince" Lean that they are "the same".

-- We are going to give several proofs below of the fact that there is
-- an equivalence `(Fin n) ⊕ (Fin m) ≃ Fin (n+m)`

--------------------------------------------------------------------------------
-- I. via Fintype

lemma card_fin_sum_fin (n m : ℕ) : Fintype.card ((Fin n) ⊕ (Fin m)) = n + m := by simp

-- just by knowing the cardinality, we get an (abstract, noncomputable) equivalence!

noncomputable def ft_equiv (n m : ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m)  := by
  apply Fintype.equivOfCardEq 
  rw [ card_fin_sum_fin ]
  rw [ Fintype.card_fin (n+m) ]


-- note that the result that permits the proof of the lemma
-- `card_fin_sum_fin` is this:

-- theorem Fintype.card_sum {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] :
--   card (α ⊕ β) = card α + card β



-- in addition to the lemma, the main tool is `Fintype.equivOfCardEq` which states


-- noncomputable def Fintype.equivOfCardEq {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] 
--   (h : card α = card β) :
--   α ≃ β


#check Fintype.equivOfCardEq

-- we've also used `Fintype.card_fin` which is the statement

-- Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n

#check Fintype.card_fin

-- but we can't compute with the term `ft_equiv`:  these evals throw errors...

-- #eval (ft_equiv 10 10).toFun (Sum.inl 0) 

-- #eval (ft_equiv 10 10).toFun (Sum.inr 0) 


--------------------------------------------------------------------------------
-- II. proof via `FinEnum`

-- `FinEnum` "keeps track" of equivalences. More precisely, if

-- `(X : Type) [FinEnum X]` and if the cardinality of X is n, then the
-- typeclass instance gives a specified(!) equivalence of types `X ≃
-- Fin n`.

-- there is automatically a `FinEnum` instance of the `Sum` of two
-- types with `FinEnum` instances. e.g.

example (n m :ℕ) : FinEnum ((Fin n) ⊕ (Fin m)) := inferInstance

-- here is how to get the cardinality from the FinEnum instance
example (X:Type) [FinEnum X] : ℕ := FinEnum.card X

-- and here is how to get the corresponding equivalence
example (X:Type) [FinEnum X] (n:ℕ) (h:n = FinEnum.card X) : X ≃ Fin n := by
  rw [h]
  exact FinEnum.equiv

-- with `FinEnum`, we don't have the "noncomputable" restriction on
-- the equivalence:
 
def fe_equi (n m : ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m)  := by
   rw [← card_fin_sum_fin ]
   rw [← FinEnum.card_eq_fintypeCard ]
   exact FinEnum.equiv
    
-- For numerical examples, we can now see what choices Lean made in
-- defining this equivalence!  for example:

#eval (fe_equi 5 7).toFun (Sum.inl 0) -- (0:Fin 12)
#eval (fe_equi 5 7).toFun (Sum.inr 0) -- (5:Fin 12)
#eval (fe_equi 5 7).toFun (Sum.inr 6) -- (11:Fin 12)


-- on the other hand, it isn't currently clear to me how one would
-- prove the following (which I assume must be true?)

example (n m : ℕ) [NeZero n] [NeZero m] : 
  (fe_equi n m).toFun (Sum.inr (Fin.ofNat m 0)) = Fin.ofNat (n+m) n := by 
   sorry -- ???
  
