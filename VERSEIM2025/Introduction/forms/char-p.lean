
import Mathlib.Tactic

--variable {p : ℕ} [Fact (Prime p)]

-- example : Field (ZMod p) := inferInstance

-- -- for shorthand, we can write k for this field
-- def kₚ  : Type := ZMod p 

-- instance : Field (@kₚ p) := by
--   unfold kₚ
--   exact inferInstance 


-- the next lemma says that for a vector space over a field k of
-- characteristic different from 2, for v in V the equation `2v=0`
-- implies that `v=0`.

lemma eq_zero_of_two_mul_eq_zero { k V : Type } [ Field k] [ AddCommGroup V] 
  [Module k V] {p:ℕ} [CharP k p] (hn2 : p ≠ 2) 
  (v:V) (h:2•v = 0) : v = 0 := by
    have two_smul_eq_zero : (2:k) • v = 0 := by 
      rw [ ofNat_smul_eq_nsmul k 2 v ]
      assumption
    have ring_char_n2 : ringChar k ≠ 2 := by 
       rw [ ringChar.eq k p ] 
       assumption
    have two_neq_zero : (2:k) ≠ 0 := by
       apply Ring.two_ne_zero ring_char_n2
    by_contra v_neq_zero
    have two_smul_ne_zero : (↑2:k) • v ≠ 0 := 
       smul_ne_zero two_neq_zero v_neq_zero
    exact two_smul_ne_zero two_smul_eq_zero 
   
