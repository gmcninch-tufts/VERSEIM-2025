
import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank


-- let's prove for an m×n matrix that rank + nullity = n.

noncomputable section

variable { k : Type } [Field k]

-- let's introduce the "standard" k  vector space

abbrev stdVS  (k:Type) [Field k] (n:ℕ) : Type := (Fin n → k)

-- we use `abbrev` so that Lean is (more likely to) automatically
-- unfolds the definition -- this really is mainly an abbreviation to
-- avoid extra typing 

example (n:ℕ) : Module k (stdVS k n) := inferInstance

-- let's write `sbv n` for the standard basis of `stdVS k n`.
  
abbrev sbv (n:ℕ) : Basis (Fin n) k (stdVS k n) := Pi.basisFun k (Fin n)

-- given an m × n matrix M, and using the standard bases, we get a
-- corresponding linear transformation

-- `stdVS n ---> stdVS m` using `Matrix.mulVecLin`

example {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) : stdVS k n →ₗ[k] stdVS k m := 
  M.mulVecLin

-- or use `Matrix.toLin (sbv n) (sbv m) M`, they amount to the same thing:

lemma mulVecLin_eq_toLin_sbv (M:Matrix (Fin m) (Fin n) k) : 
   M.mulVecLin = M.toLin (sbv n) (sbv m) := by
   rfl 

-- Now the null space of the matrix is precise the kernel of this
-- linear transformation.

-- and the nullity of M is just the dimension of this null space

-- we find this dimension via `finrank` so that it is a natural
-- number. We could have instead used `Module.rank` and then the
-- dimension would be represented as a `Cardinal`, which includes
-- infinite cardinals.

def Nullity (M:Matrix (Fin m) (Fin n) k) : ℕ :=
  let null_space : Submodule k (stdVS k n) := 
    LinearMap.ker M.mulVecLin 
  Module.finrank k null_space    

-- The rank of the matrix is precisely the dimension of the image of
-- the corresponding linear transformation. This is the dimension of
-- the "column space" -- i.e. the span of the columns of M, viewed as
-- vectors in `stdVS k m`.

-- lWe can compare `LinearMap.finrank` with `Matrix.rank`
   
-- the main point is that the column space of a matrix identifies with
-- the image of the corresponding linear map k^n → k^n.

@[simp]
lemma rank_eq_linmap_rank  {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) : 
   M.rank  = Module.finrank k (LinearMap.range M.mulVecLin)
   := by 
   unfold Matrix.rank 
   rw [ mulVecLin_eq_toLin_sbv M ]


-- --------------------------------------------------------------------------------
-- 
-- now the rank-nullity theory compares these numbers!

-- the main extra thing to know is this: the mapping

-- `φ_M : stdVS k n ---> stdVS k m` determined by M induces an invertible
-- linear mapping from the quotient space `stdVS k n ⧸ Null M` to the
-- image (in `stdVS k m`) of φ_M.

-- moreover, for any finite dimensional vector space `V` and any
-- subspace `W : Submodule k V` the quotient space `V ⧸ W` has dimension
-- `dim V ⧸ W = dim V - dim W`.

-- This means that the dimension of the image of φ is equal to 
-- `dim stdVS k n - Nullity M` -- i.e. `n - Nullity M` 


--  the invertible linear mapping between `stdVS k n ⧸ Null M` and the
--  image of `φ_M` follows from `LinearMap.quotKerEquivRange`

-- This amounts to the rank-nullity theorem!

example (l:ℕ) : Module.finrank k (Fin l → k) = l := by exact Module.finrank_fin_fun k

-- in the next proof, the real work is done by
-- `LinearMap.rank_range_add_rank_ker`

theorem rank_nullity (M:Matrix (Fin m) (Fin n) k) : 
  M.rank + Nullity M = n := by
  unfold Nullity
  rw [ rank_eq_linmap_rank ]
  rw [ LinearMap.finrank_range_add_finrank_ker M.mulVecLin ]
  simp

-- in the next proof, we use the quotient construction on vector
-- spaces and instead use `LinearMap.rank_quotient_add_rank`

theorem quotient_dim  ( V : Type )
  [ AddCommGroup V] [ Module k V] 
  (W : Submodule k V) [FiniteDimensional k V]
  : Module.rank k (V ⧸ W) + Module.rank k W = Module.rank k V  := by 
  apply Submodule.rank_quotient_add_rank

-- here we can give a proof of rank-nullity using the argument via the
-- quotient vector space described above

theorem rank_nullity' {m n : ℕ} (M:Matrix (Fin m) (Fin n) k) : 
  M.rank + Nullity M = n := by
  rw [ rank_eq_linmap_rank M] 
  let linmap : stdVS k n →ₗ[k] stdVS k m := M.mulVecLin
  unfold Nullity
  have linear_equiv : LinearMap.range linmap 
                ≃ₗ[k] (stdVS k n) ⧸ (LinearMap.ker linmap) := 
    (LinearMap.quotKerEquivRange linmap).symm  
  have dim_eq : Module.rank k ↥(LinearMap.range linmap) = 
                Module.rank k (stdVS k n ⧸ LinearMap.ker linmap) := 
    LinearEquiv.rank_eq linear_equiv
  simp
  rw [  LinearMap.finrank_range_add_finrank_ker linmap  ]
  exact Module.finrank_fin_fun k

--------------------------------------------------------------------------------
-- Finally, let's relate the non-vanishing of `M.det` to the rank of the
-- matrix `M`.

-- the "invertible matrix theorem" results which give the main results over fields are

-- `LinearMap.isUnit_iff_range_eq_top` and
-- `LinearMap.isUnit_iff_ker_eq_bot`

-- for example, we have (for finite dimensional V) that a linear map
-- `f:V → V` is invertible ↔ `ker f = ⊥`

example (n :ℕ) (f:stdVS k n →ₗ[k] stdVS k n)  (finv : LinearMap.ker f = ⊥) :
    IsUnit f := by exact (LinearMap.isUnit_iff_ker_eq_bot f).mpr finv


-- note that the determinant of a linear map is the same as that of
-- the corresponding matrix. 

example  (n:ℕ) (M:Matrix (Fin n) (Fin n) k) : (M.toLin (sbv n) (sbv n)).det = M.det := by 
  apply LinearMap.det_toLin (sbv n) M


theorem matrix_fullrank_iff_det_ne_zero (n:ℕ) (M:Matrix (Fin n) (Fin n) k) 
  : M.det ≠ 0 ↔ M.rank = n := by
  constructor

  · -- the mp direction
    intro hdet
    have im : IsUnit M := by 
      apply (Matrix.isUnit_iff_isUnit_det M).mpr
      simp
      exact hdet
    rw [ Matrix.rank_of_isUnit M im ]
    simp

  · -- the mpr direction 
    intro h
    rw [ ←LinearMap.det_toLin (sbv n) M ]
    rw [ ←mulVecLin_eq_toLin_sbv M ]

    rw [ rank_eq_linmap_rank M ] at h

    simp only [ ← Module.finrank_fin_fun (n := n) k ] at h

    have onto : LinearMap.range M.mulVecLin = ⊤ := 
       Submodule.eq_top_of_finrank_eq h
      
    have unit : IsUnit M.mulVecLin :=  by
      refine (LinearMap.isUnit_iff_range_eq_top M.mulVecLin).mpr onto

    rw [ ← isUnit_iff_ne_zero ]
    
    exact LinearMap.isUnit_det M.mulVecLin unit


  





