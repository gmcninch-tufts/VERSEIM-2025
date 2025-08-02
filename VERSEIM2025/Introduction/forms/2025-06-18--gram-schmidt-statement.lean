import Mathlib.Tactic

-- for a finite dimensional ℝ-vector space V with a positive definite
-- bilinear form, the Gram-Schmidt process takes as input a (random)
-- basis of V and returns an orthogonal basis for V.

-- to capture the algorithmic nature of this, let's write a function that
-- produces the new candidate basis -- the return value of the function will be
-- a function `Fin n → V`.

-- we'll have to check that this function is `LinearIndepent` and
-- hence determines a basis, and then check that this basis satisfies
-- `OrthogBasis`

def PosDef {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, β x x ≥ 0 ∧ x ≠ 0 → β x x > 0

def OrthogBasis {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:Basis I ℝ V) : Prop := ∀ (i j : I), i ≠ j → β (c i) (c j) = 0

def orthog_by_gs {V:Type} [AddCommGroup V] [Module ℝ V] 
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : PosDef β)
  {m:ℕ}
  (b:Fin m → V) (hb : LinearIndependent ℝ b)
  : Fin m → V := match m with 
   | Nat.zero => b
   | Nat.succ m => by sorry


def restrict {X:Type} {m:ℕ} (f:Fin (m+1) → X) : Fin m → X :=
  fun i => f i.castSucc 

#eval restrict ![2,3,4,5,8]

def extend {X:Type} {m:ℕ} (f:Fin m → X) (x :X) : Fin (m+1) → X :=
  fun i =>
  if h:i ≠ Fin.last m then f (i.castPred h) else x

#eval extend ![1,1,1] 4

-- let's write a function which takes as argument
-- a vector-values function w and returns the function
-- whose value at i is `w i` minus the sum of all the `w j` for `j < i`.

-- we can write this "recursively" as follows:

def construct {V:Type} [AddCommGroup V] [Module ℚ V] {m:ℕ} (w:Fin (m+1) → V) 
  : Fin (m+1) → V :=  
  match m with
   | 0 => w
   | m+1 => extend (construct (restrict w)) (w (Fin.last (m+1)) - (∑ j : Fin (m+1), w j.castSucc))


def sbv (n:ℕ) : Fin n → Fin n → ℚ := by
  intro i
  exact Pi.single i (1:ℚ)


#eval construct (sbv 5)
