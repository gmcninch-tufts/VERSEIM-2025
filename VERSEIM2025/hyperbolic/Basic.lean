import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Properties

variable {k V : Type} [Field k] [AddCommGroup V]
         [Module k V]

open Module          
open LinearMap
open LinearMap (BilinForm)


/-- For a vector space `V`, and a constant `ε:k`, return the hyperbolic bilinear
form `β` on the space `V × (V →ₗ[k] k)` given by the rule
`β (v,φ) (v',φ') = (φ v') + ε * (φ' v)`
-/
@[simp]
def HyperbolicForm (k V :Type) [Field k] [AddCommGroup V] [Module k V] (ε : k)
  : BilinForm k (V × (V →ₗ[k] k)) :=
  let lin_form (v:V) (φ:V →ₗ[k] k) (ε:k) : V × (V →ₗ[k] k) →ₗ[k] k :=
      { toFun := fun ⟨v',φ'⟩ => (φ v') + ε * (φ' v) 
        map_add' := fun ⟨v',φ'⟩ ⟨ v'',φ''⟩ => by 
          simp only [map_add, add_apply]; ring
        map_smul' := fun t ⟨v',φ'⟩ =>  by 
          simp only [map_smul, smul_eq_mul, smul_apply, RingHom.id_apply]; ring 
      } 
  { toFun := fun ⟨v, φ⟩  => lin_form v φ ε 
    map_add' := fun ⟨v,φ⟩ ⟨v₁,φ₁⟩ => by
      unfold lin_form 
      simp only [add_apply, map_add]
      apply LinearMap.ext
      intro ⟨v',φ'⟩
      simp; ring
    map_smul' := fun t ⟨v',φ'⟩ => by
      unfold lin_form
      simp only [smul_apply, smul_eq_mul, map_smul, RingHom.id_apply]
      apply LinearMap.ext
      intro ⟨v',φ'⟩ 
      simp; ring
  }

/-- The `HyperbolicForm` on `(V × (V →ₗ[k] k))` is symmetric when `ε=1`.
-/
theorem hyperbolic_is_symm_of_1 (k V :Type) [Field k] [AddCommGroup V] [Module k V] :
  (HyperbolicForm k V 1).IsSymm := by
  rw [ BilinForm.isSymm_def ]
  intro ⟨v,φ⟩ ⟨v₁,φ₁⟩
  simp only [HyperbolicForm, one_mul, coe_mk, AddHom.coe_mk] 
  ring

/-- The `HyperbolicForm` on `(V × (V →ₗ[k] k))` is alternating when `ε=-1`.
-/
theorem hyperbolic_is_alt_of_minus1 (k V :Type) [Field k] [AddCommGroup V] [Module k V] :
  (HyperbolicForm k V (-1:k)).IsAlt := by
  intro ⟨v,φ⟩ 
  simp only [HyperbolicForm, coe_mk, AddHom.coe_mk] 
  ring

lemma exists_functional_nezero_on_nezero (v:V) (hv : v ≠ 0) :
  ∃ ψ:V →ₗ[k] k, ψ v ≠ 0 := by
  rcases (Module.Basis.exists_basis k V) with ⟨ι,hb⟩
  let b : Module.Basis ι k V := Classical.choice hb
  have : b.repr v ≠ 0 := by aesop
  let functional (i:ι) : (ι →₀ k) →ₗ[k] k := {
    toFun := fun f => f i
    map_add' := by simp
    map_smul' := by simp
    }
  have : ∃ i, (b.repr v) i ≠ 0 := Finsupp.ne_iff.mp this
  rcases this with ⟨i,hi⟩
  use (functional i) ∘ₗ b.repr
  unfold functional; simp; assumption
 
/-- If `ε≠0`, given a non-zero vector `x` in `V × (V →ₗ[k] k)`, there
is a vector `y` in `V × (V →ₗ[k] k)` for which 
`HyperbolicForm k V ε x y ≠ 0` 
-/
lemma non_zero_pair (x : V × (V →ₗ[k] k)) (ε:k) (hε:ε≠ 0) (h:x ≠ 0) :
  ∃ y, (HyperbolicForm k V ε) x y ≠ 0 := by 
  rcases x with ⟨v,φ⟩
  by_cases hv : v = 0
  case pos => 
    have : φ ≠ 0 := by aesop
    have : ∃w, φ w ≠ 0 := by
      by_contra hw
      push_neg at hw
      have hφ : φ = 0 := LinearMap.ext hw
      apply this hφ
    rcases this with ⟨w,hw⟩
    use ⟨w,0⟩
    simp; assumption
  case neg =>
    have := (Module.forall_dual_apply_eq_zero_iff k v).mp
    have : ∃ψ:V →ₗ[k] k, ψ v ≠ 0 := by
      by_contra hψv
      push_neg at hψv
      have hvz : v = 0 := this hψv 
      apply hv hvz 
    rcases this with ⟨ψ,hψ⟩
    use ⟨0,ψ⟩
    simp
    exact ⟨hε,hψ⟩
          
/-- If `ε ≠ 0`, the `HyperbolicForm k V ε` on `(V × (V →ₗ[k] k))` is non-degenerate.
-/
theorem hyperbolic_is_nondeg (k V :Type) [Field k] [AddCommGroup V] 
  [Module k V] (ε:k) (hε:ε≠0):
  (HyperbolicForm k V ε).Nondegenerate := by
  intro ⟨v,φ⟩ h
  by_contra l
  have : ∃y, (HyperbolicForm k V ε) ⟨v,φ⟩ y ≠ 0 := non_zero_pair ⟨v,φ⟩ ε hε l
  rcases this with ⟨y,hy⟩
  exact hy (h y)
  


/-- A hyperbolic basis of a vector space `V` with a bilinear form `β` is a basis `b`
indexed by a type `ι ⊕ ι` with the properties 
- `β (b (Sum.inl i)) (b (Sum.inl j)) = 0` for every `i j`
- `β (b (Sum.inr i)) (b (Sum.inr j)) = 0` for every `i j`
- `β (b (Sum.inl i)) (b (Sum.inr j)) = ε * δ_{i,j}` for every `i j`
- `β (b (Sum.inl i)) (b (Sum.inr j)) = δ_{i,j}` for every `i j`
-/
structure HyperbolicBasis (k W :Type) [Field k] [AddCommGroup W] [Module k W] 
  (ε : k)  (β:BilinForm k W) (ι:Type) [DecidableEq ι] where
  carrier : Basis (ι ⊕ ι) k W
  cond_ll : ∀ i j, β (carrier (Sum.inl i)) (carrier (Sum.inl j)) = 0
  cond_rr : ∀ i j, β (carrier (Sum.inr i)) (carrier (Sum.inr j)) = 0
  cond_lr : ∀ i j, β (carrier (Sum.inl i)) (carrier (Sum.inr j)) = if i=j then ε else 0
  cond_rl : ∀ i j, β (carrier (Sum.inr i)) (carrier (Sum.inl j)) = if j=i then 1 else 0


/-- Construction of a hyperbolic basis for `V × (V →ₗ[k] k)` equipped
with `HyperbolicForm k V ε`.
-/
noncomputable
def HyyperbolicBasisOfHyperbolicForm (ε:k)
   (ι:Type) [Finite ι] [DecidableEq ι] (b:Basis ι k V):
  HyperbolicBasis k (V × (V →ₗ[k] k)) ε (HyperbolicForm k V ε) ι where
    carrier := Basis.prod b (Basis.dualBasis b)
    cond_ll := by simp
    cond_rr := by simp
    cond_lr := by aesop
    cond_rl := by aesop


