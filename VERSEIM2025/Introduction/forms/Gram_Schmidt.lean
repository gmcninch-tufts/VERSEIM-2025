import Mathlib.Tactic

/- This replicates much of the material in Mathlib and was done for learning purposes. -/

def Def {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, x ≠ 0 → β x x ≠ 0

def PosDef {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x, (β x x ≥ 0 ∧ (x ≠ 0 → β x x > 0))

def Symm {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x y, β x y = β y x

lemma posDef_is_Def {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h: PosDef β) : Def β := by
  intro x hx
  suffices β x x > 0 from ?_
  . linarith
  apply (h x).right
  assumption


def OrthogPred {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c: I → V) : Prop := ∀ (i j : I), i ≠ j → β (c i) (c j) = 0

def NonzeroVectors [AddCommGroup V] (c:I → V) : Prop := ∀ i, (c i ≠ 0)


def OrthogBasis {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:Basis I ℝ V) : Prop := OrthogPred β c

def UnitVectors {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:I → V) : Prop := ∀ i, β (c i) (c i) = 1

def OrthonormalPred {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:I → V) : Prop := OrthogPred β c ∧ UnitVectors β c

@[simp]
def restrict {X:Type} {m:ℕ} (f:Fin (m+1) → X) : Fin m → X :=
  fun i => f i.castSucc

theorem restrict_set_eq {X: Type} {m: ℕ} (f: Fin (m+1) → X) :
  f '' (Set.range (@Fin.castSucc m)) = Set.range (restrict f)
  := by
    simp
    ext x
    constructor
    . rintro ⟨y, ⟨hy, rfl⟩⟩
      simp at *
      have: ↑y ≠ m := by exact Nat.ne_of_lt hy
      have: y ≠ Fin.last m := by exact Ne.symm (Fin.ne_of_val_ne (id (Ne.symm this)))
      use y.castPred this
      simp
    . rintro ⟨y, rfl⟩
      simp
      use y.castSucc
      simp


noncomputable def proj {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v: V) : V :=
  (β v u / β u u) • u

lemma proj_contained {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v: V)
 : proj β u v ∈ Submodule.span ℝ {u} := by
    refine Submodule.mem_span_singleton.mpr ?_
    exact exists_apply_eq_apply (fun a ↦ a • u) ((β v) u / (β u) u)

lemma proj_contained' {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v: V) (W: Submodule ℝ V) (h: u ∈ W)
 : proj β u v ∈ W := by
    have: proj β u v ∈ Submodule.span ℝ {u} := proj_contained β u v
    have cont: Submodule.span ℝ {u} ≤ W := by exact
      (Submodule.span_singleton_le_iff_mem u W).mpr h
    exact cont this

lemma proj_nice  {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v w: V)
  (h: β u v = 0): β u (proj β v w) = 0 := by
    unfold proj
    simp[h]

lemma proj_nice'  {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v: V)
  (h': β u u ≠ 0): β u (proj β u v) = β v u := by
    unfold proj
    field_simp

example {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n: ℕ} (b: Fin n → V) (v: V):
  β v (∑ i, b i)= ∑ i, β v (b i) := by
    exact LinearMap.BilinForm.sum_right β Finset.univ v b

lemma not_needed_sum_one_nonzero_element {n: ℕ} (l: Fin n → ℝ) (i: Fin n) (h: (j: Fin n) → j ≠ i → l j =0):
  l i = ∑ j, l j := by exact Eq.symm (Fintype.sum_eq_single i h)

lemma restrict_linear_independent {V:Type} [AddCommGroup V] [Module ℝ V]
  {n:ℕ}  (b:Fin (n+1) → V) (hb : LinearIndependent ℝ b) : LinearIndependent ℝ (restrict b) := by
    unfold restrict
    apply LinearIndependent.comp hb Fin.castSucc
    exact Fin.castSucc_injective n

@[simp]

noncomputable def sub_perp_align {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n:ℕ} (b:Fin n → V) (x: V): V := x - ∑ i, proj β (b i) (x)

noncomputable def intermediate {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)  {n:ℕ} (b:Fin n → V) (x: V): Fin (n+1) → V :=
    fun i  =>
      if h' : i ≠ Fin.last n then b (i.castPred h')
        else (sub_perp_align β b x)

@[simp]
lemma intermediate_val₁ {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n:ℕ} (b:Fin n → V) (i: Fin n) (x: V): intermediate β b x (i.castSucc) = b i:= by
    simp[intermediate]


@[simp]
lemma intermediate_val₂ {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n:ℕ} (b:Fin n → V) (i: Fin (n+1)) (h: i ≠ Fin.last n) (x: V): intermediate β b x i =
    b (i.castPred h) := by
      have: ↑i ≠ n := by
        refine Nat.ne_of_lt ?_
        exact Fin.val_lt_last h
      have: ¬(↑i = n) := by exact this
      simp_all[intermediate]

@[simp]
lemma intermediate_val₃ {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n:ℕ} (b:Fin n → V) (x: V) : intermediate β b x (Fin.last n) = sub_perp_align β b x := by
    simp[intermediate]

def span_stuff {V:Type} [AddCommGroup V] [Module ℝ V] (b: Fin n → V): Submodule ℝ V :=
  Submodule.span ℝ (Set.range b)

@[simp]
lemma intermediate_span_contained {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)  {n:ℕ} (b:Fin n → V) (x: V): span_stuff b ≤ span_stuff (intermediate β b x) := by
    simp only [span_stuff]
    suffices: Set.range b ≤ Submodule.span ℝ (Set.range (intermediate β b x))
    . exact Submodule.span_le.mpr this
    rintro _ ⟨y, rfl⟩
    suffices b y ∈ Set.range (intermediate β b x)from ?_
    . have h': Set.range (intermediate β b x) ⊆
      ↑(Submodule.span ℝ (Set.range (intermediate β b x))) := by
        exact Submodule.subset_span
      exact h' this
    use y.castSucc
    simp

@[simp]
lemma intermediate_contained {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)  {n:ℕ} (b:Fin n → V) (x: V): x ∈ Submodule.span ℝ
  (Set.range (intermediate β b x)) := by
    let y := x - ∑ i, proj β (b i) (x)
    have hy: y ∈ Submodule.span ℝ (Set.range (intermediate β b x)) := by
      suffices  y ∈ Set.range (intermediate β b x) from ?_
      . exact Submodule.mem_span.mpr fun p a ↦ a this
      use Fin.last n
      show intermediate β b x (Fin.last n) = x - ∑ i, proj β (b i) (x)
      simp
    have hxy: x = y+∑ i, proj β (b i) x :=
      Eq.symm (sub_add_cancel x (∑ i, proj β (b i) x))
    nth_rewrite 2[hxy]
    apply add_mem
    . exact hy
    . suffices ∀ i, proj β (b i) x ∈ Submodule.span ℝ (Set.range (intermediate β b x)) from ?_
      . exact Submodule.sum_mem (Submodule.span ℝ (Set.range (intermediate β b x))) fun c a ↦ this c
      intro i
      suffices (b i) ∈ Submodule.span ℝ (Set.range (intermediate β b x)) from ?_
      . exact proj_contained' β (b i) x (Submodule.span ℝ (Set.range (intermediate β b x))) this
      suffices b i ∈ Set.range (intermediate β b x) from ?_
      . exact Submodule.mem_span.mpr fun p a ↦ a this
      use i.castSucc
      simp


theorem orthog_sub_perp_align {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin n → V) (hb: OrthogPred β b) (x: V): (i: Fin n) → β (b i) (sub_perp_align β b x) =0 := by
    intro i
    unfold sub_perp_align
    rw[map_sub]
    suffices β (b i) (x) = β (b i) (∑ j, proj β (b j) x) from ?_
    . rw[this, sub_self]

    rw[LinearMap.BilinForm.sum_right]
    show (β (b i)) (x)=∑ j, (β (b i)) (proj β (b j) x)

    have orthog_i_j (j: Fin n): (j ≠ i) → (β (b i)) (proj β (b j) x)=0 := by
      intro h
      apply proj_nice
      apply hb
      tauto
    rw[Fintype.sum_eq_single i orthog_i_j]
    rcases Classical.em ( b i =0 ) with h | h
    . rw[h]
      simp
    rw[proj_nice' β _ _ ((hp) (b i) h)]
    apply hs


theorem orthog_intermediate {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin n → V) (hb: OrthogPred β b) (x: V): OrthogPred β (intermediate β b x) := by
    have case1 (i j: Fin (n+1)) (h: i ≠ j): (h₁: i=Fin.last n) → (β (intermediate β b x i)) (intermediate β b x j) = 0 := by
      intro h₁
      rw[h₁]
      have h₂: j ≠ Fin.last n :=
        Ne.symm (Lean.Grind.ne_of_ne_of_eq_left (id (Eq.symm h₁)) h)
      have h₃: (intermediate β b x) (Fin.last n) = sub_perp_align β b x := by simp
      rw[h₃]
      rw[hs]
      have: intermediate β b x j = b (j.castPred h₂) := intermediate_val₂ β b j h₂ x
      rw[this]
      exact orthog_sub_perp_align β hp hs b hb x (j.castPred h₂)
    have case2 (i j: Fin (n+1)) (h: i ≠ j): (i≠ Fin.last n) → (j ≠ Fin.last n) → (β (intermediate β b x i)) (intermediate β b x j) = 0 := by
      intro h₁ h₂
      have h1: intermediate β b x i = b (i.castPred h₁) := intermediate_val₂ β b i h₁ x
      have h2: intermediate β b x j = b (j.castPred h₂) := intermediate_val₂ β b j h₂ x
      rw[h1, h2]
      apply hb
      intro h'
      simp_all
    intro i j h
    rcases Classical.em (i=Fin.last n) with h₁ | h₁
    . exact case1 i j h h₁
    rcases Classical.em (j=Fin.last n) with h₂ | h₂
    . rw[hs]
      exact case1 j i h.symm h₂
    . exact case2 i j h h₁ h₂


@[simp]
noncomputable def gram_schmidt {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin n → V)
  : Fin n → V := match n with
   | Nat.zero =>  (fun _ ↦ 0)
   | Nat.succ n =>
    let b' := restrict b
    let c' := gram_schmidt β hp hs b'
    intermediate β c' (b (Fin.last n))

@[simp]
theorem gram_schmidt_agree_succ {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin (n+1) → V) : (i: Fin n) →
    (gram_schmidt β hp hs b i.castSucc)=gram_schmidt β hp hs (restrict b) i := by
      intro i
      simp

@[simp]
theorem gram_schmidt_agree_pred {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin (n+1) → V) : (i: Fin (n+1)) → (hi: i ≠ Fin.last n) →
    (gram_schmidt β hp hs b i)=gram_schmidt β hp hs (restrict b) (i.castPred hi) := by
      intro i hi
      let j := i.castPred hi
      show gram_schmidt β hp hs b (j.castSucc) = gram_schmidt β hp hs (restrict b) j
      simp


theorem orthog_span_gram_schmidt {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin n → V)
  : OrthogPred β (gram_schmidt β hp hs b):=
  match n with
  | Nat.zero => by
    intro i j h
    have: ↑i<(0: ℕ) := by exact i.isLt
    linarith
  | Nat.succ n => by
    let c := gram_schmidt β hp hs b
    let c' := gram_schmidt β hp hs (restrict b)

    let x := b (Fin.last n)

    have h: c = intermediate β c' x := rfl

    have orthog: OrthogPred β c := by
      show OrthogPred β (intermediate β c' x)
      exact orthog_intermediate β hp hs c' (orthog_span_gram_schmidt β hp hs (restrict b)) x
    exact orthog

@[simp]
lemma span_stuff_restrict_contained {V:Type} [AddCommGroup V] [Module ℝ V] (b: Fin (n+1) → V): span_stuff (restrict b) ≤ span_stuff b := by
  show Submodule.span ℝ (Set.range (restrict b)) ≤ Submodule.span ℝ (Set.range b)
  suffices Set.range (restrict b) ⊆ Set.range (b) from Submodule.span_mono this
  rintro _ ⟨y, rfl⟩
  use y.castSucc
  simp[restrict]

theorem span_eq_gram_schmidt {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin n → V): span_stuff (gram_schmidt β hp hs b) = span_stuff b :=
  match n with
  | Nat.zero => by
    have h₁: Submodule.span ℝ (Set.range b)=⊥ := by
      rw [Set.range_eq_empty, Submodule.span_empty]
    have h₂: Submodule.span ℝ (Set.range (gram_schmidt β hp hs b))=⊥ := by
      rw [Set.range_eq_empty, Submodule.span_empty]
    simp[span_stuff]
  | Nat.succ n => by
    have h_lower_case: span_stuff (gram_schmidt β hp hs (restrict b)) = span_stuff (restrict b) := span_eq_gram_schmidt β hp hs (restrict b)
    simp only [span_stuff, gram_schmidt] at *

    refine Submodule.span_eq_span ?_ ?_
    . rintro _ ⟨y, rfl⟩
      rcases Classical.em (y=Fin.last n) with h | h
      . rw[h]
        suffices sub_perp_align β (gram_schmidt β hp hs (restrict b)) (b (Fin.last n)) ∈ ↑(Submodule.span ℝ (Set.range b))
          from ?_
        . have: intermediate β (gram_schmidt β hp hs (restrict b)) (b (Fin.last n)) (Fin.last n)
             = sub_perp_align β (gram_schmidt β hp hs (restrict b)) (b (Fin.last n)) := by
              simp [intermediate]
          (expose_names; exact Set.mem_of_eq_of_mem this this_1)
        simp only [sub_perp_align]
        apply sub_mem
        . have: b (Fin.last n) ∈ Set.range b := by exact Set.mem_range_self (Fin.last n)
          exact Submodule.mem_span.mpr fun p a ↦ a this
        have: (i: Fin n) → proj β (gram_schmidt β hp hs (restrict b) i) (b (Fin.last n))
          ∈ Submodule.span ℝ (Set.range b) := by
          intro i
          suffices h: proj β (gram_schmidt β hp hs (restrict b) i) (b (Fin.last n))
          ∈ Submodule.span ℝ (Set.range (restrict b)) from ?_
          . have: Submodule.span ℝ (Set.range (restrict b)) ≤ Submodule.span ℝ (Set.range b) := by
              exact span_stuff_restrict_contained b
            exact this h
          apply proj_contained'
          rw[<- h_lower_case]
          suffices gram_schmidt β hp hs (restrict b) i ∈ Set.range (gram_schmidt β hp hs (restrict b)) from ?_
          . exact Submodule.mem_span.mpr fun p a ↦ a this
          exact Set.mem_range_self i

        exact Submodule.sum_mem (Submodule.span ℝ (Set.range b)) fun c a ↦ this c

      . have h: y ≠ Fin.last n := h
        apply span_stuff_restrict_contained b
        simp only [span_stuff]
        rw[<- h_lower_case]

        have: intermediate β (gram_schmidt β hp hs (restrict b)) (b (Fin.last n)) y
          = (gram_schmidt β hp hs (restrict b)) (y.castPred h) :=
            intermediate_val₂ β (gram_schmidt β hp hs (restrict b)) y h (b (Fin.last n))
        rw[this]
        suffices gram_schmidt β hp hs (restrict b) (y.castPred h) ∈
           Set.range (gram_schmidt β hp hs (restrict b)) from ?_
        . exact Submodule.mem_span.mpr fun p a ↦ a this
        exact Set.mem_range_self (y.castPred h)

    . rintro _ ⟨y, rfl⟩
      rcases Classical.em (y=Fin.last n) with h | h
      . rw[h]
        simp
      . have: b y ∈ Submodule.span ℝ (Set.range (restrict b)) := by
          suffices b y ∈ Set.range (restrict b) from ?_
          . exact Submodule.mem_span.mpr fun p a ↦ a this
          use y.castPred h
          simp
        have: b y ∈ Submodule.span ℝ (Set.range (gram_schmidt β hp hs (restrict b))) := by
          rw[h_lower_case]
          exact this
        have containment: Submodule.span ℝ (Set.range (gram_schmidt β hp hs (restrict b)))
          ≤ (Submodule.span ℝ (Set.range (intermediate β (gram_schmidt β hp hs (restrict b)) (b (Fin.last n))))) :=
            intermediate_span_contained β (gram_schmidt β hp hs (restrict b)) (b (Fin.last n))
        exact containment this

lemma linear_independence_equiv_condition_fin {V:Type} [AddCommGroup V] [Module ℝ V] {n: ℕ} (b: Fin n → V)
 (h: ∀(l: Fin n → ℝ), ∑ i, (l i) • (b i)=0 → l=0): LinearIndependent ℝ b := by
    exact Fintype.linearIndependent_iff.mpr fun g a ↦ congrFun (h g a)


theorem linear_independence_orthog_nonzero {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β)
  {n:ℕ} (b:Fin n → V) (h_orthog: OrthogPred β b) (h_nonzero: NonzeroVectors b): LinearIndependent ℝ b := by
    apply linear_independence_equiv_condition_fin
    intro l h
    suffices (j: Fin n) → l j = 0 from ?_
    . exact (Set.eqOn_univ l 0).mp fun ⦃x⦄ a ↦ this x
    intro i
    have: β (∑ i, l i • b i) (b i) = l i * (β (b i)) (b i)  := by
      simp
      refine Fintype.sum_eq_single i ?_
      exact fun x a ↦ mul_eq_zero_of_right (l x) (h_orthog x i a)
    have nonzerostuff: β (b i) (b i) ≠ 0 := by
      have: b i ≠ 0 := h_nonzero i
      apply hp
      assumption
    simp[h, nonzerostuff] at this
    assumption

example {V: Type} [AddCommGroup V] (n: ℕ) (v: Fin n → V) [Module ℝ V] (W: Submodule ℝ V) (h: ∀i, v i ∈ W) : ∑ i, v i ∈ W := by
  exact Submodule.sum_mem W fun c a ↦ h c


lemma linear_independence_mem {V:Type} [AddCommGroup V] [Module ℝ V] (b: Fin (n+1) → V) (hb: LinearIndependent ℝ b) :
  ¬ (b (Fin.last n))∈ Submodule.span ℝ (Set.range (restrict b)) := by
    rw[<- restrict_set_eq]
    refine LinearIndependent.notMem_span_image hb ?_
    rintro ⟨y, h⟩
    simp_all

theorem non_zero_gram_schmidt {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b:Fin n → V) (hb: LinearIndependent ℝ b): NonzeroVectors (gram_schmidt β hp hs b) := by
    induction n with
    | zero =>
      intro i
      have: ↑i<(0: ℕ) := by exact i.isLt
      linarith
    | succ n h =>
      intro i
      rcases Classical.em (i =Fin.last n ) with h' | h'
      . rw[h']
        simp
        intro h''
        have h'': b (Fin.last n) =  ∑ i, proj β (gram_schmidt β hp hs (restrict b) i) (b (Fin.last n)) := by
          exact sub_eq_zero.mp h''
        let x := b (Fin.last n)
        have: (b (Fin.last n)) ∈ Submodule.span ℝ (Set.range (gram_schmidt β hp hs (restrict b))) := by
          rw[h'']
          suffices ∀i, proj β (gram_schmidt β hp hs (restrict b) i) (b (Fin.last n)) ∈
            Submodule.span ℝ (Set.range (gram_schmidt β hp hs (restrict b))) from ?_
          . exact
            Submodule.sum_mem (Submodule.span ℝ (Set.range (gram_schmidt β hp hs (restrict b))))
              fun c a ↦ this c
          intro i

          let c := gram_schmidt β hp hs (restrict b)
          let x := (b (Fin.last n))
          show proj β (c i) x ∈ Submodule.span ℝ (Set.range c)
          apply proj_contained'
          suffices c i ∈ Set.range c from ?_
          . exact Submodule.mem_span.mpr fun p a ↦ a this
          exact Set.mem_range_self i
        have: b (Fin.last n) ∈ span_stuff (gram_schmidt β hp hs (restrict b)) := this
        rw[span_eq_gram_schmidt β hp hs (restrict b)] at this
        exact (linear_independence_mem b hb) this
      . have low_lin_ind : LinearIndependent ℝ (restrict b) := restrict_linear_independent b hb
        have := h (restrict b) low_lin_ind
        rw[gram_schmidt_agree_pred β hp hs b i h']
        apply this

theorem gram_schmidt_linear_independence {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b: Basis (Fin n) ℝ V) : LinearIndependent ℝ (gram_schmidt β hp hs b) := by
    apply linear_independence_orthog_nonzero β hp
    . exact orthog_span_gram_schmidt β hp hs ⇑b
    . refine non_zero_gram_schmidt β hp hs ⇑b ?_
      exact Basis.linearIndependent b

structure OrthogBasis' {V:Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp: Def β) (hs: Symm β) (n:ℕ) where
   basis : Basis (Fin n) ℝ V
   is_orthog : OrthogPred β basis

noncomputable def orthog_basis {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : Def β) (hs : Symm β)
  {n:ℕ} (b: Basis (Fin n) ℝ V): OrthogBasis' β hp hs n where
    basis := by
      let vect := gram_schmidt β hp hs b
      have is_spanning: ⊤ ≤ span_stuff (gram_schmidt β hp hs b) := by
        suffices ⊤ = span_stuff (gram_schmidt β hp hs b) from ?_
        . exact eq_top_iff.mp (id (Eq.symm this))
        have h1: span_stuff (gram_schmidt β hp hs b) = span_stuff b:=
          span_eq_gram_schmidt β hp hs b
        have h2: span_stuff b = ⊤ := by
          simp[span_stuff]
        simp_all
      have is_linearly_independent := gram_schmidt_linear_independence β hp hs b
      exact Basis.mk is_linearly_independent is_spanning

    is_orthog := by
      simp
      exact orthog_span_gram_schmidt β hp hs b
