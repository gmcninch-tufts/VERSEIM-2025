# Results/Contributions

See below for a list of the major results achieved during the REU. Many of the descriptions below say 'proved' in correspondence to how we think about things mathematically, however the actual results are often in the form of definitions. 

- [Forms](/VERSEIM2025/Forms)
  - [Hyperbolic](/VERSEIM2025/Forms/Hyperbolic) - Sahan
    - [Alternating](/VERSEIM2025/Forms/Hyperbolic/Alternating.lean)
      - Nondegenerate alternating bilinear forms are hyperbolic (`alternating_is_hyperbolic`), thus dimension 2n (`alternate_is_even_dimension`), and those which are of equal (finite) dimension are isomorphic (as bilinear form spaces)  (`alternate_iso`)
    - [Basics](/VERSEIM2025/Forms/Hyperbolic/Basics.lean): 
      - States definitions for Hyperbolic forms and theorems relating the different viewpoints of Hyperbolic spaces together. 
    - [Symmetric](/VERSEIM2025/Forms/Hyperbolic/Symmetric.lean)
      - Any nondegenerate symmetric bilinear form is the direct sum of a hyperbolic and anisotropic (definite) form
    - [TwoSpaceBasics](/VERSEIM2025/Forms/Hyperbolic/TwoSpaceBasics.lean)
      - Partially duplicates material (with some modifications) from [Basics](/VERSEIM2025/Forms/Hyperbolic/Basics.lean) for easier use in [CasselsPfister](/VERSEIM2025/Forms/RationalFunctionFields/CasselsPfister.lean)
  - [RationalFunctionFields](/VERSEIM2025/Forms/RationalFunctionFields)
    - [Basics](/VERSEIM2025/Forms/RationalFunctionFields/Basics.lean) - Sahan
      - Contains definitions and results about Quadratic forms, mostly those from `V -> F` extended to `F[X] -> V[X]` and `V(X) -> F(X)`, to state/prove results in [CasselsPfister](/VERSEIM2025/Forms/RationalFunctionFields/CasselsPfister.lean)
      - `QuadraticFormExtensionPolynomial`: `deg Q(v) = 2 * deg v` for `Q:V -> F` Anisotropic (note `v ∈ V[X]` and `Q(v) ∈ F[X]`)
      - `HyperplaneReflection `: Reflecting vectors across a fixed vector 
      - Various diagrams commute (e.g. `Q: V -> F` extended to `V(X) -> F(X)` agrees with `V[X] -> F[X]` on the common domain)
    - [CasselsPfister](/VERSEIM2025/Forms/RationalFunctionFields/CasselsPfister.lean) - Sahan
      - Proves Cassels-Pfister Theorem: The values taken by the extension of a quadratic map `φ: V → F` to `V(X) → F(X)` that are in `F[X]` are taken by the extension `V[X] → F[X]` as well. (See ["The Algebraic and Geometric Theory
of Quadratic Forms"](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf) Theorem 17.3)
    - [PolynomialModule](/VERSEIM2025/Forms/RationalFunctionFields/PolynomialModule.lean) - George
      - Proves an equivalence between two notions of `V[X]`, namely viewed as extension by scalars (a tensor product of `V` with `F[X]` over `F`) and viewed as formal polynomials with coefficients in `V` (e.g. functions `Nat -> V` with finite support)
    - [Results](/VERSEIM2025/Forms/RationalFunctionFields/Results.lean) - Sahan
      - Let `f ∈ F[X]` be a sum of `n` squares in `F(X)`. Then `f` is a sum of `n` squares in `F[X]`
  - [Reflexive](/VERSEIM2025/Forms/RationalFunctionFields)
    - [Alternating_or_Symmetric](/VERSEIM2025/Forms/Reflexive/Alternating_or_Symmetric.lean) - Katherine & Sahan
      - Proves any reflexive bilinear form is alternating or symmetric
    - [Radical](/VERSEIM2025/Forms/Reflexive/Radical.lean) - Sahan
      - Given a bilinear form `B: V x V -> F`, defines `rad(B)={v| B(v,w)=0 for all w} ` and a bilinear form on `V/rad(B)` which is nondegenerate and such that the obvious diagram commutes
  - [Bilinear](/VERSEIM2025/Forms/Bilinear.lean) - George, Sahan, Clea, Katherine
    - Proves various results about bilinear forms. Notably, `isCompl_orthogonal_of_restrict_nondegenerate` generalizes [`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/BilinearForm/Orthogonal.html#LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate) from Mathlib (drops the reflexivity requirement)
  - [BilinearIsomorphisms](/VERSEIM2025/Forms/BilinearIsomorphisms.lean) - Sahan
    - Proof (construction) that two spaces `(V,β)` `(V',β')` over `F` are isomorphic from a bijection of bases(really type equivalence) that commutes with the bilinear form (`EquivBilin_of_basis_equiv`)
  - [QuadraticNondegenerate](/VERSEIM2025/Forms/BilinearIsomorphisms.lean) - Sahan
    - Given a quadratic form `Q: V -> F` gives a new quadratic form `V/rad(Q) -> F` (`quotient_rad`) such that the obvious diagram commutes (`Q` agrees with the composition `V -> V/rad(Q) -> F`; `quotient_rad_apply`) and the new form is nondegenerate (viewed as a bilinear form; `quotient_rad_nondegenerate`) 
    - Proves the image of the forms are preserved and extension by scalars works nicely with the construction. 
- [PolynomialModuleDegree](/VERSEIM2025/PolynomialModuleDegree) - Sahan
  - [Definitions](/VERSEIM2025/PolynomialModuleDegree/Definitions.lean) and [Operations](/VERSEIM2025/PolynomialModuleDegree/Operations.lean) mostly achieve results over `V[X]` (the polynomial module) that are achieved for `R[X]` (the polynomial ring) in Mathlib. 
  - [Misc](/VERSEIM2025/PolynomialModuleDegree/Misc.lean) 
    - `V[X]` has no torsion elements over `F[X]`
    - You can perform division in `V[X]` from `F[X]`
- [form_equivalence](/VERSEIM2025/form_equivalence.lean) - Clea
  - Implements a notion of isomorphism of vector spaces with bilinear forms, and proves (defines) the natural structures associated to it being an equivalence relation
  - Proves that Anisotropic, nondegenerate, symmetric, alternating are preserved under isomorphism (`anisotropic_of_equiv `, `nondeg_of_equiv `, `symm_of_equiv`, `alt_of_equiv `) 
- [applications](/VERSEIM2025/applications.lean) - Katherine
  - Proves that the orthogonal complement of a subspace is nondegenerate, assuming the entire space and the original subspace are nondegenerate (`ortho_complement_nondeg`)
- [Subspaces](/VERSEIM2025/Subspaces.lean) - Katherine
  - Let `U` and `W` be subspaces with trivial intersection, and `u: I -> U` and `w: J -> W` be linearly independent. Then the disjoint union `I ⊔ J -> V` is linearly independent (`lin_indep_by_transverse_subspaces`)
  - Let `U` and `W` be subspaces with `V` the internal direct sum of `U` and `W` and `b: I -> U` and `c: J -> W` be bases. Then disjoint union of `b` and `c` is a basis for `V` (`basis_of_direct_sum`)

