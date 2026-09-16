import Hurst.RieszCompactEnumeration
import Hurst.TensorONBCompleteness

/-!
# Complete orthonormal eigenfamily for the compact Riesz operator

Constructs the **complete orthonormal eigenfamily** of a compact symmetric kernel
operator — the last piece making the eigenvalue-energy identity
`hsNorm K² = ∑' i, κ i²` unconditional via
`Hurst.TensorONBCompleteness.hsNorm_sq_eq_tsum_eigenvalue_sq_of_orthonormal_complete`
(which consumes exactly `Orthonormal ℝ v`, `(span (range v))ᗮ = ⊥`, and the eigen
equations).

## Route

1. **Per nonzero eigenvalue**: the eigenspace is finite-dimensional (landed:
   `eigenspace_finite_riesz`), hence carries an `OrthonormalBasis`
   (mathlib `gramSchmidtOrthonormalBasis` at `ι = Fin (finrank W)`).
2. **Kernel part**: `ker T` is a closed subspace of the Hilbert space `L²`, hence a
   Hilbert space, hence carries a Hilbert basis (mathlib `exists_hilbertBasis`).
   *Zero*-eigenvalue vectors are necessarily included: the spectral theorem only gives
   `(⨆ μ, eigenspace T μ)ᗮ = ⊥`, and `eigenspace T 0 = ker T` — dropping the kernel
   would leave `ker T` inside the orthocomplement.  The kernel basis is spliced in
   through its dense span (a Hilbert basis of an infinite-dimensional space spans only
   densely algebraically; the orthogonality argument extends over the closure by
   continuity of the inner product).
3. **Splice**: index type `(μ : {x : ℝ // x ≠ 0}) × Fin (finrank (eigenspace T μ)) ⊕ w`
   (the `Fin 0` fibers are empty, so eigenvalues that are not attained contribute
   nothing).  Orthogonality across distinct eigenvalues is the elementary symmetric-
   operator computation `μ⟪x,y⟫ = ⟪Tx,y⟫ = ⟪x,Ty⟫ = ν⟪x,y⟫` (for the Riesz operator the
   symmetry is landed: `isSymmetric_TOp_rieszKernel`).
4. **Completeness**: every eigenspace is spanned (exactly for `μ ≠ 0`, densely for
   `μ = 0`) by the corresponding spliced family, so `x ⊥ range v` forces
   `x ∈ (⨆ μ, eigenspace T μ)ᗮ = ⊥`.

## Main results

* `eigenspace_inner_eq_zero` — distinct-eigenvalue eigenvectors of a symmetric
  operator are orthogonal.
* `exists_complete_eigenfamily_of_symmetric` — the general splicing theorem: a
  symmetric operator with finite-dimensional nonzero eigenspaces, closed kernel and
  the landed orthocomplement decomposition has a complete orthonormal eigenfamily.
* `exists_complete_eigenfamily` — Riesz instantiation, ending with the unconditional
  identity `hsNorm K_R² = ∑' i, κ i²` (composing with the landed Parseval equality).

Note: the landed decomposition `L² = closure(span(v))` (trivial orthocomplement)
*subsumes* the classical "L² = ⊕ eigenspaces ⊕ ker T" decomposition; since the kernel
basis is spliced in, `ker T ⊆ closure(span v)` as well.
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section

namespace HS

/-! ### A. General splicing lemmas -/

section General

variable {T : L2 →ₗ[ℝ] L2}

/-- **Distinct-eigenvalue orthogonality**: eigenvectors of a symmetric operator
belonging to eigenspaces with distinct eigenvalues are orthogonal. -/
theorem eigenspace_inner_eq_zero (hsym : T.IsSymmetric) {μ ν : ℝ} (hμν : μ ≠ ν)
    (x : Module.End.eigenspace T μ) (y : Module.End.eigenspace T ν) :
    inner ℝ (x : L2) (y : L2) = 0 := by
  have hx : T (x : L2) = μ • (x : L2) := Module.End.mem_eigenspace_iff.mp x.2
  have hy : T (y : L2) = ν • (y : L2) := Module.End.mem_eigenspace_iff.mp y.2
  have h1 : inner ℝ (T (x : L2)) (y : L2) = inner ℝ (x : L2) (T (y : L2)) :=
    hsym (x : L2) (y : L2)
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right] at h1
  have h2 : (μ - ν) * inner ℝ (x : L2) (y : L2) = 0 := by
    rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hμν
  · exact h

/-- An orthonormal family inside a submodule of `L²` stays orthonormal after
coercion to `L²`. -/
theorem orthonormal_coe_subtype {W : Submodule ℝ L2} {J : Type*} (b : J → ↥W)
    (hb : Orthonormal ℝ b) : Orthonormal ℝ (fun j : J => (b j : L2)) := by
  constructor
  · intro j
    rw [Submodule.norm_coe (b j)]
    exact hb.1 j
  · intro i j hij
    exact (Submodule.coe_inner W (b i) (b j)).symm.trans (hb.2 hij)

/-- `x` orthogonal to a spanning family of `W` is orthogonal to all of `W`
(exact span; no closedness needed). -/
theorem inner_eq_zero_of_orthogonal_span {W : Submodule ℝ L2} {J : Type*} (b : J → ↥W)
    (hspan : span ℝ (Set.range b) = ⊤)
    (x : L2) (hx : ∀ j : J, inner ℝ (b j : L2) x = 0) :
    ∀ y : ↥W, inner ℝ (y : L2) x = 0 := by
  intro y
  have hspan' : ∀ z ∈ span ℝ (Set.range b), inner ℝ (z : L2) x = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem u hu => obtain ⟨j, rfl⟩ := hu; exact hx j
    | zero => simp
    | add u v _ _ hu hv => rw [Submodule.coe_add, inner_add_left, hu, hv, add_zero]
    | smul c u _ hu => rw [Submodule.coe_smul, real_inner_smul_left, hu, mul_zero]
  exact hspan' y (hspan.ge (Submodule.mem_top : y ∈ (⊤ : Submodule ℝ ↥W)))

/-- `x` orthogonal to a densely spanning family of a closed submodule `W` is
orthogonal to all of `W` (extension over the closure by continuity). -/
theorem inner_eq_zero_of_orthogonal_span_dense {W : Submodule ℝ L2} {J : Type*} (b : J → ↥W)
    (hspan : ⊤ ≤ (span ℝ (Set.range b)).topologicalClosure)
    (x : L2) (hx : ∀ j : J, inner ℝ (b j : L2) x = 0) :
    ∀ y : ↥W, inner ℝ (y : L2) x = 0 := by
  classical
  have hcont : Continuous (fun z : ↥W => inner ℝ (z : L2) x) := by
    have h2 : (fun z : ↥W => inner ℝ (z : L2) x) = fun z : ↥W => inner ℝ x (z : L2) := by
      funext z
      exact real_inner_comm _ _
    rw [h2]
    exact ((innerSL ℝ x : L2 →L[ℝ] ℝ).comp W.subtypeL).continuous
  have hzero : ∀ z ∈ span ℝ (Set.range b), inner ℝ (z : L2) x = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem u hu => obtain ⟨j, rfl⟩ := hu; exact hx j
    | zero => simp
    | add u v _ _ hu hv => rw [Submodule.coe_add, inner_add_left, hu, hv, add_zero]
    | smul c u _ hu => rw [Submodule.coe_smul, real_inner_smul_left, hu, mul_zero]
  have hZclosed : IsClosed {z : ↥W | inner ℝ (z : L2) x = 0} :=
    IsClosed.preimage hcont isClosed_singleton
  have hsub : (span ℝ (Set.range b) : Set ↥W) ⊆ {z : ↥W | inner ℝ (z : L2) x = 0} :=
    fun z hz => hzero z hz
  have hclos : closure (↑(span ℝ (Set.range b)) : Set ↥W)
      ⊆ {z : ↥W | inner ℝ (z : L2) x = 0} :=
    closure_minimal hsub hZclosed
  intro y
  have hy : y ∈ (span ℝ (Set.range b)).topologicalClosure :=
    hspan (Submodule.mem_top : y ∈ (⊤ : Submodule ℝ ↥W))
  rw [show y ∈ (span ℝ (Set.range b)).topologicalClosure ↔
      y ∈ (((span ℝ (Set.range b)).topologicalClosure : Submodule ℝ ↥W) : Set ↥W) from Iff.rfl,
    Submodule.topologicalClosure_coe] at hy
  exact hclos hy

/-- A family spanning `W` inside itself spans the coerced image after the submodule
inclusion. -/
theorem span_range_subtype_le {W : Submodule ℝ L2} {J : Type*} (b : J → ↥W)
    (hspan : span ℝ (Set.range b) = ⊤) :
    W ≤ span ℝ (Set.range (fun j : J => (b j : L2))) := by
  have h1 : (⊤ : Submodule ℝ ↥W).map W.subtype = W := Submodule.map_subtype_top W
  calc W = (⊤ : Submodule ℝ ↥W).map W.subtype := h1.symm
    _ = (span ℝ (Set.range b)).map W.subtype := by rw [hspan]
    _ = span ℝ (W.subtype '' Set.range b) := Submodule.map_span _ _
    _ ≤ span ℝ (Set.range fun j : J => (b j : L2)) := by
        refine Submodule.span_le.mpr ?_
        rintro z ⟨x, ⟨j, rfl⟩, hj⟩
        exact Submodule.subset_span (Set.mem_range.mpr ⟨j, hj⟩)

/-- The finite-dimensional orthonormal basis of a nonzero eigenspace. -/
private def eigenSpaceONB {T : L2 →ₗ[ℝ] L2} {μ : ℝ} (_hμ : μ ≠ 0)
    (hfd : FiniteDimensional ℝ (Module.End.eigenspace T μ)) :
    OrthonormalBasis (Fin (Module.finrank ℝ (Module.End.eigenspace T μ))) ℝ
      (Module.End.eigenspace T μ) := by
  haveI := hfd
  exact InnerProductSpace.gramSchmidtOrthonormalBasis (Fintype.card_fin _).symm (fun _ => 0)

/-! ### B. The general splicing theorem -/

/-- **The complete orthonormal eigenfamily (general form)**: a symmetric operator on
`L²` whose nonzero eigenspaces are finite-dimensional, whose kernel is closed, and
whose eigenspaces span densely (the landed compact-spectral-theorem decomposition)
has a complete orthonormal eigenfamily: an orthonormal family of eigenvectors
whose span has trivial orthogonal complement. -/
theorem exists_complete_eigenfamily_of_symmetric {T : L2 →ₗ[ℝ] L2}
    (hsym : T.IsSymmetric)
    (hfd : ∀ μ : ℝ, μ ≠ 0 → FiniteDimensional ℝ (Module.End.eigenspace T μ))
    (hkerClosed : IsClosed (LinearMap.ker T : Set L2))
    (hdecomp : (⨆ μ, Module.End.eigenspace T μ)ᗮ = ⊥) :
    ∃ (ι : Type) (v : ι → L2) (κ : ι → ℝ), Orthonormal ℝ v ∧
      (∀ i, T (v i) = κ i • v i) ∧ (span ℝ (Set.range v))ᗮ = ⊥ := by
  classical
  -- the kernel of T is a Hilbert space; take a Hilbert basis of it
  haveI hWc : CompleteSpace ↥(LinearMap.ker T) := hkerClosed.completeSpace_coe
  obtain ⟨w, b, hbcoe⟩ := exists_hilbertBasis (𝕜 := ℝ) (E := ↥(LinearMap.ker T))
  -- the kernel family in L2, via the coercion given by the Hilbert-basis existence
  have hbo : Orthonormal ℝ ((↑) : w → ↥(LinearMap.ker T)) := by
    rw [← hbcoe]
    exact b.orthonormal
  have hkb : Orthonormal ℝ (fun j : ↥w => ((Subtype.val j : ↥(LinearMap.ker T)) : L2)) :=
    orthonormal_coe_subtype _ hbo
  -- the nonzero-eigenspace families in L2
  have honb : ∀ (μ : ℝ) (hμ : μ ≠ 0),
      Orthonormal ℝ (fun k : Fin (Module.finrank ℝ (Module.End.eigenspace T μ)) =>
        ((⇑(eigenSpaceONB hμ (hfd μ hμ)) k :
          ↥(Module.End.eigenspace T μ)) : L2)) :=
    fun μ hμ => orthonormal_coe_subtype _ (eigenSpaceONB hμ (hfd μ hμ)).orthonormal
  -- the spliced family and its eigenvalues
  set Ef : (p : {x : ℝ // x ≠ 0}) ×
      Fin (Module.finrank ℝ (Module.End.eigenspace T (p.1 : ℝ))) → L2 :=
    fun p => ((⇑(eigenSpaceONB p.1.2 (hfd (p.1 : ℝ) p.1.2)) p.2 :
      ↥(Module.End.eigenspace T (p.1 : ℝ))) : L2) with hEfdef
  set Kf : ↥w → L2 := fun j => ((Subtype.val j : ↥(LinearMap.ker T)) : L2) with hKfdef
  refine ⟨(p : {x : ℝ // x ≠ 0}) ×
      Fin (Module.finrank ℝ (Module.End.eigenspace T (p.1 : ℝ))) ⊕ ↥w,
    Sum.elim Ef Kf, Sum.elim (fun p => (p.1 : ℝ)) (fun _ => 0), ?_, ?_, ?_⟩
  · -- orthonormality of the splice
    constructor
    · rintro (⟨pμ, pk⟩ | j)
      · simp only [hEfdef, hKfdef, Sum.elim_inl]
        exact (honb pμ.1 pμ.2).1 pk
      · simp only [hEfdef, hKfdef, Sum.elim_inr]
        exact hkb.1 j
    · rintro (⟨pμ, pk⟩ | j) (⟨qμ, qk⟩ | k) hij
      all_goals simp only [hEfdef, hKfdef, Sum.elim_inl, Sum.elim_inr]
      · -- inl / inl
        by_cases hpq : pμ.1 = qμ.1
        · have h1 : pμ = qμ := Subtype.ext hpq
          subst h1
          have hne : pk ≠ qk := by
            intro h
            exact hij (congrArg Sum.inl (congrArg (Sigma.mk pμ) h))
          exact (honb pμ.1 pμ.2).2 hne
        · exact eigenspace_inner_eq_zero (μ := pμ.1) (ν := qμ.1) hsym hpq _ _
      · -- inl / inr
        have hmem0 : (((Subtype.val k : ↥(LinearMap.ker T)) : L2) ∈
            Module.End.eigenspace T 0) := by
          rw [Module.End.eigenspace_zero]
          exact (Subtype.val k).2
        exact eigenspace_inner_eq_zero (μ := pμ.1) (ν := 0) hsym pμ.2
          (⇑(eigenSpaceONB pμ.2 (hfd pμ.1 pμ.2)) pk)
          (Subtype.mk ((Subtype.val k : ↥(LinearMap.ker T)) : L2) hmem0)
      · -- inr / inl
        rw [real_inner_comm]
        have hmem0 : (((Subtype.val j : ↥(LinearMap.ker T)) : L2) ∈
            Module.End.eigenspace T 0) := by
          rw [Module.End.eigenspace_zero]
          exact (Subtype.val j).2
        exact eigenspace_inner_eq_zero (μ := qμ.1) (ν := 0) hsym qμ.2
          (⇑(eigenSpaceONB qμ.2 (hfd qμ.1 qμ.2)) qk)
          (Subtype.mk ((Subtype.val j : ↥(LinearMap.ker T)) : L2) hmem0)
      · -- inr / inr
        exact hkb.2 (fun h => hij (congrArg Sum.inr h))
  · -- eigen equations
    rintro (⟨pμ, pk⟩ | j)
    · simp only [hEfdef, hKfdef, Sum.elim_inl]
      have hmem : ((⇑(eigenSpaceONB pμ.2 (hfd pμ.1 pμ.2)) pk :
          ↥(Module.End.eigenspace T pμ.1)) : L2) ∈ Module.End.eigenspace T pμ.1 :=
        Submodule.coe_mem _
      rw [Module.End.mem_eigenspace_iff.mp hmem]
    · simp only [hEfdef, hKfdef, Sum.elim_inr]
      have hmem : ((Subtype.val j : ↥(LinearMap.ker T)) : L2) ∈ LinearMap.ker T :=
        (Subtype.val j).2
      rw [LinearMap.mem_ker.mp hmem, zero_smul]
  · -- completeness
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' := (Submodule.mem_orthogonal (span ℝ (Set.range (Sum.elim Ef Kf))) x).mp hx
    -- kernel pairing
    have hker : ∀ y : ↥(LinearMap.ker T), inner ℝ (Subtype.val y : L2) x = 0 :=
      inner_eq_zero_of_orthogonal_span_dense ((↑) : w → ↥(LinearMap.ker T))
        (by rw [← hbcoe]; exact b.dense_span.ge)
        x (fun j => hx' _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩))
    -- nonzero-eigenspace pairing
    have hne : ∀ (μ : ℝ), μ ≠ 0 → ∀ y ∈ Module.End.eigenspace T μ,
        inner ℝ (y : L2) x = 0 := by
      intro μ hμ y hy
      have hspanonb : span ℝ (Set.range ⇑(eigenSpaceONB hμ (hfd μ hμ))) = ⊤ := by
        rw [← OrthonormalBasis.coe_toBasis (eigenSpaceONB hμ (hfd μ hμ))]
        exact (eigenSpaceONB hμ (hfd μ hμ)).toBasis.span_eq
      exact inner_eq_zero_of_orthogonal_span (⇑(eigenSpaceONB hμ (hfd μ hμ)))
        hspanonb
        x (fun k => hx' _ (Submodule.subset_span ⟨Sum.inl ⟨⟨μ, hμ⟩, k⟩, rfl⟩))
        ⟨y, hy⟩
    have hxmem : x ∈ (⨆ μ, Module.End.eigenspace T μ)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro μ
      rw [Submodule.mem_orthogonal]
      rcases eq_or_ne μ 0 with h0 | h0
      · subst h0
        rw [Module.End.eigenspace_zero]
        exact fun z hz => hker ⟨z, hz⟩
      · exact fun z hz => hne μ h0 z hz
    rw [hdecomp] at hxmem
    exact hxmem

end General

/-! ### C. Riesz instantiation -/

section Riesz

variable {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}

/-- The uniform-`ω` Riesz kernel operator as a continuous linear endomorphism of `L2`. -/
abbrev rieszTOp (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2) : L2 →ₗ[ℝ] L2 :=
  ↑(TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))

set_option maxHeartbeats 1000000 in
/-- **The complete orthonormal eigenfamily of the uniform-`ω` Riesz operator**: there
are an index type `ι`, an orthonormal eigenfamily `v : ι → L2`
(`TOp K_R (v i) = κ i • v i`) and eigenvalues `κ` such that the span of `v` has
trivial orthogonal complement (the spliced family is complete), and the
eigenvalue-energy identity `hsNorm K_R² = ∑' i, κ i²` holds **unconditionally**
(composition with the landed Parseval equality of
`Hurst.TensorONBCompleteness`). -/
theorem exists_complete_eigenfamily
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∃ (ι : Type) (v : ι → L2) (κ : ι → ℝ),
      Orthonormal ℝ v ∧
      (∀ i, rieszTOp (c := c) hpow homega hbdd hg (v i) = κ i • v i) ∧
      (span ℝ (Set.range v))ᗮ = ⊥ ∧
      hsNorm (rieszKernel psi c omega) ^ 2 = ∑' i, κ i ^ 2 := by
  obtain ⟨ι, v, κ, hv, he, hcomp⟩ :=
    exists_complete_eigenfamily_of_symmetric
      (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
      (fun μ hμ => eigenspace_finite_riesz hpow homega hbdd hg hconst hμ)
      (ContinuousLinearMap.isClosed_ker
        (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)))
      (orthocomplement_decomposition_riesz hpow homega hbdd hg hconst)
  exact ⟨ι, v, κ, hv, he, hcomp,
    hsNorm_sq_eq_tsum_eigenvalue_sq_of_orthonormal_complete
      (K := rieszKernel psi c omega) (hK := hsKernel_rieszKernel hpow homega hbdd hg)
      hv hcomp he⟩

end Riesz

end HS

end
