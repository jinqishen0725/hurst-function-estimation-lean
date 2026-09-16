import Hurst.HSOperatorLayer3

/-!
# Spectral enumeration prerequisites for the Riesz kernel operator

The spectral prerequisites for the compact self-adjoint spectral theorem applied to the
Hilbert–Schmidt kernel operator `TOp K hK : L2 →L[ℝ] L2` (`Hurst.HSOperatorFoundation`,
`Hurst.HSOperatorLayer2`), in the **explicit-hypothesis form**: compactness is taken as

```
hCompact : IsCompactOperator (TOp K hK)
```

(the shape the parallel mesh-approximation finisher will discharge via
`Hurst.HSOperatorLayer3.isCompactOperator_TOp_limit`), and positivity — for the
nonneg-eigenvalue corollary — as

```
hPos : ∀ f : L2, 0 ≤ inner ℝ (TOp K hK f) f
```

(documented-optional: pointwise-nonneg kernels do NOT imply it, see the layer-2 tail).

## Main results

* **Self-adjointness bridging** (item 1):
  * `isSelfAdjoint_TOp_of_symmetric_kernel` — symmetric kernel ⇒ `IsSelfAdjoint (TOp K hK)`;
  * `isSymmetric_TOp_of_adjoint_eq` — the adjoint-equality form
    `(TOp K hK).adjoint = TOp K hK` (exactly what `TOp_riesz_selfAdjoint` lands) ⇒
    `LinearMap.IsSymmetric (↑(TOp K hK))`, the shape the mathlib spectral theorems consume
    (bridge `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`);
  * `isSymmetric_TOp_rieszKernel` — the Riesz instantiation.
* **Eigenvalue reality** (item 2): `eigenvalue_conj_self` — every eigenvalue of the
  symmetric kernel operator is self-conjugate (`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`
  at `𝕜 = ℝ`); since the operator is a *real* endomorphism, eigenvalues are elements of `ℝ`
  by type, and the spectrum is real by `eigenvalue_iff_mem_spectrum` (Fredholm alternative:
  for `μ ≠ 0`, `HasEigenvalue ↔ μ ∈ spectrum ℝ (TOp K hK)`).
* **Finite-dimensionality** (item 3): `finiteDimensional_eigenspace_TOp` — for every
  **nonzero** eigenvalue `μ`, the eigenspace is finite-dimensional
  (`ContinuousLinearMap.finite_dimensional_eigenspace`).  The zero eigenspace is the kernel
  of the operator and need NOT be finite-dimensional (only `T = 0` forces that, via
  `ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero`).
* **Orthocomplement decomposition** (item 4):
  `orthogonalComplement_iSup_eigenspaces_TOp` —
  `(⨆ μ, eigenspace (↑(TOp K hK)) μ)ᗮ = ⊥`, the compact self-adjoint spectral theorem
  (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`): the eigenspaces
  span a dense subspace, i.e. everything outside the operator kernel.
* **Nonneg-eigenvalue corollary** (item 5, conditional on `hPos`):
  `inner_TOp_eigenvector` — the Rayleigh identity
  `⟪TOp K v, v⟫ = μ·‖v‖²` for an eigenvector `v`;
  `eigenvalue_nonneg_of_pos` — every eigenvalue is `≥ 0`
  (via mathlib's `eigenvalue_nonneg_of_nonneg`, whose `RCLike.re⟪x, Tx⟫` input our `hPos`
  supplies at `𝕜 = ℝ`).

All statements compile placeholder-free under the explicit hypotheses.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The endomorphism coercion -/

/-- The kernel operator as a (real) linear endomorphism of `L2` — the shape the
mathlib spectral API consumes. -/
abbrev TOpEnd (K : ℝ × ℝ → ℝ) (hK : HSKernel K) : Module.End ℝ L2 :=
  ((TOp K hK : L2 →L[ℝ] L2) : L2 →ₗ[ℝ] L2)

theorem TOpEnd_apply {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) :
    TOpEnd K hK f = TOp K hK f := rfl

/-! ### Item 1: self-adjointness bridging -/

/-- Symmetric kernel ⇒ the kernel operator is self-adjoint
(`IsSelfAdjoint`, i.e. `star A = A` for the adjoint star structure). -/
theorem isSelfAdjoint_TOp_of_symmetric_kernel {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) :
    IsSelfAdjoint (TOp K hK) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr (TOp_selfAdjoint hK hsym)

/-- The adjoint-equality hypothesis (the shape `TOp_riesz_selfAdjoint` lands)
implies `LinearMap.IsSymmetric` — the hypothesis form of the mathlib spectral
theorems (`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`). -/
theorem isSymmetric_TOp_of_adjoint_eq {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hadj : (TOp K hK).adjoint = TOp K hK) :
    (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (ContinuousLinearMap.isSelfAdjoint_iff'.mpr hadj)

/-- Symmetric kernel ⇒ the kernel operator is symmetric in the `LinearMap.IsSymmetric`
form. -/
theorem isSymmetric_TOp_of_symmetric_kernel {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) :
    (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric :=
  isSymmetric_TOp_of_adjoint_eq (TOp_selfAdjoint hK hsym)

/-- **Riesz instantiation**: the Riesz kernel operator
`TOp (rieszKernel psi c omega)` is symmetric whenever the truncated weight
`(Icc (-1) 1).indicator ω` is constant (the uniform-`ω` case landed as
`TOp_riesz_selfAdjoint` in `Hurst.HSOperatorLayer2`). -/
theorem isSymmetric_TOp_rieszKernel {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (↑(TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) :
      L2 →ₗ[ℝ] L2).IsSymmetric :=
  isSymmetric_TOp_of_adjoint_eq (TOp_riesz_selfAdjoint hpow homega hbdd hg hconst)

/-! ### Item 2: eigenvalue reality -/

/-- **Eigenvalue reality**: every eigenvalue of the symmetric kernel operator is
self-conjugate (`LinearMap.IsSymmetric.conj_eigenvalue_eq_self` at `𝕜 = ℝ`).
For a real endomorphism the eigenvalues are already elements of `ℝ` by type; this
specialization is the form that transfers verbatim to a complexification. -/
theorem eigenvalue_conj_self {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ) :
    (starRingEnd ℝ) μ = μ :=
  hsym.conj_eigenvalue_eq_self hμ

/-- **Real spectrum** (Fredholm alternative): for a compact kernel operator, the nonzero
eigenvalues are exactly the nonzero points of the real spectrum.  In particular every
spectral point of `TOp K hK` is real (the spectrum is taken over `ℝ`). -/
theorem eigenvalue_iff_mem_spectrum {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    {μ : ℝ} (hμ : μ ≠ 0) :
    (Module.End.HasEigenvalue ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ
      ↔ μ ∈ spectrum ℝ (TOp K hK)) :=
  IsCompactOperator.hasEigenvalue_iff_mem_spectrum hCompact hμ

/-- Fredholm alternative dichotomy: every nonzero scalar either is an eigenvalue of the
compact kernel operator or lies in the resolvent set. -/
theorem eigenvalue_or_resolvent {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    {μ : ℝ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ
      ∨ μ ∈ resolventSet ℝ (TOp K hK) :=
  IsCompactOperator.hasEigenvalue_or_mem_resolventSet hCompact hμ

/-! ### Item 3: finite-dimensionality of the eigenspaces -/

/-- **Finite-dimensionality**: every eigenspace of a compact kernel operator with
**nonzero** eigenvalue is finite-dimensional.  (The zero eigenspace is the operator
kernel and need not be finite-dimensional.) -/
theorem finiteDimensional_eigenspace_TOp {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (↑(TOp K hK) : L2 →ₗ[ℝ] L2) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hCompact μ hμ

/-- Concrete eigenspace membership for the kernel operator. -/
theorem mem_eigenspace_TOp_iff {K : ℝ × ℝ → ℝ} {hK : HSKernel K} {μ : ℝ} (f : L2) :
    f ∈ Module.End.eigenspace (↑(TOp K hK) : L2 →ₗ[ℝ] L2) μ ↔ TOp K hK f = μ • f :=
  Module.End.mem_eigenspace_iff

/-! ### Item 4: the orthocomplement decomposition -/

/-- **Compact self-adjoint spectral theorem**: the orthogonal complement of the span of
all eigenspaces of a compact symmetric kernel operator is trivial — the eigenvectors
span everything except the kernel of the operator. -/
theorem orthogonalComplement_iSup_eigenspaces_TOp {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric) :
    (⨆ μ, Module.End.eigenspace (↑(TOp K hK) : L2 →ₗ[ℝ] L2) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hCompact hsym

/-! ### Item 5: the nonneg-eigenvalue corollary (conditional on hPos) -/

/-- **Rayleigh identity**: for an eigenvector `v` of the kernel operator with eigenvalue
`μ`, the quadratic form evaluates to `μ · ‖v‖²`. -/
theorem inner_TOp_eigenvector {K : ℝ × ℝ → ℝ} {hK : HSKernel K} {μ : ℝ} {v : L2}
    (hv : Module.End.HasEigenvector ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ v) :
    inner ℝ (TOp K hK v) v = μ * ‖v‖ ^ 2 := by
  have h1 : (↑(TOp K hK) : L2 →ₗ[ℝ] L2) v = μ • v := hv.apply_eq_smul
  rw [show inner ℝ (TOp K hK v) v
      = inner ℝ ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) v) v from rfl, h1,
    real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **Nonneg eigenvalues**: if the kernel operator has nonneg quadratic form
(`hPos` — an explicit hypothesis, NOT implied by pointwise nonnegativity of the kernel),
then every eigenvalue is `≥ 0`.  Proof via mathlib's Rayleigh-quotient lemma
`eigenvalue_nonneg_of_nonneg` (its `RCLike.re ⟪x, T x⟫` input is our `hPos` at `𝕜 = ℝ`). -/
theorem eigenvalue_nonneg_of_pos {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hPos : ∀ f : L2, 0 ≤ inner ℝ (TOp K hK f) f)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ) :
    0 ≤ μ := by
  refine eigenvalue_nonneg_of_nonneg hμ fun x => ?_
  have h1 : RCLike.re (inner ℝ x ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) x))
      = inner ℝ (TOp K hK x) x := by
    rw [real_inner_comm]
    rfl
  rw [h1]
  exact hPos x

/-- Same corollary, proved directly from the Rayleigh identity `inner_TOp_eigenvector`:
`μ = ⟪Tv, v⟫ / ‖v‖² ≥ 0` for a unit eigenvector. -/
theorem eigenvalue_nonneg_of_pos' {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hPos : ∀ f : L2, 0 ≤ inner ℝ (TOp K hK f) f)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue ((↑(TOp K hK) : L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ) :
    0 ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hvne : v ≠ 0 := hv.2
  have hv1 : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hvne
  have hvpos : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have hray := inner_TOp_eigenvector hv
  have hq : 0 ≤ μ * ‖v‖ ^ 2 := by rw [← hray]; exact hPos v
  exact (mul_nonneg_iff_of_pos_right hvpos).mp hq

end HS

end
