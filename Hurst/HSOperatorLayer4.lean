import Hurst.HSOperatorLayer3

/-!
# HS operator layer 4: quadratic-form positivity and the spectral bridges

Builds the positivity / spectrum-clause prerequisites on the landed `HS` stack
(`Hurst.HSOperatorFoundation`, `Hurst/HSOperatorLayer2.lean`,
`Hurst/HSOperatorLayer3.lean`), reusing its encoding exactly: kernels
`K : ℝ × ℝ → ℝ`, `HSKernel K = MemLp K 2 vol2`, `TOp K hK : L2 →L[ℝ] L2`,
`kpair K f g = ∫∫ K(x,y) f(y) g(x)`.

## Main results (all sorry-free)

* `KernelPSD` — the quadratic-form positivity predicate `∀ f : L2, 0 ≤ kpair K f f`;
  * `KernelPSD_sq_degenerate` — **the elementary PSD source**: diagonal finite-rank
    kernels `∑_{j∈s} a_j ⊗ a_j` are PSD, since
    `kpair (∑ a_j ⊗ a_j) f f = ∑ (∫ a_j · f)² ≥ 0` (from layer-3 `kpair_degenerate`);
  * `KernelPSD_add`, `KernelPSD_smul` — the PSD class is a convex cone;
* `eigenvalue_nonneg_of_kernelPSD` — **the clause-(i) bridge**: `KernelPSD K` forces
  every eigenvalue `μ` of `TOp K` to satisfy `0 ≤ μ` (elementary: on an eigenvector,
  `kpair K v v = μ‖v‖²`); `eigenvalue_nonneg_of_kernelPSD_mathlib` — the same fact
  proved by instantiating mathlib's `eigenvalue_nonneg_of_nonneg` directly (`𝕜 = ℝ`
  works; `RCLike.re` collapses by `show`);
* `abs_eigenvalue_le_hsNorm` — every eigenvalue satisfies `|μ| ≤ hsNorm K`
  (operator-norm bound; the tail control input for `Summable λ²`);
* `isSelfAdjoint_TOp`, `isSymmetric_TOp` — the `IsSelfAdjoint`/`LinearMap.IsSymmetric`
  bridges for symmetric kernels (via `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`);
* `eigenspace_orthogonal_eq_bot_of_compact`,
  `finite_dim_eigenspace_of_compact` — the mathlib compact-self-adjoint spectral
  theorem (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`,
  `ContinuousLinearMap.finite_dimensional_eigenspace`), instantiated on `L2` with
  `𝕜 = ℝ` (the `RCLike` generality covers it);
* `riesz_eigenspace_orthogonal_eq_bot` — the same, specialized to the uniform-`ω`
  truncated Riesz kernel of layer 2, conditional on the (still open, layer-3 mesh
  input) compactness of `TOp K_R`.

## Positivity verdict for the Riesz kernel (honest report)

* `KernelPSD K` for the Riesz kernel `K_R(x,y) = ω(x)·c·|x-y|^(-ψ)` is **NOT landed**
  and is genuinely harder than `K ≥ 0` pointwise: the integrand factor `f(y)f(x)`
  changes sign, so pointwise nonnegativity of the kernel does NOT give a nonneg
  quadratic form (the layer-2 counterexample: the moving-average kernel `1_{|x-y|≤ε}`
  is pointwise nonneg but has negative eigenvalues).
* The true route for the uniform-`ω` case is positive-definiteness of
  `|x-y|^(-ψ)` as a function of `x-y` (its Fourier symbol `~|ξ|^{-(1-ψ)}` is positive;
  equivalently the Laplace representation `x^{-ψ} = (1/Γ(ψ))∫₀^∞ t^{ψ-1}e^{-tx}dt`
  writes the kernel as a mixture of `e^{-t|x-y|}`, each of which is positive-definite
  as the characteristic function of a Cauchy law).  Mathlib v4.31 has **no** Bochner /
  positive-definite-function / Fourier-inversion API at the level needed for this
  argument (searched: `Analysis/InnerProductSpace/Positive.lean` is the finite-order
  operator positivity `0 ≤ ⟪Tx, x⟫`, `Analysis/Matrix/PosDef.lean` is matrix-level).
  Landing this would need a self-contained Fourier-inversion development — deferred.
* Downstream, clause (i) (`0 ≤ λ_j`) is therefore carried as the conditional
  `eigenvalue_nonneg_of_kernelPSD` + `KernelPSD_sq_degenerate`: PSD is available for
  degenerate kernel models, and the general Riesz case is open.  The peeling chain's
  signed variant (`Hurst/EvenPeeling.lean`) covers signed spectra, so clauses
  (ii) `Summable λ²` + (iii) `HasSum` do not need clause (i).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The PSD class and its elementary sources -/

/-- Quadratic-form positivity (positive semidefiniteness) of a kernel:
`kpair K f f = ∫∫ K(x,y) f(y) f(x) ≥ 0` for all `f ∈ L²`. -/
def KernelPSD (K : ℝ × ℝ → ℝ) : Prop := ∀ f : L2, 0 ≤ kpair K f f

/-- **The elementary PSD source**: a diagonal finite-rank kernel `∑_{j∈s} a_j ⊗ a_j`
has nonnegative quadratic form — the pairing factors as `∑ (∫ a_j · f)² ≥ 0`. -/
theorem KernelPSD_sq_degenerate {ι : Type*} (s : Finset ι) (a : ι → ℝ → ℝ)
    (ha : ∀ j, MemLp (a j) 2 vol) :
    KernelPSD (fun p => ∑ j ∈ s, a j p.1 * a j p.2) := by
  intro f
  rw [kpair_degenerate s a a ha ha f f]
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- The PSD class is closed under addition of kernels. -/
theorem KernelPSD_add {K₁ K₂ : ℝ × ℝ → ℝ} (hK₁ : HSKernel K₁) (hK₂ : HSKernel K₂)
    (h₁ : KernelPSD K₁) (h₂ : KernelPSD K₂) : KernelPSD (K₁ + K₂) := by
  intro f
  rw [kpair_add_kernel hK₁ hK₂ f f]
  exact add_nonneg (h₁ f) (h₂ f)

/-- The PSD class is closed under multiplication by a nonnegative scalar. -/
theorem KernelPSD_smul {K : ℝ × ℝ → ℝ} (hK : HSKernel K) {c : ℝ} (hc : 0 ≤ c)
    (h : KernelPSD K) : KernelPSD (c • K) := by
  intro f
  rw [kpair_smul_kernel c hK f f]
  exact mul_nonneg hc (h f)

/-! ### The eigenvalue bridge -/

/-- **Clause-(i) bridge**: quadratic-form positivity forces every eigenvalue `μ` of
the kernel operator to be nonnegative.  (On an eigenvector `v ≠ 0`,
`kpair K v v = ⟪TOp K v, v⟫ = μ·‖v‖²`.) -/
theorem eigenvalue_nonneg_of_kernelPSD {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hpsd : KernelPSD K) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue ((TOp K hK : L2 →ₗ[ℝ] L2)) μ) : 0 ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hve : (TOp K hK : L2 →ₗ[ℝ] L2) v = μ • v := hv.apply_eq_smul
  simp only [ContinuousLinearMap.coe_coe] at hve
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  have hvp : (0:ℝ) < ‖v‖ ^ 2 := sq_pos_iff.mpr hv0
  have h1 : 0 ≤ kpair K v v := hpsd v
  have hinner : kpair K v v = μ * ‖v‖ ^ 2 := by
    rw [← inner_TOp hK v v, hve, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hinner] at h1
  exact (mul_nonneg_iff_of_pos_right hvp).mp h1

/-- The same bridge, proved by instantiating mathlib's `eigenvalue_nonneg_of_nonneg`
(`Analysis/InnerProductSpace/Spectrum.lean`) directly: the `RCLike.re` in its
hypothesis is the identity for `𝕜 = ℝ` (collapsed by `show`), and the pairing
translates through `inner_TOp`. -/
theorem eigenvalue_nonneg_of_kernelPSD_mathlib {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hpsd : KernelPSD K) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue ((TOp K hK : L2 →ₗ[ℝ] L2)) μ) : 0 ≤ μ := by
  refine eigenvalue_nonneg_of_nonneg hμ fun x => ?_
  show 0 ≤ inner ℝ x ((TOp K hK : L2 →ₗ[ℝ] L2) x)
  have hx : inner ℝ x ((TOp K hK : L2 →ₗ[ℝ] L2) x) = kpair K x x := by
    rw [ContinuousLinearMap.coe_coe, real_inner_comm, inner_TOp hK x x]
  rw [hx]
  exact hpsd x

/-- Eigenvalues are bounded by the operator norm. -/
theorem abs_eigenvalue_le_norm {K : ℝ × ℝ → ℝ} (hK : HSKernel K) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue ((TOp K hK : L2 →ₗ[ℝ] L2)) μ) :
    |μ| ≤ ‖TOp K hK‖ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hve : (TOp K hK : L2 →ₗ[ℝ] L2) v = μ • v := hv.apply_eq_smul
  simp only [ContinuousLinearMap.coe_coe] at hve
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  have hnorm : ‖TOp K hK v‖ = |μ| * ‖v‖ := by
    rw [hve, norm_smul, Real.norm_eq_abs]
  have hle : |μ| * ‖v‖ ≤ ‖TOp K hK‖ * ‖v‖ := by
    rw [← hnorm]
    exact ContinuousLinearMap.le_opNorm _ v
  exact le_of_mul_le_mul_right hle
    (lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv0))

/-- The combined bound: every eigenvalue is controlled by the kernel HS norm
(the tail input for `Summable λ²`). -/
theorem abs_eigenvalue_le_hsNorm {K : ℝ × ℝ → ℝ} (hK : HSKernel K) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue ((TOp K hK : L2 →ₗ[ℝ] L2)) μ) :
    |μ| ≤ hsNorm K :=
  (abs_eigenvalue_le_norm hK hμ).trans (TOp_norm_le hK)

/-! ### The self-adjointness bridges -/

/-- Symmetric kernels give self-adjoint operators, in the `IsSelfAdjoint` sense
required by the compact spectral theorem. -/
theorem isSelfAdjoint_TOp {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) : IsSelfAdjoint (TOp K hK) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr (TOp_selfAdjoint hK hsym)

/-- The same fact in the `LinearMap.IsSymmetric` shape of the eigenspace API. -/
theorem isSymmetric_TOp {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) :
    LinearMap.IsSymmetric ((TOp K hK : L2 →L[ℝ] L2) : L2 →ₗ[ℝ] L2) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_TOp hK hsym)

/-! ### The compact self-adjoint spectral theorem, instantiated on `L2` -/

/-- **Spectral theorem (compact self-adjoint case)**: for a symmetric kernel whose
operator is compact, the eigenspaces of `TOp K` span densely (their orthogonal
complement is trivial). -/
theorem eigenspace_orthogonal_eq_bot_of_compact {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap)
    (hcomp : IsCompactOperator (TOp K hK)) :
    (⨆ μ, Module.End.eigenspace ((TOp K hK : L2 →ₗ[ℝ] L2)) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcomp
    (isSymmetric_TOp hK hsym)

/-- **Spectral theorem (compact self-adjoint case)**: nonzero eigenspaces of a compact
kernel operator are finite-dimensional. -/
theorem finite_dim_eigenspace_of_compact {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (hcomp : IsCompactOperator (TOp K hK)) (μ : ℝ) (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace ((TOp K hK : L2 →ₗ[ℝ] L2)) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hcomp μ hμ

/-! ### Specialization to the uniform-`ω` Riesz kernel (conditional on compactness) -/

/-- The uniform-`ω` truncated Riesz kernel of layer 2 is symmetric. -/
theorem rieszKernel_symm_of_const {psi c : ℝ} {omega : ℝ → ℝ}
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∀ p : ℝ × ℝ, rieszKernel psi c omega p = rieszKernel psi c omega p.swap := by
  intro p
  have e1 : rieszKernel psi c omega p
      = (I : Set ℝ).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi) :=
    rieszKernel_apply _ _ _ _ _
  have e2 : rieszKernel psi c omega p.swap
      = (I : Set ℝ).indicator omega p.2 * c * |p.2 - p.1| ^ (-psi) :=
    rieszKernel_apply psi c omega p.2 p.1
  rw [e1, e2, hconst p.1 p.2, abs_sub_comm p.1 p.2]

/-- **The Riesz spectral decomposition** (conditional on compactness, the open layer-3
mesh input): for the uniform-`ω` truncated Riesz kernel, the eigenspaces of `TOp K_R`
span densely in `L²`. -/
theorem riesz_eigenspace_orthogonal_eq_bot {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hcomp : IsCompactOperator (TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg))) :
    (⨆ μ, Module.End.eigenspace
      ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2)) μ)ᗮ = ⊥ :=
  eigenspace_orthogonal_eq_bot_of_compact (hsKernel_rieszKernel hpow homega hbdd hg)
    (rieszKernel_symm_of_const hconst) hcomp

end HS

end
