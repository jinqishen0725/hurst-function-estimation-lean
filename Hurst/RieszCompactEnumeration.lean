import Hurst.HSOperatorFoundation
import Hurst.HSOperatorLayer2
import Hurst.HSOperatorLayer3
import Hurst.HSOperatorLayer4
import Hurst.HSKernelMeshApprox
import Hurst.SpectralEnumeration
import Hurst.FrozenSpectralEnumeration

/-!
# Compactness and spectral enumeration for the uniform-`ω` Riesz kernel operator

Discharges the `hCompact` hypothesis of the conditional spectral enumeration
(`Hurst.SpectralEnumeration`, `Hurst.FrozenSpectralEnumeration`) for the continuum
truncated weighted Riesz kernel `rieszKernel psi c omega` of `Hurst.HSOperatorLayer2`,
and lands the Riesz-instantiated corollaries.

## Step 1 — compactness (`isCompactOperator_TOp_riesz`)

The raw Riesz kernel `K_R(x,y) = ω(x)·c·|x-y|^(-ψ)` is DISCONTINUOUS on the diagonal, so
`continuous_kernel_compact` does not apply directly.  The route (all inputs landed):

1. the raw kernel is a Hilbert–Schmidt kernel (`hsKernel_rieszKernel`);
2. `exists_continuous_approx` (density of bounded-continuous kernels in `hsNorm`) gives a
   bounded-CONTINUOUS approximant `K_n` with `hsNorm (K_R - K_n) ≤ 1/(n+1)`;
3. `TOp K_n` is compact (`continuous_kernel_compact`);
4. `TOp_norm_diff_le` gives `‖TOp K_R - TOp K_n‖ ≤ hsNorm (K_R - K_n) ≤ 1/(n+1)`;
5. `isCompactOperator_TOp_limit` closes: `TOp K_R` is compact.

## Step 2 — Riesz-instantiated enumeration

The conditional theorems of `Hurst.SpectralEnumeration`, instantiated on the uniform-`ω`
Riesz kernel with `hCompact := isCompactOperator_TOp_riesz ...`:
`isSelfAdjoint_TOp_riesz`, `eigenvalues_real_riesz`, `eigenspace_finite_riesz`,
`orthocomplement_decomposition_riesz`, plus the Fredholm dichotomy
`eigenvalue_or_resolvent_riesz`.

## Step 3 — countability / summability groundwork

* `eigenvalue_level_finite` — for every `ε > 0` the set of eigenvalues of modulus `≥ ε` is
  finite (the compactness contradiction core `not_injective_eigenvalues_ge` of
  `Hurst.FrozenSpectralEnumeration` + the choice plumbing through
  `Set.Infinite.natEmbedding`); Riesz-instantiated as `eigenvalue_set_finite_riesz`.
* `nonzero_spectrum_countable` — the nonzero spectrum is countable; Riesz-instantiated as
  `eigenvalue_set_countable_riesz`.  Together with the finite levels this IS the
  "the nonzero spectrum is countable with `0` as its only possible accumulation point"
  statement.  (Named distinctly from the parallel `Hurst.FrozenSpectralCount` lemmas,
  which have identical statements — a consumer importing both modules gets each fact
  under at least one unambiguous name, and the Riesz-instantiated corollaries here
  discharge the `hCompact` hypothesis.)
* `abs_eigenvalue_riesz_le_hsNorm`, `sq_eigenvalue_riesz_le_hsNorm_sq` — the per-entry
  tail bound `|μ| ≤ hsNorm K_R` (summability groundwork for `Σ μ_j²`).

## Gap report — the remaining path to P2's `rieszSpectrum`

Every prerequisite of the decreasing enumeration with `HasSum` to the cycle integrals is
now unconditional EXCEPT the trace-power identification `tr(TOp^k) = weightedRieszCycleIntegral
k psi c omega` (its `k = 2` case is landed as `HS.cycle2` / `HS.cycle2_bound`).  The final
layer is: (a) the enumeration-with-multiplicity existence (the
`Countable.exists_surjective_nat` sigma-type plumbing documented in the gap report of
`Hurst.FrozenSpectralEnumeration`), and (b) `Σ_j val j ^ k = tr(TOp^k)` for `k ≥ 2`
(needs the section formula `(Tf) x = ∫ K(x,y) f y dy`, which `Hurst.HSOperatorFoundation`
does not land — `TOpFun` is defined through the Riesz representer).  PSD of the uniform-`ω`
kernel (the Fourier route) remains deferred as documented in `Hurst.HSOperatorLayer4`;
the signed peeling chain covers signed spectra.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### Step 1: compactness of the uniform-`ω` Riesz operator -/

/-- `hsNorm` is invariant under swapping the order of subtraction (squaring kills the
sign); this bridges the `hsNorm (K - L)` of `TOp_norm_diff_le` with the
`hsNorm (fun p => L p - K p)` produced by `exists_continuous_approx`. -/
private theorem hsNorm_sub_comm (A B : ℝ × ℝ → ℝ) :
    hsNorm (A - B) = hsNorm (fun p => B p - A p) := by
  rw [hsNorm_def, hsNorm_def]
  refine congrArg Real.sqrt ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show (A - B) p ^ 2 = (B p - A p) ^ 2
  simp only [Pi.sub_apply]
  ring

set_option maxHeartbeats 1000000 in
/-- **The compactness theorem for the uniform-`ω` Riesz kernel operator**: the operator
`TOp K_R` of the continuum truncated weighted Riesz kernel is a compact operator.
The diagonal discontinuity is bypassed by operator-norm approximation with
bounded-continuous kernels (`exists_continuous_approx`) and the compact-limit bridge
(`isCompactOperator_TOp_limit`).  Hypotheses exactly match `TOp_riesz_selfAdjoint`
(the `2ψ < 1` requirement enters through the square-integrability `hg`). -/
theorem isCompactOperator_TOp_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    IsCompactOperator (TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg)) := by
  classical
  have hall : ∀ n : ℕ, ∃ g : ℝ × ℝ → ℝ, Continuous g ∧
      HSKernel g ∧ hsNorm (fun p => rieszKernel psi c omega p - g p) ≤ 1 / ((n:ℝ) + 1) :=
    fun n => exists_continuous_approx (hsKernel_rieszKernel hpow homega hbdd hg)
      (by positivity)
  choose g hgc hgm hgn using hall
  have hTc : ∀ n : ℕ, IsCompactOperator (TOp (g n) (hgm n)) := fun n =>
    continuous_kernel_compact (hgm n) (hgc n)
  have hTn : ∀ n : ℕ, ‖TOp (g n) (hgm n) - TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg)‖ ≤ 1 / ((n:ℝ) + 1) := by
    intro n
    calc ‖TOp (g n) (hgm n) - TOp (rieszKernel psi c omega)
          (hsKernel_rieszKernel hpow homega hbdd hg)‖
        ≤ hsNorm (g n - rieszKernel psi c omega) :=
          TOp_norm_diff_le (hgm n) (hsKernel_rieszKernel hpow homega hbdd hg)
      _ = hsNorm (fun p => rieszKernel psi c omega p - g n p) := hsNorm_sub_comm _ _
      _ ≤ 1 / ((n:ℝ) + 1) := hgn n
  exact isCompactOperator_TOp_limit (hsKernel_rieszKernel hpow homega hbdd hg)
    (fun n => TOp (g n) (hgm n)) hTc hTn

/-! ### Step 2: the Riesz-instantiated enumeration -/

/-- **Riesz self-adjointness bridge**: the uniform-`ω` Riesz kernel operator is
self-adjoint in the `IsSelfAdjoint` shape of the compact spectral theorem. -/
theorem isSelfAdjoint_TOp_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    IsSelfAdjoint (TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg)) :=
  isSelfAdjoint_TOp_of_symmetric_kernel (rieszKernel_symm_of_const hconst)

/-- **Eigenvalue reality for the Riesz operator**: every eigenvalue of the uniform-`ω`
Riesz kernel operator is self-conjugate (real eigenvalues; the form transferring
verbatim to a complexification). -/
theorem eigenvalues_real_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {μ : ℝ}
    (hμ : Module.End.HasEigenvalue
      ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ) :
    (starRingEnd ℝ) μ = μ :=
  eigenvalue_conj_self (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst) hμ

/-- **Fredholm dichotomy for the Riesz operator**: every nonzero scalar is either an
eigenvalue of the compact Riesz operator or lies in its resolvent set. -/
theorem eigenvalue_or_resolvent_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {μ : ℝ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue
      ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ
      ∨ μ ∈ resolventSet ℝ (TOp (rieszKernel psi c omega)
        (hsKernel_rieszKernel hpow homega hbdd hg)) :=
  eigenvalue_or_resolvent (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst) hμ

/-- **Finite-dimensional eigenspaces for the Riesz operator**: every eigenspace of the
compact Riesz operator with nonzero eigenvalue is finite-dimensional. -/
theorem eigenspace_finite_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace
      ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ) :=
  finiteDimensional_eigenspace_TOp
    (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst) hμ

/-- **Orthocomplement decomposition for the Riesz operator** (compact self-adjoint
spectral theorem): the eigenspaces of the compact Riesz operator span densely —
their orthogonal complement is trivial. -/
theorem orthocomplement_decomposition_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (⨆ μ, Module.End.eigenspace
      ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ)ᗮ = ⊥ :=
  orthogonalComplement_iSup_eigenspaces_TOp
    (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)

/-! ### Step 3a: the tail bound (summability groundwork) -/

/-- Every eigenvalue of the uniform-`ω` Riesz kernel operator satisfies
`|μ| ≤ hsNorm K_R`. -/
theorem abs_eigenvalue_riesz_le_hsNorm {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {μ : ℝ}
    (hμ : Module.End.HasEigenvalue
      ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ) :
    |μ| ≤ hsNorm (rieszKernel psi c omega) :=
  abs_eigenvalue_le_hsNorm _ hμ

/-- Squared form of the per-entry tail bound: `μ² ≤ hsNorm K_R²`. -/
theorem sq_eigenvalue_riesz_le_hsNorm_sq {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {μ : ℝ}
    (hμ : Module.End.HasEigenvalue
      ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2) : Module.End ℝ L2) μ) :
    μ ^ 2 ≤ hsNorm (rieszKernel psi c omega) ^ 2 := by
  have h := abs_eigenvalue_riesz_le_hsNorm hpow homega hbdd hg hconst hμ
  have h2 := pow_le_pow_left₀ (abs_nonneg μ) h 2
  rwa [sq_abs] at h2

/-! ### Step 3b: countability of the nonzero spectrum -/

set_option maxHeartbeats 1000000 in
/-- **Eigenvalue levels are finite**: for a compact symmetric kernel operator and
`ε > 0`, the set of eigenvalues of modulus `≥ ε` is finite.  Proof: an infinite level
yields an injective eigenvalue sequence with unit eigenvectors through
`Set.Infinite.natEmbedding` (choice plumbing), contradicting the compactness core
`not_injective_eigenvalues_ge` of `Hurst.FrozenSpectralEnumeration`.  (Same statement as
`Hurst.FrozenSpectralCount.eigenvalue_set_finite`; named distinctly to avoid the
cross-module ambiguity for consumers importing both.) -/
theorem eigenvalue_level_finite {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ ε ≤ |μ|}.Finite := by
  by_contra hnf
  have hinf : {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ ε ≤ |μ|}.Infinite :=
    hnf
  obtain ⟨f, hfij⟩ := hinf.natEmbedding
  have hprop : ∀ n : ℕ,
      Module.End.HasEigenvalue (TOpEnd' K hK) ((f n : ℝ)) ∧ ε ≤ |(f n : ℝ)| :=
    fun n => (f n).property
  choose v hv using fun n => (hprop n).1.exists_hasEigenvector
  have hevec : ∀ n : ℕ, Module.End.HasEigenvector (TOpEnd' K hK) ((f n : ℝ))
      ((‖v n‖⁻¹ : ℝ) • v n) := fun n => (hasEigenvector_norm_inv (hv n)).1
  have hunit : ∀ n : ℕ, ‖((‖v n‖⁻¹ : ℝ) • v n)‖ = 1 := fun n =>
    (hasEigenvector_norm_inv (hv n)).2
  have hinj : Function.Injective (fun n : ℕ => ((f n : ℝ) : ℝ)) := by
    intro i j hij
    exact hfij (Subtype.ext hij)
  exact not_injective_eigenvalues_ge hCompact hsym hε (fun n => (f n : ℝ))
    (fun n => (‖v n‖⁻¹ : ℝ) • v n) hevec hunit (fun n => (hprop n).2) hinj

/-- **The nonzero spectrum is countable**: for a compact symmetric kernel operator,
the set of nonzero eigenvalues is countable — a countable union of the finite levels
`{μ : |μ| ≥ 1/(n+1)}`. -/
theorem nonzero_spectrum_countable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric) :
    {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0}.Countable := by
  have hlev : ∀ n : ℕ,
      {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧
        (1:ℝ) / ((n:ℝ) + 1) ≤ |μ|}.Countable :=
    fun n => (eigenvalue_level_finite hCompact hsym (by positivity)).countable
  have hsub : {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0} ⊆
      ⋃ n : ℕ, {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧
        (1:ℝ) / ((n:ℝ) + 1) ≤ |μ|} := by
    intro μ ⟨hμ, hμ0⟩
    have hpos : (0:ℝ) < |μ| := abs_pos.mpr hμ0
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |μ|)
    have hmul : (1:ℝ) < (n:ℝ) * |μ| := (div_lt_iff₀ hpos).mp hn
    rw [mul_comm] at hmul
    refine Set.mem_iUnion.mpr ⟨n, hμ, ?_⟩
    refine (div_le_iff₀ (show (0:ℝ) < (n:ℝ) + 1 by linarith)).mpr ?_
    rw [mul_add]
    linarith
  exact Set.Countable.mono hsub (Set.countable_iUnion hlev)

/-! ### Step 3c: the Riesz-instantiated countability -/

/-- **Finite eigenvalue levels for the Riesz operator**: for every `ε > 0`, only
finitely many eigenvalues of the uniform-`ω` Riesz operator have modulus `≥ ε` —
`0` is the only possible accumulation point of the spectrum. -/
theorem eigenvalue_set_finite_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | Module.End.HasEigenvalue
      (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ ∧
      ε ≤ |μ|}.Finite :=
  eigenvalue_level_finite (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst) hε

/-- **Countable nonzero spectrum for the Riesz operator**: the nonzero eigenvalues of
the uniform-`ω` Riesz kernel operator form a countable set. -/
theorem eigenvalue_set_countable_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    {μ : ℝ | Module.End.HasEigenvalue
      (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ ∧
      μ ≠ 0}.Countable :=
  nonzero_spectrum_countable (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)

end HS

end
