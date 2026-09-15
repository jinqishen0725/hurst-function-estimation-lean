import Hurst.HSCycleComposition
import Hurst.CycleTraceIdentification
import Hurst.FrozenSpectralCount
import Hurst.HSOperatorLayer3
import Hurst.P2SpectrumCloseout

/-!
# General-`k` HasSum for the Riesz spectrum: the `k = 2` anchor and the interpolation layer

This file lands the honest general-`k` layer of the `IsRieszSpectrumSequence` power-sum
consumption on the landed encoding (`Hurst.HSOperatorFoundation`/`Hurst.HSOperatorLayer2`,
assembled by `Hurst.P2SpectrumCloseout`): for a multiplicity-exact eigenvalue enumeration
`(val, vec)` of the compact symmetric kernel operator `TOp K hK`
(`HS.exists_multiplicity_enumeration`, `Hurst.FrozenSpectralCount`), it proves

1. **The `k = 2` HasSum anchor** (`HS.rieszSpectrum_hasSum_two`, Riesz-instantiated):
   `HasSum (fun j => val j ^ 2) (∑' j, val j ^ 2)` together with the identification of the
   target's closure
   `∑' j, val j ^ 2 ≤ weightedRieszCycleIntegral 2 psi c omega`
   (`HS.rieszSpectrum_two_tsum_le_cycleIntegral` + the landed
   `weightedRieszCycleIntegral 2 psi c omega = hsNorm K_R ^ 2`,
   `Hurst.RieszSpectralTrace`).  This is the honest closed form: upgrading the bound to the
   exact `HasSum … (weightedRieszCycleIntegral 2 psi c omega)` needs the REVERSE Parseval
   inequality `hsNorm K_R² ≤ ∑' val j²` — the kernel expansion `K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)`
   in `L²(vol2)`, the documented boundary of `Hurst.HSNormIdentity` /
   `Hurst.CycleTraceIdentification` / `Hurst.RieszSpectralTrace` (NOT landed here).

2. **The interpolation / summability layer (general `k ≥ 2`)** — the honest bounded form
   of the general-`k` HasSum:
   * `HS.abs_le_hsNorm_of_multEnum` — per-entry `|val j| ≤ hsNorm K` (eigenvalue norm
     bound + `TOp_norm_le`);
   * `HS.pow_abs_le_mul_sq` — norm interpolation per entry:
     `|val j| ^ k ≤ hsNorm K ^ (k-2) * val j ^ 2` for `2 ≤ k` (since `|val j| ≤ hsNorm K`);
   * `HS.summable_abs_pow_of_multEnum` — `Summable (fun j => |val j| ^ k)` for every
     `k ≥ 2` (finite Bessel partial-sum bounds + `summable_of_sum_le`);
   * `HS.tsum_abs_pow_le_multEnum` — `∑' j, |val j| ^ k ≤ hsNorm K ^ k`;
   * `HS.tsum_abs_pow_le_mul_tsum_sq` — the interpolated form
     `∑' j, |val j| ^ k ≤ hsNorm K ^ (k-2) * ∑' j, val j ^ 2` (via `hasSum_le` against the
     scaled square series);
   * `HS.summable_pow_of_posTOp` — under operator positivity (`hPos`), the power series
     itself: `Summable (fun j => val j ^ k)` for every `k ≥ 2`;
   * `HS.exists_multiplicity_enumeration_pow_summable` — the consumption bundle packaging
     the enumeration clauses with all of the above;
   * the Riesz-instantiated `HS.rieszSpectrum_hasSum_general_k`: the sequence
     `|rieszSpectrumVal …| ^ k` `HasSum`s to its own tsum, and the tsum is bounded both by
     `hsNorm K_R ^ (k-2) * weightedRieszCycleIntegral 2 psi c omega` and by
     `hsNorm K_R ^ k` — the honest HasSum-to-the-Riesz-side-limit.

3. **The `C_k`-exact HasSum (`k ≥ 3`) — DOCUMENTED BOUNDARY.**  The exact identification
   `HasSum (fun j => val j ^ k) (weightedRieszCycleIntegral k psi c omega)` for `k ≥ 3`
   is gated on the spectral-Calculus composition — the contraction/peel induction
   `C_k(K) = C_{k-1}(compKernel K K)` of `Hurst.HSCycleComposition` (documented residue:
   the `hA`/`hB` integrability discharges of `cycle2_compKernel_eq_triple` /
   `cycle2_eq_compKernel_triple`, the `chainCycleTriple = chainCycleTripleB`
   measure-preserving transport, and the chain-level peel induction), PLUS the
   operator-side trace pairing `Σ_j κ_j^k = C_k(K)` (the product-basis Parseval gap,
   `Hurst.CycleTraceIdentification`).  This file supplies the summability side of that
   HasSum completely (`Summable` for every `k ≥ 2` with the interpolation bounds), so the
   exact statement closes the moment the composition identification lands, via
   `HasSum` transport to the identified target.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### The generic interpolation layer for a multiplicity-exact enumeration -/

/-- **Per-entry norm-interpolation bound**: every entry of a multiplicity-exact
enumeration of the compact symmetric kernel operator satisfies `|val j| ≤ hsNorm K`
(the eigenvalue norm bound `‖T v‖ = |μ| ‖v‖` with `‖v‖ > 0`, plus `TOp_norm_le`). -/
theorem abs_le_hsNorm_of_multEnum
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (j : ℕ) : |val j| ≤ hsNorm K := by
  rcases hval j with h0 | hv
  · rw [h0, abs_zero]
    exact hsNorm_nonneg K
  · have hve := hv
    have h2 : (0:ℝ) < ‖vec j‖ := norm_pos_iff.mpr hve.2
    have h3 : ‖(TOpEnd' K hK) (vec j)‖ ≤ ‖TOp K hK‖ * ‖vec j‖ :=
      ContinuousLinearMap.le_opNorm (TOp K hK) (vec j)
    rw [hve.apply_eq_smul, norm_smul, Real.norm_eq_abs,
      mul_comm (|val j|) (‖vec j‖), mul_comm (‖TOp K hK‖) (‖vec j‖)] at h3
    exact ((mul_le_mul_iff_right₀ h2).mp h3).trans (TOp_norm_le hK)

/-- **Norm interpolation per entry**: for `2 ≤ k`,
`|val j| ^ k ≤ hsNorm K ^ (k-2) * val j ^ 2` — the interpolation
`|val| ^ k = |val| ^ (k-2) * |val| ^ 2` with `|val j| ≤ hsNorm K`
(`abs_le_hsNorm_of_multEnum`). -/
theorem pow_abs_le_mul_sq
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (k : ℕ) (hk : 2 ≤ k) (j : ℕ) :
    |val j| ^ k ≤ hsNorm K ^ (k - 2) * val j ^ 2 := by
  have hk2 : (k - 2) + 2 = k := by omega
  have habs : |val j| ≤ hsNorm K := abs_le_hsNorm_of_multEnum hval j
  rw [← hk2, pow_add]
  calc |val j| ^ (k - 2) * |val j| ^ 2
      ≤ hsNorm K ^ (k - 2) * |val j| ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) habs (k - 2))
          (sq_nonneg _)
    _ = hsNorm K ^ (k - 2) * val j ^ 2 := by rw [sq_abs]

/-- The finite interpolation bound: every partial sum of `|val j| ^ k` is at most the
`k`-th power of the kernel HS norm (finite Bessel bound on the square series,
contracted by the interpolation factor). -/
private theorem sum_abs_pow_le_hsNorm_pow
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) (u : Finset ℕ) :
    ∑ j ∈ u, |val j| ^ k ≤ hsNorm K ^ k := by
  have hk2 : (k - 2) + 2 = k := by omega
  have hkey := sum_val_sq_le_hsNorm_sq_of_multEnum hCompact hsym hval hmult u
  calc ∑ j ∈ u, |val j| ^ k
      ≤ ∑ j ∈ u, (hsNorm K ^ (k - 2) * val j ^ 2) :=
        Finset.sum_le_sum (fun j _ => pow_abs_le_mul_sq hval k hk j)
    _ = hsNorm K ^ (k - 2) * ∑ j ∈ u, val j ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ hsNorm K ^ (k - 2) * hsNorm K ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (pow_nonneg (hsNorm_nonneg K) (k - 2))
    _ = hsNorm K ^ ((k - 2) + 2) := (pow_add _ _ _).symm
    _ = hsNorm K ^ k := by rw [hk2]

/-- **The interpolation/summability theorem (general `k ≥ 2`)**: for a multiplicity-exact
enumeration of the compact symmetric kernel operator, the absolute-value power series
`∑ |val j| ^ k` converges for every `k ≥ 2`. -/
theorem summable_abs_pow_of_multEnum
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun j => |val j| ^ k) :=
  summable_of_sum_le (fun j => pow_nonneg (abs_nonneg (val j)) k)
    (fun u => sum_abs_pow_le_hsNorm_pow hCompact hsym hval hmult k hk u)

/-- **The tsum interpolation bound (closed form)**:
`∑' j, |val j| ^ k ≤ hsNorm K ^ k` for every `k ≥ 2`. -/
theorem tsum_abs_pow_le_multEnum
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) :
    ∑' j, |val j| ^ k ≤ hsNorm K ^ k :=
  Real.tsum_le_of_sum_le (fun j => pow_nonneg (abs_nonneg (val j)) k)
    (fun u => sum_abs_pow_le_hsNorm_pow hCompact hsym hval hmult k hk u)

/-- **The interpolated tsum bound (the mission form)**:
`∑' j, |val j| ^ k ≤ hsNorm K ^ (k-2) * ∑' j, val j ^ 2` — `hasSum_le` against the
interpolation-scaled square series (`Summable.const_smul` of the `Summable (λ²)` clause). -/
theorem tsum_abs_pow_le_mul_tsum_sq
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) :
    ∑' j, |val j| ^ k ≤ hsNorm K ^ (k - 2) * ∑' j, val j ^ 2 := by
  have hsq := summable_val_sq_of_multEnum hCompact hsym hval hmult
  refine hasSum_le (fun j => pow_abs_le_mul_sq hval k hk j)
    (summable_abs_pow_of_multEnum hCompact hsym hval hmult k hk).hasSum ?_
  have h2 : HasSum (fun j => hsNorm K ^ (k - 2) • val j ^ 2)
      (hsNorm K ^ (k - 2) • ∑' j, val j ^ 2) :=
    hsq.hasSum.const_smul (hsNorm K ^ (k - 2))
  simpa only [smul_eq_mul] using h2

/-- **Under operator positivity the power series itself converges**: for `hPos : ∀ f,
0 ≤ ⟪T f, f⟫` every enumerated entry is nonnegative (landed `eigenvalue_nonneg_of_pos`),
so `|val j| ^ k = val j ^ k` and `Summable (fun j => val j ^ k)` for every `k ≥ 2`. -/
theorem summable_pow_of_posTOp
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (hPos : ∀ f : L2, 0 ≤ inner ℝ (TOp K hK f) f)
    (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun j => val j ^ k) := by
  have hnn : ∀ j, 0 ≤ val j := by
    intro j
    rcases hval j with h0 | hv
    · rw [h0]
    · exact eigenvalue_nonneg_of_pos hPos (Module.End.hasEigenvalue_of_hasEigenvector hv)
  have hfun : ∀ j, val j ^ k = |val j| ^ k := fun j => by rw [abs_of_nonneg (hnn j)]
  exact ((summable_abs_pow_of_multEnum hCompact hsym hval hmult k hk).hasSum.congr_fun
    hfun).summable

/-- **The consumption bundle**: the multiplicity-exact enumeration exists with, for every
`k ≥ 2`, `Summable (fun j => |val j| ^ k)`, the tsum bound `∑' |val j| ^ k ≤ hsNorm K ^ k`,
and the interpolated form `∑' |val j| ^ k ≤ hsNorm K ^ (k-2) * ∑' j, val j ^ 2`. -/
theorem exists_multiplicity_enumeration_pow_summable
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric) :
    ∃ val : ℕ → ℝ, ∃ vec : ℕ → L2,
      (∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j)) ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
        Nat.card {j : ℕ // val j = μ}
          = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) ∧
      (∀ k : ℕ, 2 ≤ k → Summable (fun j => |val j| ^ k)) ∧
      (∀ k : ℕ, 2 ≤ k → ∑' j, |val j| ^ k ≤ hsNorm K ^ k) ∧
      (∀ k : ℕ, 2 ≤ k → ∑' j, |val j| ^ k ≤ hsNorm K ^ (k - 2) * ∑' j, val j ^ 2) := by
  obtain ⟨val, vec, h1, h2⟩ := exists_multiplicity_enumeration hCompact hsym
  exact ⟨val, vec, h1, h2,
    fun k hk => summable_abs_pow_of_multEnum hCompact hsym h1 h2 k hk,
    fun k hk => tsum_abs_pow_le_multEnum hCompact hsym h1 h2 k hk,
    fun k hk => tsum_abs_pow_le_mul_tsum_sq hCompact hsym h1 h2 k hk⟩

/-! ### The Riesz-instantiated layer: the `k = 2` anchor and the general-`k` HasSum -/

variable (psi c : ℝ) (omega : ℝ → ℝ) (M : ℝ)

/-- **The `k = 2` HasSum anchor at the Riesz kernel (honest form)**: the squared
constructed spectrum `HasSum`s to its own tsum, and the tsum is at most the `k = 2`
weighted Riesz cycle integral
(`weightedRieszCycleIntegral 2 psi c omega = hsNorm K_R ^ 2`,
`Hurst.RieszSpectralTrace`).  The upgrade to the exact
`HasSum … (weightedRieszCycleIntegral 2 psi c omega)` needs the reverse Parseval
inequality `hsNorm K_R² ≤ ∑' val j²` (the kernel expansion `K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)`
in `L²(vol2)`) — the documented boundary, NOT landed. -/
theorem rieszSpectrum_hasSum_two
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
      (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
    ∧ (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
        ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega) :=
  ⟨(rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst).hasSum,
    rieszSpectrum_two_tsum_le_cycleIntegral psi c omega M hpow homega hbdd hg hconst⟩

/-- **The general-`k` HasSum at the Riesz kernel (the honest HasSum-to-the-Riesz-side-limit)**:
for every `k ≥ 2`, the sequence `|rieszSpectrumVal … j| ^ k` `HasSum`s to its own tsum,
and the tsum satisfies the two interpolation bounds

* `∑' j, |val j| ^ k ≤ hsNorm K_R ^ (k-2) * weightedRieszCycleIntegral 2 psi c omega`
  (the `k = 2` anchor contracted by the interpolation factor), and
* `∑' j, |val j| ^ k ≤ hsNorm K_R ^ k` (the closed form).

The `C_k`-exact target (`weightedRieszCycleIntegral k psi c omega`, `k ≥ 3`) is the
documented boundary: gated on the spectral-Calculus composition peel induction
(`Hurst.HSCycleComposition` residue) plus the operator-side trace pairing
(product-basis Parseval, `Hurst.CycleTraceIdentification`). -/
theorem rieszSpectrum_hasSum_general_k
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun j => |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k)
      (∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k)
    ∧ (∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k
        ≤ hsNorm (rieszKernel psi c omega) ^ (k - 2)
          * Hurst.weightedRieszCycleIntegral 2 psi c omega)
    ∧ (∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k
        ≤ hsNorm (rieszKernel psi c omega) ^ k) := by
  have hcompact := isCompactOperator_TOp_riesz (c := c) hpow homega hbdd hg hconst
  have hsym := isSymmetric_TOp_rieszKernel (c := c) hpow homega hbdd hg hconst
  have hentry := rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst
  have hmult : ∀ μ : ℝ, Module.End.HasEigenvalue
      (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
      μ ≠ 0 →
      Nat.card {j : ℕ // rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = μ}
        = Module.finrank ℝ (Module.End.eigenspace
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ) :=
    fun μ hμ hμ0 => rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0
  refine ⟨(summable_abs_pow_of_multEnum hcompact hsym hentry hmult k hk).hasSum, ?_,
    tsum_abs_pow_le_multEnum hcompact hsym hentry hmult k hk⟩
  refine (tsum_abs_pow_le_mul_tsum_sq hcompact hsym hentry hmult k hk).trans ?_
  exact mul_le_mul_of_nonneg_left
    (rieszSpectrum_two_tsum_le_cycleIntegral psi c omega M hpow homega hbdd hg hconst)
    (pow_nonneg (hsNorm_nonneg (rieszKernel psi c omega)) (k - 2))

/-- **The general-`k` power-series convergence under operator positivity** (the
P2-consumption side): with `hPos : ∀ f, 0 ≤ ⟪T_R f, f⟫` the constructed spectrum is
nonnegative entrywise, so `Summable (fun j => val j ^ k)` and the `HasSum` to its own
tsum hold for every `k ≥ 2`, with the interpolation bound
`∑' val j ^ k ≤ hsNorm K_R ^ k`. -/
theorem rieszSpectrum_summable_pow_of_posTOp
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hPos : ∀ f : L2, 0 ≤ inner ℝ
      (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f)
    (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k)
    ∧ HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k)
        (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k)
    ∧ (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k
        ≤ hsNorm (rieszKernel psi c omega) ^ k) := by
  have hcompact := isCompactOperator_TOp_riesz (c := c) hpow homega hbdd hg hconst
  have hsym := isSymmetric_TOp_rieszKernel (c := c) hpow homega hbdd hg hconst
  have hentry := rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst
  have hmult : ∀ μ : ℝ, Module.End.HasEigenvalue
      (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
      μ ≠ 0 →
      Nat.card {j : ℕ // rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = μ}
        = Module.finrank ℝ (Module.End.eigenspace
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ) :=
    fun μ hμ hμ0 => rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0
  have hps := summable_pow_of_posTOp hcompact hsym hentry hmult hPos k hk
  have hnn := rieszSpectrum_nonneg_of_posTOp psi c omega M hpow homega hbdd hg hconst hPos
  have hfun : ∀ j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k
      = |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k :=
    fun j => by rw [abs_of_nonneg (hnn j)]
  have heq : (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k)
      = (∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k) :=
    tsum_congr hfun
  refine ⟨hps, hps.hasSum, ?_⟩
  rw [heq]
  exact tsum_abs_pow_le_multEnum hcompact hsym hentry hmult k hk

end HS

end
