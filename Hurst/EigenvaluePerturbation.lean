import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Hurst.SpectralMatchingSort
import Hurst.TracePowerTransfer

/-!
# Eigenvalue perturbation estimates for real Hermitian matrices

Mathlib has no min-max / Rayleigh variational characterization of eigenvalues
(no `Rayleigh`, `minmax`, `Weyl` material in the matrix folders), so a full
Weyl bound is out of reach here.  This file lands instead:

* the scalar shift of the spectrum, in both signs (pure algebra);
* the PSD dominance lemma: `(A + δ • 1).PosSemidef → ∀ i, -δ ≤ λ_i(A)`;
* the downstream form: `B` PSD and `‖A - B‖₂ ≤ δ` imply `λ_i(A) ≥ -δ`
  for every eigenvalue `λ_i(A)` (the lemma the signed chain needs);
* the op-norm twin of `Hurst.TracePowerTransfer.abs_trace_pow_sub_le`:
  for Hermitian `A B`, `|tr(A^k) - tr(B^k)| ≤ n · k · (max ‖A‖ ‖B‖)^(k-1) · ‖A - B‖₂`
  (the `√n` of the Frobenius version drops because `|tr C| ≤ n ‖C‖₂`).

All operator norms below are the L2 (spectral) operator norm
(`Matrix.Norms.L2Operator` scoped instance).
-/

set_option maxHeartbeats 1000000

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace Hurst

-- probe: algebraMap into matrices is definitionally `scalar`
example (z : ℝ) : algebraMap ℝ (Matrix (Fin 3) (Fin 3) ℝ) z = Matrix.scalar _ z := rfl

variable {n : ℕ}

private theorem algebraMap_eq_scalar (z : ℝ) :
    algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) z = Matrix.scalar (Fin n) z := rfl

private theorem isUnit_neg_iff (M : Matrix (Fin n) (Fin n) ℝ) : IsUnit (-M) ↔ IsUnit M := by
  constructor
  · intro h
    have h2 := IsUnit.neg h
    rwa [neg_neg] at h2
  · exact IsUnit.neg

/-- `‖1‖ = 1` for the L2 operator norm (not an instance: fails on the trivial ring). -/
private theorem l2_opNorm_one [Nonempty (Fin n)] :
    ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ = 1 :=
  CStarRing.norm_one

section SpectrumShift

/-- Shifting a matrix by the scalar `δ • 1` shifts its real spectrum by `δ`. -/
theorem mem_spectrum_add_scalar (A : Matrix (Fin n) (Fin n) ℝ) (μ δ : ℝ)
    (hμ : μ ∈ spectrum ℝ A) : μ + δ ∈ spectrum ℝ (A + Matrix.scalar (Fin n) δ) := by
  rw [spectrum.mem_iff] at hμ ⊢
  have hring : (algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) (μ + δ)
      - (A + Matrix.scalar (Fin n) δ)) = algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) μ - A := by
    rw [map_add, ← algebraMap_eq_scalar]
    abel
  rw [hring]
  exact hμ

/-- The spectrum of `δ • 1 - D` is the reflection of the spectrum of `D` about `δ/2`. -/
theorem mem_spectrum_scalar_sub (D : Matrix (Fin n) (Fin n) ℝ) (δ z : ℝ) :
    z ∈ spectrum ℝ (Matrix.scalar (Fin n) δ - D) ↔ δ - z ∈ spectrum ℝ D := by
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have heq : (algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) z
      - (Matrix.scalar (Fin n) δ - D))
      = -(algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) (δ - z) - D) := by
    rw [map_sub, ← algebraMap_eq_scalar]
    abel
  constructor
  · intro h hu
    exact h (heq.symm ▸ (isUnit_neg_iff _).mpr hu)
  · intro h hu
    apply h
    exact (isUnit_neg_iff _).mp (heq ▸ hu)

end SpectrumShift

/-- Every eigenvalue of a Hermitian matrix is bounded by its L2 operator norm. -/
theorem abs_eigenvalues_le_l2_opNorm {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.IsHermitian)
    (j : Fin n) : |hC.eigenvalues j| ≤ ‖C‖ := by
  have hvn : ‖(hC.eigenvectorBasis j : EuclideanSpace ℝ (Fin n))‖ = 1 :=
    hC.eigenvectorBasis.norm_eq_one j
  have hmul := hC.mulVec_eigenvectorBasis j
  have hrel : ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C)
      (hC.eigenvectorBasis j : EuclideanSpace ℝ (Fin n)))
      = (hC.eigenvalues j : ℝ) • (hC.eigenvectorBasis j : EuclideanSpace ℝ (Fin n)) := by
    have h1 : WithLp.ofLp ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C)
        (hC.eigenvectorBasis j : EuclideanSpace ℝ (Fin n)))
        = WithLp.ofLp ((hC.eigenvalues j : ℝ) • (hC.eigenvectorBasis j
            : EuclideanSpace ℝ (Fin n))) := by
      rw [Matrix.ofLp_toEuclideanCLM, hmul, WithLp.ofLp_smul]
    have h2 := congrArg (WithLp.toLp 2) h1
    rwa [WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h2
  calc |hC.eigenvalues j|
      = ‖(hC.eigenvalues j : ℝ) • (hC.eigenvectorBasis j : EuclideanSpace ℝ (Fin n))‖ := by
        rw [norm_smul, Real.norm_eq_abs, hvn, mul_one]
    _ = ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C)
          (hC.eigenvectorBasis j : EuclideanSpace ℝ (Fin n))‖ := by rw [hrel]
    _ ≤ ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C)‖
          * ‖(hC.eigenvectorBasis j : EuclideanSpace ℝ (Fin n))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖C‖ := by
        rw [Matrix.cstar_norm_def, hvn, mul_one]

section PsdDominance

/-- **PSD dominance (core shift form).** If `A + δ • 1` is positive semidefinite,
then every eigenvalue of `A` is at least `-δ`. -/
theorem eigenvalues_ge_of_add_scalar_posSemidef {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ}
    (hA : A.IsHermitian) (hpsd : (A + Matrix.scalar (Fin n) δ).PosSemidef) (i : Fin n) :
    -δ ≤ hA.eigenvalues i := by
  have hpair := Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hpsd
  have hzero : 0 ≤ hA.eigenvalues i + δ :=
    hpair.2 (mem_spectrum_add_scalar A _ δ (hA.eigenvalues_mem_spectrum_real i))
  linarith

/-- **PSD dominance (downstream form).** If `B` is positive semidefinite and the
L2 operator norm of `A - B` is at most `δ`, then every eigenvalue of `A`
is at least `-δ`. -/
theorem eigenvalues_ge_neg_delta_of_posSemidef_of_norm_le {A B : Matrix (Fin n) (Fin n) ℝ}
    {δ : ℝ} (hB : B.PosSemidef) (hA : A.IsHermitian)
    (hop : ‖A - B‖ ≤ δ) (i : Fin n) : -δ ≤ hA.eigenvalues i := by
  have hD : (B - A).IsHermitian := hB.isHermitian.sub hA
  have hDiag : (Matrix.scalar (Fin n) δ).IsHermitian := Matrix.isHermitian_diagonal _
  -- spectrum of `δ•1 - (B - A)` is nonnegative
  have hsub : spectrum ℝ (Matrix.scalar (Fin n) δ - (B - A)) ⊆ {z : ℝ | 0 ≤ z} := by
    intro z hz
    have hw : δ - z ∈ spectrum ℝ (B - A) := (mem_spectrum_scalar_sub (B - A) δ z).mp hz
    have hw' : δ - z ∈ Set.range hD.eigenvalues := by
      rw [← hD.spectrum_real_eq_range_eigenvalues]; exact hw
    obtain ⟨j, hj⟩ := hw'
    have habs : |δ - z| ≤ ‖B - A‖ := by
      rw [← hj]
      exact abs_eigenvalues_le_l2_opNorm hD j
    have hle : δ - z ≤ δ := le_trans (le_abs_self _) (le_trans habs (by rw [norm_sub_rev]; exact hop))
    show 0 ≤ z
    linarith
  have hspsd : (Matrix.scalar (Fin n) δ - (B - A)).PosSemidef :=
    Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mpr ⟨hDiag.sub hD, hsub⟩
  have hexp : A + Matrix.scalar (Fin n) δ
      = B + (Matrix.scalar (Fin n) δ - (B - A)) := by
    rw [Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j
    · simp [hij]; ring
    · simp [hij]
  have hpsd : (A + Matrix.scalar (Fin n) δ).PosSemidef := by
    rw [hexp]
    exact Matrix.PosSemidef.add hB hspsd
  exact eigenvalues_ge_of_add_scalar_posSemidef hA hpsd i

end PsdDominance

section OpNormTracePowers

/-- The L2 operator norm is power-submultiplicative. -/
theorem norm_pow_le_l2_opNorm (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ s : ℕ, ‖A ^ s‖ ≤ ‖A‖ ^ s
  | 0 => by
      rcases isEmpty_or_nonempty (Fin n) with h | h
      · have h0 : (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
          ext i j
          exact isEmptyElim i
        rw [pow_zero, pow_zero, h0, norm_zero]
        norm_num
      · rw [pow_zero, pow_zero, l2_opNorm_one]
  | s + 1 => by
      calc ‖A ^ (s + 1)‖ = ‖A ^ s * A‖ := by rw [pow_succ]
        _ ≤ ‖A ^ s‖ * ‖A‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖A‖ ^ s * ‖A‖ := mul_le_mul_of_nonneg_right (norm_pow_le_l2_opNorm A s)
            (norm_nonneg A)

/-- Left-multiplication by a power under the L2 operator norm. -/
theorem norm_pow_left_mul_le_l2_opNorm (A Y : Matrix (Fin n) (Fin n) ℝ) :
    ∀ s : ℕ, ‖A ^ s * Y‖ ≤ ‖A‖ ^ s * ‖Y‖
  | 0 => by rw [pow_zero, pow_zero, one_mul, one_mul]
  | s + 1 => by
      have h : A ^ (s + 1) * Y = A ^ s * (A * Y) := by
        rw [pow_succ, mul_assoc]
      calc ‖A ^ (s + 1) * Y‖ = ‖A ^ s * (A * Y)‖ := by rw [h]
        _ ≤ ‖A‖ ^ s * ‖A * Y‖ := norm_pow_left_mul_le_l2_opNorm A (A * Y) s
        _ ≤ ‖A‖ ^ s * (‖A‖ * ‖Y‖) :=
            mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul A Y)
              (pow_nonneg (norm_nonneg A) s)
        _ = ‖A‖ ^ (s + 1) * ‖Y‖ := by rw [pow_succ]; ring

/-- Right-multiplication by a power under the L2 operator norm. -/
theorem norm_mul_pow_right_le_l2_opNorm (X A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ t : ℕ, ‖X * A ^ t‖ ≤ ‖X‖ * ‖A‖ ^ t
  | 0 => by rw [pow_zero, pow_zero, mul_one, mul_one]
  | t + 1 => by
      have h : X * A ^ (t + 1) = X * A ^ t * A := by
        rw [pow_succ, ← mul_assoc]
      calc ‖X * A ^ (t + 1)‖ = ‖X * A ^ t * A‖ := by rw [h]
        _ ≤ ‖X * A ^ t‖ * ‖A‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ (‖X‖ * ‖A‖ ^ t) * ‖A‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_pow_right_le_l2_opNorm X A t)
              (norm_nonneg A)
        _ = ‖X‖ * ‖A‖ ^ (t + 1) := by rw [pow_succ]; ring

/-- The trace of a Hermitian matrix is bounded by `n` times its L2 operator norm. -/
theorem abs_trace_le_card_mul_l2_opNorm {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.IsHermitian) :
    |C.trace| ≤ (n : ℝ) * ‖C‖ := by
  have htr : C.trace = ∑ i : Fin n, (hC.eigenvalues i : ℝ) := by
    simpa using hC.trace_eq_sum_eigenvalues
  have hsum : ∑ i : Fin n, |hC.eigenvalues i| ≤ ∑ _i : Fin n, ‖C‖ :=
    Finset.sum_le_sum fun i _ => abs_eigenvalues_le_l2_opNorm hC i
  calc |C.trace| = |∑ i : Fin n, (hC.eigenvalues i : ℝ)| := by rw [htr]
    _ ≤ ∑ i : Fin n, |hC.eigenvalues i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (n : ℝ) * ‖C‖ := by simpa using hsum

/-- **Op-norm twin of the trace-power transfer estimate.** For Hermitian `A B`,
`|tr(A^k) - tr(B^k)| ≤ n · k · (max ‖A‖ ‖B‖)^(k-1) · ‖A - B‖₂`.
The dimension factor is the sharp `n` (vs. the `√n`-per-unit version for the
Frobenius norm in `Hurst.TracePowerTransfer`). -/
theorem abs_trace_pow_sub_le_l2_opNorm {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : ℕ) :
    |Matrix.trace (A ^ k) - Matrix.trace (B ^ k)|
      ≤ (n : ℝ) * (k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) := by
  have hC : ((A ^ k - B ^ k) : Matrix (Fin n) (Fin n) ℝ).IsHermitian :=
    (hA.pow k).sub (hB.pow k)
  have htrace : Matrix.trace (A ^ k) - Matrix.trace (B ^ k)
      = Matrix.trace (A ^ k - B ^ k) := by
    rw [Matrix.trace_sub]
  -- norm bound on the telescoped difference
  have hnorm : ‖A ^ k - B ^ k‖ ≤ (k : ℝ) * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
    have htel := matrix_pow_sub_pow_telescope A B k
    have hstep : ∀ t ∈ Finset.range k,
        ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖ ≤ (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
      intro t ht
      have htlt : t < k := Finset.mem_range.mp ht
      have h1 : ‖A ^ (k - 1 - t) * (A - B)‖ ≤ ‖A‖ ^ (k - 1 - t) * ‖A - B‖ :=
        norm_pow_left_mul_le_l2_opNorm A (A - B) _
      have h2 : (‖A‖ ^ (k - 1 - t) * ‖A - B‖) * ‖B‖ ^ t
          ≤ (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
        have hp := pow_mul_pow_le_max_pow ‖A‖ ‖B‖ (norm_nonneg A) (norm_nonneg B) k t htlt
        have e1 : (‖A‖ ^ (k - 1 - t) * ‖A - B‖) * ‖B‖ ^ t
            = (‖A‖ ^ (k - 1 - t) * ‖B‖ ^ t) * ‖A - B‖ :=
          mul_right_comm _ _ _
        rw [e1]
        exact mul_le_mul_of_nonneg_right hp (norm_nonneg (A - B))
      calc ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖
          ≤ ‖A ^ (k - 1 - t) * (A - B)‖ * ‖B‖ ^ t := by
            refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
            exact mul_le_mul_of_nonneg_left (norm_pow_le_l2_opNorm B t)
              (norm_nonneg (A ^ (k - 1 - t) * (A - B)))
        _ ≤ (‖A‖ ^ (k - 1 - t) * ‖A - B‖) * ‖B‖ ^ t :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg B) t)
        _ ≤ (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := h2
    calc ‖A ^ k - B ^ k‖ = ‖∑ t ∈ Finset.range k, A ^ (k - 1 - t) * (A - B) * B ^ t‖ := by
          rw [htel]
        _ ≤ ∑ t ∈ Finset.range k, ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖ := norm_sum_le _ _
        _ ≤ ∑ t ∈ Finset.range k, (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ :=
            Finset.sum_le_sum fun t ht => hstep t ht
        _ = (k : ℝ) * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
          ring
  calc |Matrix.trace (A ^ k) - Matrix.trace (B ^ k)|
      = |Matrix.trace (A ^ k - B ^ k)| := by rw [htrace]
    _ ≤ (n : ℝ) * ‖A ^ k - B ^ k‖ := abs_trace_le_card_mul_l2_opNorm hC
    _ ≤ (n : ℝ) * (k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) := by
        exact mul_le_mul_of_nonneg_left hnorm (by positivity)

end OpNormTracePowers

end Hurst
