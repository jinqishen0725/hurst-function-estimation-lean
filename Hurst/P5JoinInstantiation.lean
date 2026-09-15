import Hurst.P5SeamClosed
import Hurst.P5L1Joining
import Hurst.GridErrorRate

/-!
# P5 join instantiation: the L1 joining lemma at the seam's `G`

This file instantiates `Hurst.P5L1Joining.logProjection_L1_tendsto_zero` at the
seam's chain objects and composes it with
`Hurst.P5SeamClosed.p5Seam_joinBridge`, producing the exact `hJoin` contract
consumed by `Hurst.P5SeamClosed.logStatistic_knownScaleH_seam`:

* `Pn n = featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))`,
* `G n = p5KnownScaleLogStatistic f r n (δ n) t` (the UNIT-weight log statistic,
  weights `S⁻¹ u_i`),
* `Sψ n = (n δ n) ^ (2 - 2 f t)`, `L n = log n`, `c n = 2 S^ψ log n = seamScaleC`,
* the center `m = E of the spectral statistic` enters only through the explicit
  projection-center band hypothesis `hband` (the file-22-W9 bandwidth datum).

## Exponent bookkeeping (the scale bridge, checked by hand first)

Write `S = n δ n`, `ψ = 2 - 2 f t`, `wSpec i = actualQ1SpectralWeight` and
`wUnit i = S⁻¹ u i` (the `p5KnownScaleLogStatistic` weights).  By
`p5Seam_unitWeight_eq`, `wUnit i = S^(-ψ) * wSpec i`, so

`∑ wUnit² = (S^(-ψ))² ∑ wSpec² = S^{-2ψ} ∑ wSpec²`.

The `hE2`-reduced variance bound (`gaussianLogStatistic_mse` +
`gaussianLogStatistic_variance_sqmass_row_bound` with the per-row bound from
`hE2` via `sqEnergy_row_le`) gives, with
`V n := 4 * gaussianLogSquareVariance * C * (S^(-ψ))² * ∑ wSpec²`,

`E (Ĝ_unit - E Ĝ_unit)² ≤ V n = 4 gSqVar C S^{-2ψ} ∑ wSpec²`.

The joining lemma's closing scale is `S^ψ V / (L d)`, and the cancellation
`S^ψ (S^(-ψ))² = S^(-ψ)` (valid for `S > 0`) lands it as

`S^ψ V / (log n d) = 4 gSqVar C S^{-ψ} ∑ wSpec² / (log n d) ≤ 4 gSqVar C ∑ wSpec² / (log n d)`,

since `0 ≤ S^(-ψ) ≤ 1` once `S ≥ 1` eventually (from `hN`) and `ψ ≥ 0` (from
`hfb : f t < 1`).  The last display tends to zero by `hW0` (`∑ wSpec² → 0`)
divided by `log n * d → ∞`.  So NO extra window hypothesis is needed beyond
`hW0`, `hN`, `hfb` and `hd : 0 < d` — the "window" of the abstract joining
lemma is discharged here from the P5 variance data.

## Hypothesis notes (documented deviations)

* `hSpos : ∀ n, 2 ≤ n → 0 < n δ n` is taken POINTWISE because
  `p5Seam_joinBridge` demands that shape (its `hMean` step needs it at every
  `n`); the seam theorems only carry the eventual `hδpos`, so plugging this
  theorem into `logStatistic_knownScaleH_seam` requires strengthening that one
  datum — recorded here for the upstream caller.
* `hlong : 3 / 4 < f t` is carried for interface parity with the P5 chain (it
  is unused by this L1 bound; the L1 closing only needs `hfb : f t < 1`, which
  is the file-22-W9 `hfb` datum).
* `hband` is the projection-center band `d ≤ E H̃_n ≤ 1 - d` (with
  `E H̃_n = (cσ - E Ĝ_unit)/(2 log n)`), kept explicit as in
  `logProjection_L1_tendsto_zero` — the center depends on the data, and
  discharging it is upstream (file 22 W9).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-- Scale cancellation used twice below: `S^ψ (S^{-ψ})² = S^{-ψ}` for `S > 0`
(both seams of the exponent bookkeeping above reduce to this). -/
private theorem p5Join_pow_mul_pow_neg_sq (S ψ : ℝ) (hS : 0 < S) :
    S ^ ψ * (S ^ (-ψ)) ^ 2 = S ^ (-ψ) := by
  have h1 : S ^ ψ * S ^ (-ψ) = 1 := by
    rw [← Real.rpow_add hS ψ (-ψ), show ψ + -ψ = (0 : ℝ) by ring, Real.rpow_zero]
  rw [pow_two, ← mul_assoc, h1, one_mul]

/-- Pointwise square identity for the two weightings at the seam:
`(S⁻¹ u)² = (S^{-ψ})² (S^{ψ-1} u)²`, i.e. the unit-weight square mass is the
spectral square mass scaled by `S^{-2ψ}`. -/
private theorem p5Join_weight_sq (S u ψ : ℝ) (hS : 0 < S) :
    (S⁻¹ * u) ^ 2 = (S ^ (-ψ)) ^ 2 * (S ^ (ψ - 1) * u) ^ 2 := by
  rw [p5Seam_unitWeight_eq S u ψ hS, mul_pow]

/-- The instantiated variance bound at the seam: `4 gSqVar C S^{-2ψ} ∑ wSpec²`,
i.e. the `hE2`-reduced variance of the UNIT-weight log statistic with the
spectral weight mass factored out (so `hW0` controls it after the `S^ψ`
cancellation of the joining scale). -/
def p5JoinInstantiatedVariance (f : ℝ → ℝ) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (C : ℝ)
    (n : ℕ) : ℝ :=
  4 * gaussianLogSquareVariance * C * (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2 *
    ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2

theorem p5JoinInstantiatedVariance_nonneg (f : ℝ → ℝ) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ)
    (C : ℝ) (hC0 : 0 ≤ C) (n : ℕ) :
    0 ≤ p5JoinInstantiatedVariance f r t δ C n := by
  have h1 : 0 ≤ 4 * gaussianLogSquareVariance * C :=
    mul_nonneg (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg) hC0
  unfold p5JoinInstantiatedVariance
  exact mul_nonneg (mul_nonneg h1 (sq_nonneg _))
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- The joining-scale cancellation at the instantiated variance:
`S^ψ V n = 4 gSqVar C S^{-ψ} ∑ wSpec²` for `S n > 0` — this is the exponent
bookkeeping that turns the window into an `hW0`-controlled quantity. -/
private theorem p5JoinInstantiatedVariance_red (f : ℝ → ℝ) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ)
    (C : ℝ) (n : ℕ) (hS : 0 < (n : ℝ) * δ n) :
    ((n : ℝ) * δ n) ^ (2 - 2 * f t) * (p5JoinInstantiatedVariance f r t δ C n)
      = 4 * gaussianLogSquareVariance * C * ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) *
        ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 := by
  unfold p5JoinInstantiatedVariance
  calc ((n : ℝ) * δ n) ^ (2 - 2 * f t) *
        (4 * gaussianLogSquareVariance * C *
            (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2 *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2)
      = (((n : ℝ) * δ n) ^ (2 - 2 * f t) *
            (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2) *
          (4 * gaussianLogSquareVariance * C *
            ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
              (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) := by ring
    _ = ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) * (4 * gaussianLogSquareVariance * C *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) := by
        rw [p5Join_pow_mul_pow_neg_sq ((n : ℝ) * δ n) (2 - 2 * f t) hS]
    _ = 4 * gaussianLogSquareVariance * C * ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 := by ring

/-- The square-mass bridge `∑ wUnit² = S^{-2ψ} ∑ wSpec²` at the seam weights. -/
private theorem p5Join_sq_mass_bridge (f : ℝ → ℝ) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (n : ℕ)
    (hS : 0 < (n : ℝ) * δ n) :
    ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i) ^ 2
      = (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2 *
        ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 := by
  have hpoint : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i) ^ 2
      = (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2 *
        (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 := by
    intro i
    show (((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i) ^ 2
        = (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2 *
          (((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) *
            actualQ1ChainWeight f r n (δ n) t i) ^ 2
    rw [p5Join_weight_sq _ _ _ hS]
  calc ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i) ^ 2
      = ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2 *
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => hpoint i
    _ = (((n : ℝ) * δ n) ^ (-(2 - 2 * f t))) ^ 2 *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 :=
        (Finset.mul_sum _ _ _).symm

set_option linter.unusedVariables false in
/-- **The L1 joining lemma instantiated at the P5 seam (the deliverable).**

This is `Hurst.P5L1Joining.logProjection_L1_tendsto_zero` instantiated at
`G = p5KnownScaleLogStatistic f r n (δ n) t` (unit weights), `Pn = the D3
observation feature-Gaussian`, `Sψ n = (n δ n)^(2-2 f t)`, `L n = log n`,
composed with `Hurst.P5SeamClosed.p5Seam_joinBridge`: its conclusion is the
EXACT `hJoin` contract consumed by
`Hurst.P5SeamClosed.logStatistic_knownScaleH_seam`,

`∫ ω, |seamScaleC f t δ n (Ĥ_n ω - E Ĥ_n) - -(Ĝ_spec n ω - E Ĝ_spec n)| ∂Pn n → 0`.

The abstract joining lemma's window `S^ψ V / (L d) → 0` is discharged from the
P5 variance data `hW0`/`hE2` (see the module docstring for the exponent
bookkeeping); the projection-center band `hband` and the band width `d` remain
explicit (the center `E H̃_n` depends on the data). -/
theorem logProjection_L1_tendsto_instantiated
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ)
    (hSpos : ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hlong : 3 / 4 < f t)
    (hfb : f t < 1)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hW0 : Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) atTop (𝓝 0))
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 ≤ C)
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n in atTop, d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n (δ n) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) / (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n (δ n) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) / (2 * Real.log n)
        ≤ 1 - d) :
    Tendsto (fun n : ℕ => ∫ ω,
        |seamScaleC f t δ n *
            (p5KnownScaleEstimator f r n (δ n) t cσ ω -
              ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) -
          -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) ω -
            ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
      ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    atTop (𝓝 0) := by
  obtain ⟨C, hC0, hCev⟩ := hE2
  -- eventual basics
  have hev2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := Filter.eventually_ge_atTop 2
  have hSev : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * δ n :=
    Filter.eventually_atTop.mpr ⟨2, fun n hn => hSpos n hn⟩
  have hS1ev : ∀ᶠ n : ℕ in atTop, 1 < (n : ℝ) * δ n := hN.eventually_gt_atTop 1
  -- per-row squared-correlation bound from the hE2 total energy
  have hRow : ∀ᶠ n : ℕ in atTop, ∀ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t j) (actualQ1Coeff n (δ n) t k)) ^ 2 ≤ C := by
    filter_upwards [hCev] with n htot j
    exact sqEnergy_row_le _ C htot (fun i k => sq_nonneg _) j
  -- the variance data of the joining lemma at the unit-weight statistic
  have hMem : ∀ n : ℕ, MemLp (p5KnownScaleLogStatistic f r n (δ n) t) 2
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
    fun n => gaussianLogStatistic_memLp_two
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
      (actualQ1Coeff n (δ n) t) (hane n)
  have hMom : ∀ᶠ n : ℕ in atTop,
      ∫ x, (p5KnownScaleLogStatistic f r n (δ n) t x -
          ∫ y, p5KnownScaleLogStatistic f r n (δ n) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) ^ 2 ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      ≤ p5JoinInstantiatedVariance f r t δ C n := by
    filter_upwards [hRow, hSev] with n hRowN hSn
    have hunfold : p5KnownScaleLogStatistic f r n (δ n) t
        = gaussianLogStatistic
            (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
            (actualQ1Coeff n (δ n) t) := rfl
    rw [hunfold]
    have hwsum := p5Join_sq_mass_bridge f r t δ n hSn
    have h2 : ∫ x, (gaussianLogStatistic
          (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
          (actualQ1Coeff n (δ n) t) x -
        ∫ y, gaussianLogStatistic
          (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
          (actualQ1Coeff n (δ n) t) y ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) ^ 2 ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      = Var[gaussianLogStatistic
          (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
          (actualQ1Coeff n (δ n) t);
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))] := by
      rw [gaussianLogStatistic_mse
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
        (actualQ1Coeff n (δ n) t)
        (∫ y, gaussianLogStatistic
          (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
          (actualQ1Coeff n (δ n) t) y ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        (hane n)]
      rw [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    calc ∫ x, (gaussianLogStatistic
          (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
          (actualQ1Coeff n (δ n) t) x -
        ∫ y, gaussianLogStatistic
          (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
          (actualQ1Coeff n (δ n) t) y ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) ^ 2 ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        = Var[gaussianLogStatistic
            (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
            (actualQ1Coeff n (δ n) t);
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))] := h2
      _ ≤ 4 * gaussianLogSquareVariance * C *
            ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
              (((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t j) ^ 2 :=
          gaussianLogStatistic_variance_sqmass_row_bound
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
            (actualQ1Coeff n (δ n) t) (hane n) C hRowN
      _ = p5JoinInstantiatedVariance f r t δ C n := by
          unfold p5JoinInstantiatedVariance
          rw [hwsum]
          ring
  -- the window: `S^ψ V / (log n d) ≤ 4 gSqVar C ∑ wSpec² / (log n d) → 0`
  have hK0 : 0 ≤ 4 * gaussianLogSquareVariance * C :=
    mul_nonneg (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg) hC0
  have hDen : Tendsto (fun n : ℕ => Real.log (n : ℝ) * d) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const hd
  have hr : Tendsto (fun n : ℕ => 4 * gaussianLogSquareVariance * C *
      (∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) / (Real.log n * d)) atTop (𝓝 0) :=
    (hW0.const_mul (4 * gaussianLogSquareVariance * C)).div_atTop hDen
  have hWin : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 - 2 * f t) *
      (p5JoinInstantiatedVariance f r t δ C n) / (Real.log n * d)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hr
    · filter_upwards [hev2] with n hn2
      exact div_nonneg
        (mul_nonneg (Real.rpow_nonneg (le_of_lt (hSpos n hn2)) _)
          (p5JoinInstantiatedVariance_nonneg f r t δ C hC0 n))
        (mul_nonneg (le_of_lt (Real.log_pos (by exact_mod_cast hn2))) hd.le)
    · filter_upwards [hev2, hS1ev] with n hn2 h1S
      have hSn : 0 < (n : ℝ) * δ n := hSpos n hn2
      have hle : ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) ≤ 1 := by
        have h9 : ((n : ℝ) * δ n) ^ (-(2 - 2 * f t))
            ≤ ((n : ℝ) * δ n) ^ (0 : ℝ) :=
          (Real.rpow_le_rpow_left_iff h1S).mpr (by linarith)
        rwa [Real.rpow_zero] at h9
      have hA0n : 0 ≤ ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hDpos : 0 < Real.log n * d := mul_pos (Real.log_pos (by exact_mod_cast hn2)) hd
      rw [p5JoinInstantiatedVariance_red f r t δ C n hSn]
      refine (div_le_div_iff₀ hDpos hDpos).mpr ?_
      calc (4 * gaussianLogSquareVariance * C * ((n : ℝ) * δ n) ^ (-(2 - 2 * f t)) *
              (∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
                (actualQ1SpectralWeight f r n (δ n) t i) ^ 2)) * (Real.log n * d)
          ≤ (4 * gaussianLogSquareVariance * C * 1 *
              (∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
                (actualQ1SpectralWeight f r n (δ n) t i) ^ 2)) * (Real.log n * d) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK0) hA0n)
              hDpos.le
        _ = (4 * gaussianLogSquareVariance * C *
              (∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
                (actualQ1SpectralWeight f r n (δ n) t i) ^ 2)) * (Real.log n * d) := by
            rw [mul_one]
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [hev2] with n hn
    exact Real.log_pos (by exact_mod_cast hn)
  have hSψpos : ∀ᶠ n : ℕ in atTop, 0 ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t) := by
    filter_upwards [hev2] with n hn
    exact Real.rpow_nonneg (le_of_lt (hSpos n hn)) _
  -- assemble: joining lemma (hSmall shape) → seam bridge → the hJoin contract
  exact p5Seam_joinBridge f hf r t δ cσ hane hSpos
    (logProjection_L1_tendsto_zero
      (Pn := fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      (G := fun n x => p5KnownScaleLogStatistic f r n (δ n) t x)
      cσ
      (Sψ := fun n => ((n : ℝ) * δ n) ^ (2 - 2 * f t))
      (L := fun n => Real.log n)
      (d := fun _ => d)
      (V := p5JoinInstantiatedVariance f r t δ C)
      hMem hMom hLpos hSψpos (Eventually.of_forall fun _ => hd) hband hWin)

end Hurst
