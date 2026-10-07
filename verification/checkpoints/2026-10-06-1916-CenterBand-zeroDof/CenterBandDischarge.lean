import Mathlib.Topology.Algebra.Order.Field

import Hurst.FeasibleRates
import Hurst.FeatureRowNondegenerate
import Hurst.LocalWeights
import Hurst.VaryingIncrement

/-!
# The center-band discharge: the calibrated ratio tends to `f t`

This file resolves the `hband` data premise (file-22-W9 center calibration) of
the feasible endpoint.  For EVERY fixed `cσ` (the constant contributes
`cσ / (2 log n) → 0`) and the explicit choice `d := (1 - f t) / 2`, the band
condition

`d ≤ (cσ - E Ĝ_n) / (2 log n) ≤ 1 - d`  eventually

holds, because the ratio tends to `f t ∈ (3 / 4, 1)`.

## Math first (the contract; deviations written back below)

With `H = midpointSampleHurst f hf.1 n`, `w_j = localPolynomialWeights` at the
active indices, and `inc_j = gridStrideFirstActual n 1 H (idx j)`:

1. **Exact expectation decomposition** (`centerBand_expectation_decomp`):
   `E Ĝ_n = ∑_j w_j (-2 H_j log n + log ‖inc_j‖² + gLSM)`, from
   `gaussianLogStatistic_expectation` (GaussianLog:153) plus the exact
   identity `gridStrideFirst_feature_identity` (the coefficient combination is
   the positive scalar `(1/n)^{H_j}` times the never-vanishing increment of
   task 1) — `log ‖combo_j‖² = -2 H_j log n + log ‖inc_j‖²` EXACTLY.

2. **The three error terms are `o(log n)`**:
   - `∑ w_j = 1` and `∑ |w_j| ≤ C_w` (k = 0 moment + stability of
     `localPolynomialWeights_uniform_stability`, eventual at `N₀ ≤ n δ`);
   - `|H_j - f t| ≤ D (1+M) δ` on the active set (Lipschitz from
     `hurstHolder_uniform_lower_derivative_lipschitz`, `|grid - t| < δ`);
   - `|log ‖inc_j‖²| ≤ 10 ε_n` with `ε_n = C₀ D (1+M) n^{b-1} → 0`
     (`normalizedVaryingIncrement_uniform_remainder` +
     `log_norm_square_error_from_unit`, step bound `|H_r - H_l| ≤ D(1+M)/n`).

   Hence `E Ĝ_n = -2 f t log n + η_n` with `|η_n| ≤ K` bounded, and the ratio
   equals `f t + (cσ - η_n)/(2 log n) → f t`.

3. **Band selection**: `d := (1 - f t)/2` satisfies `d < f t < 1 - d`
   (from `3/4 < f t < 1`), so the ratio is eventually in `[d, 1 - d]`.

Deviation from the task-book sketch: the sketch routed the log-mean estimate
through the pair law (`varyingPair_log_mean_from_remainder`); the landed route
is shorter — the Gaussian expectation formula reduces everything to the
deterministic norm `‖inc_j‖`, so only `log_norm_square_error_from_unit` is
needed (no pair law).  No step was refuted; the conclusion is the advertised
one with `cσ` FREE (any fixed real) and `d` explicit.
-/

set_option maxHeartbeats 1200000

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Real
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## The exact expectation decomposition -/

/-- The log-scale statistic's expectation decomposes over the active rows into
the exact grid-log factor `-2 H_j log n`, the increment log (controlled
later), and the χ² log-mean. -/
theorem centerBand_expectation_decomp (p M : ℝ)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (n : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ) :
    ∫ y, p5KnownScaleLogStatistic f r n δ t y ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) =
      ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j) *
          (-(2 * (midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ) *
              Real.log (n : ℝ)) +
            Real.log (‖gridStrideFirstActual n 1
              (midpointSampleHurst f hf.1 n) (localWeightActiveIndex n 1 δ t j)‖ ^ 2) +
            gaussianLogSquareMean) := by
  have hnR : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hS : ((n : ℝ) * δ) ≠ 0 := mul_ne_zero hnR hδ.ne'
  have hane : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t j i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 :=
    fun j => actualQ1_hane_discharged f hf n hn δ t j
  have hexph := gaussianLogStatistic_expectation
    (v := actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    (w := fun i => ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t i)
    (a := actualQ1Coeff n δ t) hane
  show ∫ y, gaussianLogStatistic
    (fun i => ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t i)
    (actualQ1Coeff n δ t) y ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) = _
  rw [hexph]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
      = localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j) := by
    rw [actualQ1ChainWeight, inv_mul_cancel_left₀ hS]
  have hinc0 : (0 : ℝ) < ‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 δ t j)‖ :=
    norm_pos_iff.mpr (gridStrideFirstActual_ne_zero n 1 hn (by norm_num)
      (midpointSampleHurst f hf.1 n) (localWeightActiveIndex n 1 δ t j))
  have hbase : (0 : ℝ) < (((1 : ℕ) : ℝ) / (n : ℝ)) :=
    div_pos (by norm_num) (by exact_mod_cast hn)
  have hrpow : (0 : ℝ) < (((1 : ℕ) : ℝ) / (n : ℝ)) ^ (midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ) :=
    Real.rpow_pos_of_pos hbase _
  -- normalize the coefficient/observation defs, then cancel the weight
  simp only [actualQ1Coeff, actualQ1Obs]
  rw [hw]
  -- the combination identity, applied to the expectation sum
  rw [gridStrideFirst_feature_identity n 1 hn (by norm_num)
    (midpointSampleHurst f hf.1 n) (localWeightActiveIndex n 1 δ t j)]
  -- log of the scaled increment norm, split into factors
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrpow.le, mul_pow,
    Real.log_mul (pow_pos hrpow 2).ne' (pow_ne_zero 2 hinc0.ne'), Real.log_pow,
    Real.log_rpow hbase,
    show ((1 : ℕ) : ℝ) / (n : ℝ) = ((n : ℝ))⁻¹ from by norm_num,
    Real.log_inv (n : ℝ)]
  ring

/-! ## The increment log bound (uniform over the active rows) -/

/-- At a fixed `n`, every active row's normalized increment has log-norm-square
within `10 ε` of zero, where `ε = C₀ D (1+M) n^{b-1}` is the varying-minus-
frozen remainder at the Lipschitz step bound `B = D (1+M)`. -/
theorem centerBand_increment_log_bound
    (p M C₀ D a b : ℝ)
    (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ D)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (hlip : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      |f y - f x| ≤ D * (1 + M) * |y - x|)
    (hrem : ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s ℓ B : ℝ, |s + ℓ| ≤ 1 → 0 < ℓ → ℓ ≤ 1 → 0 ≤ B → |(k : ℝ) - h| ≤ B * ℓ →
      ‖normalizedVaryingIncrement h k s ℓ - normalizedFrozenIncrement h s ℓ‖ ≤
        C₀ * B * ℓ ^ (1 - b))
    (n : ℕ) (hn0 : 0 < n) (δ t : ℝ)
    (j : Fin (localWeightActiveSet n 1 δ t).card)
    (hεhalf : C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1)) ≤ 1 / 2) :
    |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
        (localWeightActiveIndex n 1 δ t j)‖ ^ 2)| ≤
      10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1))) := by
  set H := midpointSampleHurst f hf.1 n with hHdef
  set i₀ := localWeightActiveIndex n 1 δ t j with hi₀
  have hnR : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn0.ne'
  have hLv : (strideFirstLeft n 1 i₀).val = i₀.val := rfl
  have hℓ : (0 : ℝ) < ((1 : ℕ) : ℝ) / n :=
    div_pos (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) (by exact_mod_cast hn0)
  have hℓ1 : (((1 : ℕ) : ℝ) / n) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn0 : (0 : ℝ) < n)]
    exact_mod_cast hn0
  have hgl : (grid n (strideFirstLeft n 1 i₀).val) ∈ Ioo (0 : ℝ) 1 :=
    grid_mem n _ hn0 (strideFirstLeft n 1 i₀).isLt
  have hgr : (grid n (strideFirstRight n 1 i₀).val) ∈ Ioo (0 : ℝ) 1 :=
    grid_mem n _ hn0 (strideFirstRight n 1 i₀).isLt
  have hstep1 : (grid n (strideFirstRight n 1 i₀).val)
      = (grid n i₀.val) + ((1 : ℕ) : ℝ) / n := grid_stride_first_step n 1 i₀
  have hbandL : ((H (strideFirstLeft n 1 i₀)) : ℝ) ∈ Icc a b := hF hgl
  have hbandR : ((H (strideFirstRight n 1 i₀)) : ℝ) ∈ Icc a b := hF hgr
  have hv : |(grid n (strideFirstRight n 1 i₀).val)
        - (grid n (strideFirstLeft n 1 i₀).val)| = ((1 : ℕ) : ℝ) / n := by
    rw [hstep1, hLv, add_sub_cancel_left, abs_of_pos hℓ]
  have hstep : |((H (strideFirstRight n 1 i₀)) : ℝ) - ((H (strideFirstLeft n 1 i₀)) : ℝ)|
      ≤ (D * (1 + M)) * (((1 : ℕ) : ℝ) / n) := by
    have hfL := hlip (grid n (strideFirstLeft n 1 i₀).val) hgl
      (grid n (strideFirstRight n 1 i₀).val) hgr
    calc |((H (strideFirstRight n 1 i₀)) : ℝ) - ((H (strideFirstLeft n 1 i₀)) : ℝ)|
        = |f (grid n (strideFirstRight n 1 i₀).val)
            - f (grid n (strideFirstLeft n 1 i₀).val)| := rfl
      _ ≤ (D * (1 + M)) * |(grid n (strideFirstRight n 1 i₀).val)
            - (grid n (strideFirstLeft n 1 i₀).val)| := hfL
      _ = (D * (1 + M)) * (((1 : ℕ) : ℝ) / n) := by rw [hv]
  have hsle : |(grid n i₀.val) + ((1 : ℕ) : ℝ) / n| ≤ 1 := by
    rw [← hstep1, abs_of_pos hgr.1]
    exact le_of_lt hgr.2
  have hremv := hrem (H (strideFirstLeft n 1 i₀)) (H (strideFirstRight n 1 i₀))
    hbandL hbandR (grid n i₀.val) (((1 : ℕ) : ℝ) / n) (D * (1 + M)) hsle hℓ hℓ1
    (by positivity : (0 : ℝ) ≤ D * (1 + M)) hstep
  have hscalar : (((1 : ℕ) : ℝ) / n) ^ (1 - b) = ((n : ℝ) ^ (b - 1)) := by
    rw [show (((1 : ℕ) : ℝ) / n) = ((n : ℝ))⁻¹ from by norm_num,
      show (b - 1) = -(1 - b) from by ring,
      ← Real.rpow_neg_eq_inv_rpow]
  rw [hscalar] at hremv
  have hfroz : ‖normalizedFrozenIncrement (H (strideFirstLeft n 1 i₀))
      (grid n i₀.val) (((1 : ℕ) : ℝ) / n)‖ = 1 :=
    normalizedFrozenIncrement_norm _ _ _ hℓ
  exact log_norm_square_error_from_unit
    (normalizedFrozenIncrement (H (strideFirstLeft n 1 i₀)) (grid n i₀.val)
      (((1 : ℕ) : ℝ) / n))
    (normalizedVaryingIncrement (H (strideFirstLeft n 1 i₀))
      (H (strideFirstRight n 1 i₀)) (grid n i₀.val) (((1 : ℕ) : ℝ) / n))
    (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1)))
    (by
      have h1 : (0 : ℝ) ≤ ((n : ℝ) ^ (b - 1)) :=
        Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le n)) _
      positivity)
    hfroz hremv hεhalf


/-! ## The ratio limit and the band discharge -/

/-- **The calibrated ratio tends to `f t`.**  At the feasible bandwidth
`δ n = n ^ (-γ)`, `(cσ - E Ĝ_n) / (2 log n) → f t` for EVERY fixed `cσ`,
with all internal estimates from the expectation decomposition, the weight
stability package, the Hölder-Lipschitz step bound, and the increment log
bound. -/
theorem centerBand_ratio_tendsto
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (γ cσ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Tendsto (fun n : ℕ =>
      (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
        (2 * Real.log n)) atTop (𝓝 (f t)) := by
  -- the three uniform constants
  obtain ⟨D, hD0, hD⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  have hk0 : (0 : ℕ) < Nat.floor p := Nat.floor_pos.mpr hp
  have hlip : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      |f y - f x| ≤ D * (1 + M) * |y - x| := by
    intro x hx y hy
    have hh := hD M hM f hf 0 hk0 x hx y hy
    simpa only [iteratedDeriv_zero] using hh
  obtain ⟨C₀, hC₀0, hrem⟩ := normalizedVaryingIncrement_uniform_remainder a b ha hb hab
  obtain ⟨N₀, hN₀, Cw, hCw, hstab⟩ := localPolynomialWeights_uniform_stability r 1
  -- the eventual data
  have hδt : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-γ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_of_atTop (fun n : ℕ => (n : ℝ)) (-γ)
      (by linarith) tendsto_natCast_atTop_atTop
  have hSt : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 - γ))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hεt : Tendsto (fun n : ℕ => ((n : ℝ) ^ (b - 1))) atTop (𝓝 0) :=
    tendsto_rpow_neg_of_atTop (fun n : ℕ => (n : ℝ)) (b - 1)
      (by linarith) tendsto_natCast_atTop_atTop
  have hlogt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnlgt : Tendsto (fun n : ℕ => Real.log n / ((n : ℝ) ^ γ)) atTop (𝓝 0) := by
    simpa only [pow_one] using nat_log_power_div_rpow_tendsto γ hγ0 1
  have hεpt : Tendsto (fun n : ℕ => C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hεt.const_mul (C₀ * (D * (1 + M)))
  set K : ℝ := 2 * |cσ| + |gaussianLogSquareMean|
    + 2 * (Cw * D * (1 + M)) + 10 * (Cw * C₀ * D * (1 + M)) with hKdef
  -- the key eventual bound
  have hkey : ∀ᶠ n : ℕ in atTop,
      |cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        - 2 * f t * Real.log n| ≤ K := by
    filter_upwards [eventually_ge_atTop 1,
      hδt.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      hSt.eventually_ge_atTop N₀,
      hεpt.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      hεt.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hnlgt.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with
      n hn1 hδ12 hN₀S hεhalf hε1lt hnlg
    have hn0 : 0 < n := hn1
    have hn1R : ((1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) ≤ n := le_trans (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)) hn1R
    have hδpos : (0 : ℝ) < ((n : ℝ) ^ (-γ)) := Real.rpow_pos_of_pos (by exact_mod_cast hn0) _
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hNS : N₀ ≤ n * ((n : ℝ) ^ (-γ)) := hN₀S.trans_eq
      (show ((n : ℝ) ^ (1 - γ)) = n * ((n : ℝ) ^ (-γ)) from by
        have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
        rw [show (1 - γ : ℝ) = 1 + (-γ) from by ring, Real.rpow_add hn0R,
          Real.rpow_one])
    obtain ⟨hdet, hwbound, hwabsum, hwsum⟩ := hstab n hn0 (by omega) ((n : ℝ) ^ (-γ)) t
      hδpos hδ12.le htIcc hNS
    have hE := centerBand_expectation_decomp p M f hf r n hn0 ((n : ℝ) ^ (-γ)) t hδpos
    -- unit sum over the active window
    have hw1 : ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
          (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j) = 1 := by
      have hmom := hwsum ⟨0, by omega⟩
      simp only [pow_zero, mul_one] at hmom
      have hbr := localPolynomialWeights_sum_active r n 1 ((n : ℝ) ^ (-γ)) t
        (fun _ => (1 : ℝ))
      simp only [mul_one] at hbr
      rw [← hbr]
      exact hmom
    -- absolute-sum bound over the active window
    have hwabs : ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
          (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)| ≤ Cw := by
      have h1 : ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)|
          = ∑ x : {i // i ∈ localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t},
              |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t x.val| := by
        simpa only [localWeightActiveIndex] using
          (localWeightActiveEquiv n 1 ((n : ℝ) ^ (-γ)) t).sum_comp
            (fun x => |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t x.val|)
      rw [h1, Finset.sum_coe_sort (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t)
        (fun i => |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t i|)]
      exact (Finset.sum_mono_set_of_nonneg
        (fun i => abs_nonneg _) (Finset.subset_univ _)).trans hwabsum
    -- rowwise closeness of H to f t on the active window
    have hclose : ∀ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        |(midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
          - f t| ≤ D * (1 + M) * ((n : ℝ) ^ (-γ)) := by
      intro j
      have hmem0 : |(grid n (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).val - t)
          / ((n : ℝ) ^ (-γ))| < 1 := by
        simpa only [localWeightActiveSet, Finset.mem_filter, Finset.mem_univ, true_and]
          using localWeightActiveIndex_mem n 1 ((n : ℝ) ^ (-γ)) t j
      rw [abs_div, abs_of_pos hδpos] at hmem0
      have hglt : |(grid n (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).val - t)|
          < ((n : ℝ) ^ (-γ)) := (div_lt_one hδpos).mp hmem0
      have hgrid : (grid n (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).val)
          ∈ Ioo (0 : ℝ) 1 :=
        grid_mem n _ hn0 (lt_of_lt_of_le
          (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).isLt (by omega))
      have hfL := hlip t ht
        (grid n (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).val) hgrid
      show |f (grid n (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).val) - f t| ≤ _
      calc |f (grid n (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).val) - f t|
          ≤ D * (1 + M) * |(grid n (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j).val)
              - t| := hfL
        _ ≤ D * (1 + M) * ((n : ℝ) ^ (-γ)) :=
            mul_le_mul_of_nonneg_left hglt.le (by positivity)
    -- rowwise increment log bound
    have hLb : ∀ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)| ≤
          10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1))) :=
      fun j => centerBand_increment_log_bound p M C₀ D a b hM hC₀0 hD0.le f hf hF hlip hrem
        n hn0 ((n : ℝ) ^ (-γ)) t j hεhalf.le
    -- the recentered sum identity
    have hsumH : ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * (midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
        - f t = ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * ((midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
            - f t) := by
      have hsplit : ∀ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * (midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
          - f t * localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          = localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
            * ((midpointSampleHurst f hf.1 n
                (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
              - f t) := fun j => by ring
      calc ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
            localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
            * (midpointSampleHurst f hf.1 n
                (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
          - f t = (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * (midpointSampleHurst f hf.1 n
                  (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ))
            - f t * 1 := by rw [mul_one]
        _ = (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * (midpointSampleHurst f hf.1 n
                  (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ))
            - f t * ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
                localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j) := by
              rw [hw1]
        _ = ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              (localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * (midpointSampleHurst f hf.1 n
                  (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
              - f t * localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        _ = _ := Finset.sum_congr rfl fun j _ => hsplit j
    -- bound the two sums
    have hs1 : |∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * ((midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
            - f t)| ≤ Cw * (D * (1 + M)) * ((n : ℝ) ^ (-γ)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
            |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
            * ((midpointSampleHurst f hf.1 n
                (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
              - f t)|
          ≤ ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)|
              * (D * (1 + M) * ((n : ℝ) ^ (-γ))) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact (abs_mul _ _).trans_le
              (mul_le_mul_of_nonneg_left (hclose j) (abs_nonneg _))
        _ = (D * (1 + M) * ((n : ℝ) ^ (-γ))) * ∑ j : Fin (localWeightActiveSet n 1
              ((n : ℝ) ^ (-γ)) t).card, |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)| := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        _ ≤ (D * (1 + M) * ((n : ℝ) ^ (-γ))) * Cw := by
            exact mul_le_mul_of_nonneg_left hwabs
              (mul_nonneg (mul_nonneg hD0.le (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hM))
                (Real.rpow_nonneg hnpos _))
        _ = Cw * (D * (1 + M)) * ((n : ℝ) ^ (-γ)) := by ring
    have hs2 : |∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)|
        ≤ Cw * 10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
            |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
            * Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)|
          ≤ ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)|
              * (10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1)))) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact (abs_mul _ _).trans_le
              (mul_le_mul_of_nonneg_left (hLb j) (abs_nonneg _))
        _ = (10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1)))) *
              ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
                |localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)| := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        _ ≤ (10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1)))) * Cw := by
            exact mul_le_mul_of_nonneg_left hwabs
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10)
                (mul_nonneg (mul_nonneg hC₀0
                  (mul_nonneg hD0.le (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hM)))
                  (Real.rpow_nonneg hnpos _)))
        _ = Cw * 10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1))) := by ring
    -- the expanded expectation
    have hsumexp : ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * (-(2 * (midpointSampleHurst f hf.1 n
                (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
              * Real.log (n : ℝ))
            + Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)
            + gaussianLogSquareMean)
        = -(2 * Real.log (n : ℝ)) * (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * (midpointSampleHurst f hf.1 n
                  (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ))
          + ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)
          + gaussianLogSquareMean := by
      have hper : ∀ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * (-(2 * (midpointSampleHurst f hf.1 n
                (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
              * Real.log (n : ℝ))
            + Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)
            + gaussianLogSquareMean)
          = -(2 * Real.log (n : ℝ)) * (localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * (midpointSampleHurst f hf.1 n
                  (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ))
            + (localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)
              + localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j) * gaussianLogSquareMean) :=
        fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => hper j,
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hw1, one_mul]
      ring
    -- numeric bounds closing the constant K
    have hEqlog : Real.log n * ((n : ℝ) ^ (-γ)) = Real.log n / ((n : ℝ) ^ γ) := by
      rw [div_eq_inv_mul, ← Real.rpow_neg hnpos, mul_comm]
    have hlog1 : 2 * Real.log n * ((n : ℝ) ^ (-γ)) ≤ 2 := by
      have h2 := mul_le_mul_of_nonneg_left hnlg.le (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * Real.log n * ((n : ℝ) ^ (-γ))
          = 2 * (Real.log n * ((n : ℝ) ^ (-γ))) := by ring
        _ = 2 * (Real.log n / ((n : ℝ) ^ γ)) := by rw [hEqlog]
        _ ≤ 2 * 1 := by linarith [h2]
        _ = 2 := by norm_num
    have hε1 : ((n : ℝ) ^ (b - 1)) ≤ 1 := hε1lt.le
    -- triangle assembly
    have htri : ∀ x y z w : ℝ, |x + y - z - w| ≤ |x| + |y| + |z| + |w| := by
      intro x y z w
      calc |x + y - z - w| = |(x + y) + (-(z + w))| := by congr 1; ring
        _ ≤ |x + y| + |-(z + w)| := abs_add_le _ _
        _ = |x + y| + |z + w| := by rw [abs_neg]
        _ ≤ (|x| + |y|) + (|z| + |w|) := add_le_add (abs_add_le x y) (abs_add_le z w)
        _ = |x| + |y| + |z| + |w| := by ring
    have hlnn : (0 : ℝ) ≤ Real.log n := by
      exact Real.log_nonneg (by exact_mod_cast hn1)
    have hA : |2 * Real.log n * (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * ((midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
            - f t))| ≤ 2 * (Cw * D * (1 + M)) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlnn)]
      calc 2 * Real.log n * |∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
            localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
            * ((midpointSampleHurst f hf.1 n
                (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
              - f t)|
          ≤ 2 * Real.log n * (Cw * (D * (1 + M)) * ((n : ℝ) ^ (-γ))) :=
              mul_le_mul_of_nonneg_left hs1 (by linarith)
        _ = Cw * (D * (1 + M)) * (2 * Real.log n * ((n : ℝ) ^ (-γ))) := by ring
        _ ≤ Cw * (D * (1 + M)) * 2 := mul_le_mul_of_nonneg_left hlog1 (by positivity)
        _ = 2 * (Cw * D * (1 + M)) := by ring
    have hB : |∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
            (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
          * Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)|
        ≤ 10 * (Cw * C₀ * D * (1 + M)) := by
      calc _ ≤ Cw * 10 * (C₀ * (D * (1 + M)) * ((n : ℝ) ^ (b - 1))) := hs2
        _ = 10 * (Cw * C₀ * D * (1 + M)) * ((n : ℝ) ^ (b - 1)) := by ring
        _ ≤ 10 * (Cw * C₀ * D * (1 + M)) * 1 :=
              mul_le_mul_of_nonneg_left hε1 (by positivity)
        _ = 10 * (Cw * C₀ * D * (1 + M)) := by ring
    calc |cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
          - 2 * f t * Real.log n|
        = |cσ + 2 * Real.log n * (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * ((midpointSampleHurst f hf.1 n
                  (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
                - f t))
            - (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
                localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
                * Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                    (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2))
            - gaussianLogSquareMean| := by
          rw [hE, hsumexp, ← hsumH]
          ring
      _ ≤ |cσ| + |2 * Real.log n * (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * ((midpointSampleHurst f hf.1 n
                  (strideFirstLeft n 1 (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) : ℝ)
                - f t))|
          + |∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              localPolynomialWeights r n 1 ((n : ℝ) ^ (-γ)) t
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
              * Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)‖ ^ 2)|
          + |gaussianLogSquareMean| :=
              htri cσ _ _ gaussianLogSquareMean
      _ ≤ K := by
          rw [hKdef]
          have h1 := abs_nonneg cσ
          have h2 := abs_nonneg gaussianLogSquareMean
          linarith
  -- squeeze and conclude
  have hhalf : Tendsto (fun n : ℕ => (K / 2) * ((Real.log n)⁻¹)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hlogt).const_mul (K / 2)
  have hBdiv : Tendsto (fun n : ℕ => K / (2 * Real.log n)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hhalf
    filter_upwards [eventually_ge_atTop 1] with n _
    field_simp
  have habs : ∀ᶠ n : ℕ in atTop,
      |(cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
        / (2 * Real.log n) - f t| ≤ K / (2 * Real.log n) := by
    filter_upwards [hkey, eventually_ge_atTop 3] with n hK hn3
    have h1n : (1 : ℝ) < n := by
      have h3 : ((3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn3
      have h13 : ((1 : ℝ)) < ((3 : ℕ) : ℝ) := by norm_num
      linarith
    have h2l : (0 : ℝ) < 2 * Real.log n := by
      have := Real.log_pos h1n
      linarith
    have hnum : (cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
        / (2 * Real.log n) - f t
      = (cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        - f t * (2 * Real.log n)) / (2 * Real.log n) := by
      rw [div_sub' h2l.ne']
      ring
    rw [hnum, abs_div, abs_of_pos h2l,
      show (f t * ((2 : ℝ) * Real.log n)) = 2 * f t * Real.log n from by ring]
    exact div_le_div_of_nonneg_right hK h2l.le
  have habsT : Tendsto (fun n : ℕ =>
      |(cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
        / (2 * Real.log n) - f t|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => abs_nonneg
      ((cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
        / (2 * Real.log n) - f t)) habs hBdiv
  have hsub : Tendsto (fun n : ℕ => (cσ - (∫ y, p5KnownScaleLogStatistic f r n
        ((n : ℝ) ^ (-γ)) t y ∂ featureGaussian (actualQ1Obs f n
          (midpointSampleHurst f hf.1 n)))) / (2 * Real.log n) - f t) atTop (𝓝 0) :=
    tendsto_zero_iff_abs_tendsto_zero
      (fun n : ℕ => (cσ - (∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
          / (2 * Real.log n) - f t) |>.mpr habsT
  have hl : (fun n : ℕ => f t + ((cσ - (∫ y, p5KnownScaleLogStatistic f r n
          ((n : ℝ) ^ (-γ)) t y ∂ featureGaussian (actualQ1Obs f n
            (midpointSampleHurst f hf.1 n)))) / (2 * Real.log n) - f t))
      =ᶠ[atTop] (fun n : ℕ => (cσ - (∫ y, p5KnownScaleLogStatistic f r n
          ((n : ℝ) ^ (-γ)) t y ∂ featureGaussian (actualQ1Obs f n
            (midpointSampleHurst f hf.1 n)))) / (2 * Real.log n)) :=
    Eventually.of_forall fun n => by ring
  refine Tendsto.congr' hl ?_
  have hadd := Tendsto.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => f t) atTop (𝓝 (f t))) hsub
  simpa only [add_zero] using hadd

/-! ## The band discharge -/

/-- **The `hband` premise, discharged with the explicit band `d = (1 - f t)/2`
and EVERY fixed `cσ`.**  The calibrated ratio tends to `f t ∈ (3/4, 1)`, and
`(1 - f t)/2 < f t < 1 - (1 - f t)/2` by arithmetic, so the band holds
eventually. -/
theorem centerBand_hband_discharged
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (γ cσ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hlong : 3 / 4 < f t) :
    ∀ᶠ n : ℕ in atTop,
      (1 - f t) / 2 ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
        (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
        (2 * Real.log n) ≤ 1 - (1 - f t) / 2 := by
  have hft : f t ∈ Ioo (0 : ℝ) 1 := hf.1 ht
  have hu1 : 0 < 1 - f t := by linarith [hft.2]
  have hdlow : (1 - f t) / 2 < f t := by
    have h3 : (3 : ℝ) * f t > 1 := by nlinarith
    nlinarith
  have hdhigh : f t < 1 - (1 - f t) / 2 := by
    have hkey2 : f t < 1 := hft.2
    nlinarith
  have hratio := centerBand_ratio_tendsto p a b M hp ha hb hab hM f hf hF r t ht
    γ cσ hγ0 hγ1
  filter_upwards [hratio.eventually (Ioo_mem_nhds hdlow hdhigh)] with n hmem
  exact ⟨hmem.1.le, hmem.2.le⟩

/-! ## The center-band-discharged endpoint -/

/-- **The feasible endpoint with the center band discharged.**  On top of
`actualQ1_knownScaleH_fullChain_generalSigned_feasible`, the `hband` premise is
discharged with the explicit band `d = (1 - f t)/2` and EVERY fixed `cσ` via
`centerBand_hband_discharged`; the remaining premises are the model window,
the b-band datum, the β window, `cσ` and the E5 bias envelope. -/
theorem actualQ1_knownScaleH_fullChain_generalSigned_feasible_centerBand
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hbband : (1 - f t) ^ 2 < 1 - b)
    (β : ℝ) (hβ0 : 0 < β) (hβ : β < (1 - f t) * (4 * f t - 3))
    (cσ : ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * ((n : ℝ) ^ (-(f t)))) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsWeightedRieszSecondChaosLaw gaussianSeqMeasure Q (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r) ∧
      TendstoInDistribution
        (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
          seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ x - f t))
        atTop (fun ω => -Q ω)
        (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        gaussianSeqMeasure := by
  have hft : f t ∈ Ioo (0 : ℝ) 1 := hf.1 ht
  have hft1 : (f t : ℝ) < 1 := hft.2
  have hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-(f t))) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-(f t))) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 :=
    fun n k => actualQ1_hane_all f hf ((n : ℝ) ^ (-(f t))) t n k
  have hband := centerBand_hband_discharged p a b M hp ha hb hab hM f hf hF r t ht
    (f t) cσ hft.1 hft1 hlong
  exact actualQ1_knownScaleH_fullChain_generalSigned_feasible p a b M r hp ha hb hab hM
    f hf hF t ht hlong hbband β hβ0 hβ cσ ((1 - f t) / 2)
    (div_pos (by linarith) (by norm_num)) hband C hC hBias

/-! ## The zero-degree-of-freedom instance (takeover7 leftover) -/

/-- **The zero-degree-of-freedom feasible endpoint.**  The β window is
instantiated internally at the window midpoint
`β := (1 - f t) * (4 * f t - 3) / 2` (positive since `4 f t - 3 > 0` and
`0 < 1 - f t`); the caller supplies no rate parameters at all. -/
theorem actualQ1_knownScaleH_fullChain_generalSigned_feasible_centerBand_zeroDof
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hbband : (1 - f t) ^ 2 < 1 - b)
    (cσ : ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * ((n : ℝ) ^ (-(f t)))) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsWeightedRieszSecondChaosLaw gaussianSeqMeasure Q (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r) ∧
      TendstoInDistribution
        (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
          seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t cσ x - f t))
        atTop (fun ω => -Q ω)
        (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        gaussianSeqMeasure := by
  have hft1 : (f t : ℝ) < 1 := (hf.1 ht).2
  have h4 : (0 : ℝ) < 4 * f t - 3 := by linarith
  have hβ0 : (0 : ℝ) < (1 - f t) * (4 * f t - 3) / 2 :=
    div_pos (mul_pos (sub_pos.mpr hft1) h4) (by norm_num)
  have hβ : (1 - f t) * (4 * f t - 3) / 2 < (1 - f t) * (4 * f t - 3) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_pos (sub_pos.mpr hft1) h4]
  exact actualQ1_knownScaleH_fullChain_generalSigned_feasible_centerBand p a b M r hp
    ha hb hab hM f hf hF t ht hlong hbband
    ((1 - f t) * (4 * f t - 3) / 2) hβ0 hβ cσ C hC hBias

end Hurst
