import Hurst.GridLogVariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- The covariance perturbation also sharpens the actual logarithmic mean, uniformly at the boundary. -/
theorem actual_grid_log_mean_sharp (a b B : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → gridCovarianceError b C n ≤ 1 / 2 →
      ∀ H : Fin n → Ioo (0 : ℝ) 1, (∀ i, (H i : ℝ) ∈ Icc a b) →
      (∀ i : Fin (n - 1), |(H (firstDiffRight n i) : ℝ) - H (firstDiffLeft n i)| ≤ B / n) →
      ∀ i : Fin (n - 1),
      (∑ j, gridDifferenceCoefficients n i j • gridObservationFeatures n H j ≠ 0) ∧
      |(∫ x, Real.log (⟪gridDifferenceCoefficients n i, x⟫ ^ 2) ∂featureGaussian (gridObservationFeatures n H)) -
        (-2 * (H (firstDiffLeft n i) : ℝ) * Real.log n + gaussianLogSquareMean)| ≤ 2 * gridCovarianceError b C n := by
  obtain ⟨C, hC, hc⟩ := actual_grid_covariance_perturbation a b B ha hb hab hB
  refine ⟨C, hC, ?_⟩
  intro n hn hsmall H hH hstep i
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let W := gridActualIncrement n H i
  have hd := hc n hn H hH hstep i i
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, gridFrozenIncrement,
    normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hd
  have hfloor : (1 / 2 : ℝ) ≤ ‖W‖ ^ 2 := by have := (abs_le.mp hd).1; dsimp only [W]; linarith
  have hW : W ≠ 0 := by intro hz; rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hfloor; norm_num at hfloor
  have hfeat : ∑ j, gridDifferenceCoefficients n i j • gridObservationFeatures n H j ≠ 0 := by
    rw [gridDifference_feature_identity n hn H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' hW
  refine ⟨hfeat, ?_⟩
  have hm := featureGaussian_expected_log_square (gridObservationFeatures n H) (gridDifferenceCoefficients n i) hfeat
  rw [gridDifference_feature_identity n hn H i, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.log_mul (pow_ne_zero 2 (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 / n) _).ne')
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hW)), Real.log_pow,
    Real.log_rpow (by positivity : (0 : ℝ) < 1 / n), one_div, Real.log_inv] at hm
  have hl := log_lipschitz_from_below (‖W‖ ^ 2) 1 (1 / 2) (by norm_num) hfloor (by norm_num)
  simp only [Real.log_one, sub_zero] at hl
  have hd' : |‖W‖ ^ 2 - 1| ≤ gridCovarianceError b C n := hd
  have hlog : |Real.log (‖W‖ ^ 2)| ≤ 2 * gridCovarianceError b C n := by linarith
  rw [hm]
  convert! hlog using 1
  congr 1
  dsimp only [W]
  ring

end Hurst
