import Hurst.SecondGridLogVariance
import Hurst.LogNormPerturbation
import Hurst.LogCorrectionSmooth

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

/-- Uniform actual q=2 logarithmic mean, with the nonlinear correction retained. -/
theorem hurstHolder_grid_second_log_mean (p a b M : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ i : Fin (n - 2),
      (∑ j, gridSecondCoefficients n i j • gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0) ∧
      |(∫ x, Real.log (⟪gridSecondCoefficients n i, x⟫ ^ 2)
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) -
        (-2 * f (grid n i.val) * Real.log n + q2LogCorrection (f (grid n i.val)) + gaussianLogSquareMean)| ≤
          gridCovarianceError (1 / 2) C n := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_grid_second_remainder p a b M hp ha hb hab hM
  obtain ⟨c, hcp, hfloor⟩ := normalizedFrozenSecondIncrement_uniform_norm_floor b hb
  refine ⟨(20 / c ^ 2) * C, by positivity, ?_⟩
  have he1 := (gridCovarianceError_tendsto (1 / 2) C (by norm_num)).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hec := (gridCovarianceError_tendsto (1 / 2) C (by norm_num)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < c / 2 by positivity))
  filter_upwards [eventually_ge_atTop 1, he1, hec] with n hn he1 hec
  intro f hf hF i
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let H := midpointSampleHurst f hf.1 n
  let W := gridSecondActual n H i
  let V := normalizedFrozenSecondIncrement (H (secondDiffLeft n i)) (grid n i.val) (1 / n)
  let e := gridCovarianceError (1 / 2) C n
  have he0 : 0 ≤ e := by
    dsimp [e, gridCovarianceError]
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  have hh : (H (secondDiffLeft n i) : ℝ) ≤ b := (hF (grid_mem n _ hn0 (secondDiffLeft n i).isLt)).2
  obtain ⟨hW, hlog⟩ := log_norm_square_perturbation W V c e hcp he0 he1.le hec.le
    (hfloor _ hh _ _ (by positivity)) (normalizedFrozenSecondIncrement_norm_le _ _ _ (by positivity))
    (hc f hf hF n hn0 i)
  have hfeat : ∑ j, gridSecondCoefficients n i j • gridObservationFeatures n H j ≠ 0 := by
    rw [gridSecond_feature_identity n hn0 H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' hW
  refine ⟨hfeat, ?_⟩
  have hm := featureGaussian_expected_log_square (gridObservationFeatures n H) (gridSecondCoefficients n i) hfeat
  rw [gridSecond_feature_identity n hn0 H i, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.log_mul (pow_ne_zero 2 (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 / n) _).ne')
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hW)), Real.log_pow,
    Real.log_rpow (by positivity : (0 : ℝ) < 1 / n), one_div, Real.log_inv] at hm
  have hv : ‖V‖ ^ 2 = 4 - (2 : ℝ) ^ (2 * f (grid n i.val)) :=
    normalizedFrozenSecondIncrement_norm_sq _ _ _ (by positivity)
  rw [hv] at hlog
  rw [hm]
  have heq : (20 / c ^ 2) * e = gridCovarianceError (1 / 2) ((20 / c ^ 2) * C) n := by
    dsimp [e, gridCovarianceError]
    ring
  rw [heq] at hlog
  convert! hlog using 1
  congr 1
  dsimp only [W, H, midpointSampleHurst, secondDiffLeft, q2LogCorrection]
  ring

end Hurst
