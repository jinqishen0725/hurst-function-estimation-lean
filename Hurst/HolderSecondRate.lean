import Hurst.HolderSecondMSE
import Hurst.OptimalBandwidth

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Uniform full-interval q=2 MSE at the p=2 minimax scale. -/
theorem hurstHolder_q2_p2_uniform_mse_rate (a b M : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass 2 M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x, (q2LocalEstimator b 1 n (optimalLocalBandwidth 2 n) t x - g t) ^ 2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
          C * (lowerBoundRate 2 n) ^ 2 := by
  obtain ⟨N₀, hN₀, Cb, hCb, Cv, hCv, D, hD, Ce, hCe, N, hN, hmse⟩ :=
    hurstHolder_q2_p2_local_mse a b M ha hb hab hM
  have herror := (gridCovarianceError_square_row_tendsto (1 / 2) Ce (by norm_num)).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((optimalLocalBandwidth_eventual_design 2 N₀ (by norm_num)).and herror)
  refine ⟨2 * Cb ^ 2 + Cv / 4 + (D ^ 2 / 2), by positivity, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgmse⟩ := hmse f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro n hn t ht
  obtain ⟨⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩, herr⟩ := hK n ((le_max_right N K).trans hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have h := hgmse n ((le_max_left N K).trans hn) (optimalLocalBandwidth 2 n) t hδ hδhalf ht hnd
  have hbal := optimalLocalBandwidth_bias_balance 2 n
  norm_num only [show (2 : ℝ) * 2 = 4 by norm_num, Real.rpow_ofNat] at hbal
  rw [hbal] at h
  have hv : Cv / (4 * (n : ℝ) * optimalLocalBandwidth 2 n * Real.log n ^ 2) =
      (Cv / 4) * (lowerBoundRate 2 n) ^ 2 := by
    rw [← optimalLocalBandwidth_variance_balance 2 (by norm_num) n hn1]
    ring
  rw [hv] at h
  have he : (gridCovarianceError (1 / 2) Ce n) ^ 2 ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith
  have he' : (gridCovarianceError (1 / 2) Ce n) ^ 2 / Real.log n ^ 2 ≤ (lowerBoundRate 2 n) ^ 2 :=
    (div_le_self (sq_nonneg _) hlog2).trans (he.trans hrate)
  have he'' := mul_le_mul_of_nonneg_left he' (show 0 ≤ (D ^ 2 / 2) by positivity)
  apply h.trans
  calc
    _ = (2 * Cb ^ 2 * (lowerBoundRate 2 n) ^ 2 + Cv / 4 * (lowerBoundRate 2 n) ^ 2) +
        (D ^ 2 / 2) * ((gridCovarianceError (1 / 2) Ce n) ^ 2 / Real.log n ^ 2) := by ring
    _ ≤ (2 * Cb ^ 2 * (lowerBoundRate 2 n) ^ 2 + Cv / 4 * (lowerBoundRate 2 n) ^ 2) +
        (D ^ 2 / 2) * (lowerBoundRate 2 n) ^ 2 := add_le_add le_rfl he''
    _ = _ := by ring

end Hurst
