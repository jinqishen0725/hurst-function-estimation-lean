import Hurst.HolderGridMSE
import Hurst.OptimalBandwidth

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Uniform full-interval q=1 MSE at the minimax scale, including p=1. -/
theorem hurstHolder_q1_uniform_mse_rate (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x, (q1LocalEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) t x - g t) ^ 2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
          C * (lowerBoundRate p n) ^ 2 := by
  obtain ⟨N₀, hN₀, Cb, hCb, Cv, hCv, D, hD, Ce, hCe, N, hN, hmse⟩ :=
    hurstHolder_q1_local_mse p a b M hp ha hb hab hM
  have herror := (gridCovarianceError_square_row_tendsto b Ce hb).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((optimalLocalBandwidth_eventual_design p N₀ hp).and herror)
  refine ⟨2 * Cb ^ 2 + Cv / 4 + 2 * D ^ 2, by positivity, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgmse⟩ := hmse f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro n hn t ht
  obtain ⟨⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩, herr⟩ := hK n ((le_max_right N K).trans hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have h := hgmse n ((le_max_left N K).trans hn) (optimalLocalBandwidth p n) t hδ hδhalf ht hnd
  rw [optimalLocalBandwidth_bias_balance] at h
  have hv : Cv / (4 * (n : ℝ) * optimalLocalBandwidth p n * Real.log n ^ 2) =
      (Cv / 4) * (lowerBoundRate p n) ^ 2 := by
    rw [← optimalLocalBandwidth_variance_balance p hp n hn1]
    ring
  rw [hv] at h
  have he : (gridCovarianceError b Ce n) ^ 2 ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith
  have he' : (gridCovarianceError b Ce n) ^ 2 / Real.log n ^ 2 ≤ (lowerBoundRate p n) ^ 2 :=
    (div_le_self (sq_nonneg _) hlog2).trans (he.trans hrate)
  have he'' := mul_le_mul_of_nonneg_left he' (show 0 ≤ 2 * D ^ 2 by positivity)
  apply h.trans
  calc
    _ = (2 * Cb ^ 2 * (lowerBoundRate p n) ^ 2 + Cv / 4 * (lowerBoundRate p n) ^ 2) +
        2 * D ^ 2 * ((gridCovarianceError b Ce n) ^ 2 / Real.log n ^ 2) := by ring
    _ ≤ (2 * Cb ^ 2 * (lowerBoundRate p n) ^ 2 + Cv / 4 * (lowerBoundRate p n) ^ 2) +
        2 * D ^ 2 * (lowerBoundRate p n) ^ 2 := add_le_add le_rfl he''
    _ = _ := by ring

end Hurst
