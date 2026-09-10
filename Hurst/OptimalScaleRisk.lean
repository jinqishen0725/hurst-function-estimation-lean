import Hurst.UnitScaleRisk
import Hurst.ScaleBandwidth
import Hurst.ScaleMeasurability

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q2_optimal_scale_risk (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ n : ℕ, N ≤ n →
      MemLp (q2LogScaleEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n)) 2
        (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      (∫ x, (q2LogScaleEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x)^2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/(Real.log n)^2 ≤
        C*(lowerBoundRate p n)^2 := by
  obtain ⟨N₀, hN₀, C, hC, N, hN, hscale⟩ := hurstHolder_q2_logScale_mse_unit p a b M hp ha hb hab hM
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hm₁.and (hm₂.and
    ((optimalLocalBandwidth_eventual_design p N₀ (by linarith)).and (scale_optimal_rate_eventually p (by linarith)))))
  refine ⟨4*C, by positivity, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF n hn
  obtain ⟨hm1, hm2, hdesign, hrate⟩ := hK n ((le_max_right N K).trans hn)
  obtain ⟨hn1, hδ, hδhalf, hnd, _, hL⟩ := hdesign
  obtain ⟨hm, hmd⟩ := scaleAverageResolution_design p n hδ
  have hmem := q2LogScaleEstimator_memLp (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) a b ha hb hab
    (gridObservationFeatures n (midpointSampleHurst f hf.1 n)) (fun i => (hm1 f hf hF i).1) (fun i => (hm2 f hf hF i).1)
  refine ⟨hmem, ?_⟩
  have he := hscale f hf hF n ((le_max_left N K).trans hn) hL (scaleAverageResolution p n) hm
    (optimalLocalBandwidth p n) hδ hδhalf hnd hmd
  have hd := div_le_div_of_nonneg_right he (sq_nonneg (Real.log n))
  have hr := mul_le_mul_of_nonneg_left hrate hC
  have hh : C*((Real.log n*(optimalLocalBandwidth p n)^p)^2+(Real.log n*gridCovarianceError (1/2) 1 n)^2+
      (Real.log n)^2/(n:ℝ)+1/((n:ℝ)*optimalLocalBandwidth p n))/(Real.log n)^2 ≤
      (4*C)*(lowerBoundRate p n)^2 := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hr
  exact hd.trans hh

end Hurst
