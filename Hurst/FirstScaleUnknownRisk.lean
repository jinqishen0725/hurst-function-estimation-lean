import Hurst.FirstScaleRisk
import Hurst.FirstScaleEquivariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_optimal_scale_risk_unknown (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ σ : ℝ, σ ≠ 0 → ∀ n : ℕ, N ≤ n →
      (∫ x, (q1LogScaleEstimator (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x-Real.log (σ^2))^2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val))/(Real.log n)^2 ≤ C*(lowerBoundRate p n)^2 := by
  obtain ⟨C, hC, N, hN, hunit⟩ := hurstHolder_q1_optimal_scale_risk p a b M hp ha hb hab hM
  obtain ⟨N₄, hN₄, D₄, hD₄, hw₄⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p-1) 2
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha (by linarith) hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha (by linarith) hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hm₁.and (hm₂.and
    (optimalLocalBandwidth_eventual_design p N₄ hp)))
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  intro σ hσ n hn
  have hn2 : 2 ≤ n := (hN.trans (le_max_left _ _)).trans hn
  obtain ⟨hm1, hm2, hdesign⟩ := hK n ((le_max_right N K).trans hn)
  obtain ⟨hn1, hδ, hδhalf, hnd, _, _⟩ := hdesign
  obtain ⟨hm, hmd⟩ := scaleAverageResolution_design p n hδ
  have hwms : ∑ i, averagedLocalWeights (Nat.ceil p-1) n 2 (scaleAverageResolution p n) (optimalLocalBandwidth p n) i = 1 := by
    apply averagedLocalWeights_sum _ _ _ _ hm
    intro j
    have hj := grid_mem (scaleAverageResolution p n) j.val hm j.isLt
    have he := (hw₄ n (by omega) hn2 _ _ hδ hδhalf ⟨hj.1.le,hj.2.le⟩ hnd).2.2.2 0
    simpa using he
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  have he := q1LogScaleEstimator_scale_integral (Nat.ceil p-1) n (scaleAverageResolution p n)
    (optimalLocalBandwidth p n) v hwms (fun i => (hm1 f hf hF i).1) (fun i => (hm2 f hf hF i).1) σ hσ (fun y => y^2)
  change (∫ x, (q1LogScaleEstimator (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x-Real.log (σ^2))^2
    ∂featureGaussian (fun i => σ • v i))/(Real.log n)^2 ≤ _
  rw [he]
  exact (hunit f hf hF n ((le_max_left N K).trans hn)).2

end Hurst
