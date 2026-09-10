import Hurst.UnitUnknownMSE
import Hurst.UnknownInvariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst
set_option maxHeartbeats 800000

theorem hurstHolder_q2_unknown_mse_rate (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0:ℝ) 1) ∧ MapsTo g (Icc (0:ℝ) 1) (Icc a b) ∧
      ∀ σ : ℝ, σ ≠ 0 → ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0:ℝ) 1,
      (∫ x, (q2UnknownLocalEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x-g t)^2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤ C*(lowerBoundRate p n)^2 := by
  obtain ⟨C, hC, N, hN, hunit⟩ := hurstHolder_q2_unknown_unit_mse_rate p a b M hp ha hb hab hM
  obtain ⟨N₂, hN₂, D₂, hD₂, hw₂⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p-1) 2
  obtain ⟨N₄, hN₄, D₄, hD₄, hw₄⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p-1) 4
  obtain ⟨E₀, _, hm₀⟩ := hurstHolder_grid_second_log_mean p a b M hp ha hb hab hM
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hm₀.and (hm₁.and (hm₂.and
    (optimalLocalBandwidth_eventual_design p (max N₂ N₄) (by linarith)))))
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgb, hu⟩ := hunit f hf hF
  refine ⟨g, hg, heq, hgb, ?_⟩
  intro σ hσ n hn t ht
  have hn4 : 4 ≤ n := (hN.trans (le_max_left _ _)).trans hn
  obtain ⟨hm0, hm1, hm2, hdesign⟩ := hK n ((le_max_right N K).trans hn)
  obtain ⟨hn1, hδ, hδhalf, hnd, _, _⟩ := hdesign
  obtain ⟨hm, hmd⟩ := scaleAverageResolution_design p n hδ
  have hws : ∑ i, localPolynomialWeights (Nat.ceil p-1) n 2 (optimalLocalBandwidth p n) t i = 1 := by
    have he := (hw₂ n (by omega) (by omega) _ t hδ hδhalf ht ((le_max_left _ _).trans hnd)).2.2.2 0
    simpa using he
  have hwms : ∑ i, averagedLocalWeights (Nat.ceil p-1) n 4 (scaleAverageResolution p n) (optimalLocalBandwidth p n) i = 1 := by
    apply averagedLocalWeights_sum _ _ _ _ hm
    intro j
    have hj := grid_mem (scaleAverageResolution p n) j.val hm j.isLt
    have he := (hw₄ n (by omega) hn4 _ _ hδ hδhalf ⟨hj.1.le, hj.2.le⟩ ((le_max_right _ _).trans hnd)).2.2.2 0
    simpa using he
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  have he := q2UnknownLocalEstimator_scale_integral (Nat.ceil p-1) n (scaleAverageResolution p n)
    (optimalLocalBandwidth p n) t a b v hws hwms
    (fun i => (hm0 f hf hF i).1) (fun i => (hm1 f hf hF i).1) (fun i => (hm2 f hf hF i).1) σ hσ (fun y => (y-g t)^2)
  change (∫ x, (q2UnknownLocalEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x-g t)^2
    ∂featureGaussian (fun i => σ • v i)) ≤ _
  rw [he]
  exact hu n ((le_max_left N K).trans hn) t ht

end Hurst
