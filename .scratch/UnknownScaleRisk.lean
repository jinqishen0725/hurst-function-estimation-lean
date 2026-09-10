import Hurst.UnitScaleRisk
import Hurst.ScaleEquivariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q2_logScale_mse_unknown_scale (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ σ : ℝ, σ ≠ 0 → ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n → ∀ m : ℕ, 0 < m →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ → 1 ≤ (m:ℝ)*δ →
      (∫ x, (q2LogScaleEstimator a b (Nat.ceil p-1) n m δ x-Real.log (σ^2))^2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤
        C*((Real.log n*δ^p)^2+(Real.log n*gridCovarianceError (1/2) 1 n)^2+(Real.log n)^2/(n:ℝ)+1/((n:ℝ)*δ)) := by
  obtain ⟨N₀, hN₀, C, hC, N, hN, hunit⟩ := hurstHolder_q2_logScale_mse_unit p a b M hp ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p-1) 4
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hm₁.and hm₂)
  refine ⟨max N₀ Nw, lt_of_lt_of_le hN₀ (le_max_left _ _), C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF σ hσ n hn hL m hm δ hδ hδhalf hnd hmd
  have hn4 : 4 ≤ n := (hN.trans (le_max_left _ _)).trans hn
  obtain ⟨hm1, hm2⟩ := hK n ((le_max_right N K).trans hn)
  have hws : ∑ i, averagedLocalWeights (Nat.ceil p-1) n 4 m δ i = 1 := by
    apply averagedLocalWeights_sum _ _ _ _ hm δ
    intro j
    have hj := grid_mem m j.val hm j.isLt
    have he := (hw n (by omega) hn4 δ (grid m j.val) hδ hδhalf ⟨hj.1.le, hj.2.le⟩ ((le_max_right _ _).trans hnd)).2.2.2 0
    simpa using he
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  have he := q2LogScaleEstimator_scale_integral (Nat.ceil p-1) n m δ a b v hws
    (fun i => (hm1 f hf hF i).1) (fun i => (hm2 f hf hF i).1) σ hσ (fun x => x^2)
  change (∫ x, (q2LogScaleEstimator a b (Nat.ceil p-1) n m δ x-Real.log (σ^2))^2 ∂featureGaussian (fun i => σ • v i)) ≤ _
  rw [he]
  exact hunit f hf hF n ((le_max_left N K).trans hn) hL m hm δ hδ hδhalf ((le_max_left _ _).trans hnd) hmd

end Hurst
