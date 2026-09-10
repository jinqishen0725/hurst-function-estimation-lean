import Hurst.ScaleAverage

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q2_linearScale_variance (p a b M : ℝ) (r : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ V ≥ 0, ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n →
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ → 1 ≤ (m:ℝ)*δ →
      MemLp (q2LinearScale r n m δ) 2 (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      Var[q2LinearScale r n m δ; featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤
        V*(Real.log n)^2/(n:ℝ) := by
  obtain ⟨N₁, hN₁, V₁, hV₁, hv₁⟩ := hurstHolder_merged_stride_log_variance p a b M r 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N₂, hN₂, V₂, hV₂, hv₂⟩ := hurstHolder_merged_stride_log_variance p a b M r 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hv₁.and (hv₂.and (hm₁.and hm₂)))
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁ (le_max_left _ _), (4+4/(Real.log 2)^2)*(V₁+V₂), by positivity,
    max N 4, le_max_right _ _, ?_⟩
  intro n hn hL f hf hF m hm δ hδ hδhalf hnd hmd
  obtain ⟨hv1, hv2, hm1, hm2⟩ := hN n ((le_max_left N 4).trans hn)
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := averagedLocalWeights r n 4 m δ
  let a₁ := commonStrideCoefficients n 1 4 (by norm_num)
  let a₂ := commonStrideCoefficients n 2 4 (by norm_num)
  have hz₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hm1 f hf hF i).1
  have hz₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hm2 f hf hF i).1
  have hG₁ := gaussianLogStatistic_memLp_two v w a₁ hz₁
  have hG₂ := gaussianLogStatistic_memLp_two v w a₂ hz₂
  refine ⟨(hG₁.const_mul _).add (hG₂.const_mul _), ?_⟩
  have he := linearScaleCombination_variance (featureGaussian v) _ _ hG₁ hG₂ (Real.log n) hL
  apply he.trans
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (hv1 f hf hF m hm δ hδ hδhalf ((le_max_left _ _).trans hnd) hmd)
      (hv2 f hf hF m hm δ hδ hδhalf ((le_max_right _ _).trans hnd) hmd))
    (show 0 ≤ (4+4/(Real.log 2)^2)*(Real.log n)^2 by positivity)
  exact hh.trans_eq (by ring)

end Hurst
