import Hurst.MergedFirstLongVariance
import Hurst.FirstScale

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_linearScale_variance_lt_one
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0,
    ∃ A₁ ≥ 1, ∃ C₁ ≥ 0, ∃ D₁ ≥ 0,
    ∃ A₂ ≥ 1, ∃ C₂ ≥ 0, ∃ D₂ ≥ 0,
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Real.log n →
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ m : ℕ, 0 < m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      N₀ ≤ (n : ℝ) * δ → 1 ≤ (m : ℝ) * δ →
      MemLp (q1LinearScale r n m δ) 2
        (featureGaussian
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ∧
      Var[q1LinearScale r n m δ;
        featureGaussian
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤
        (4 + 4 / (Real.log 2) ^ 2) * (Real.log n) ^ 2 *
          (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
           D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n) := by
  obtain ⟨N₁, hN₁, A₁, hA₁, C₁, hC₁, D₁, hD₁, hv₁⟩ :=
    hurstHolder_merged_first_stride_log_variance_lt_one
      p a b M r 1 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N₂, hN₂, A₂, hA₂, C₂, hC₂, D₂, hD₂, hv₂⟩ :=
    hurstHolder_merged_first_stride_log_variance_lt_one
      p a b M r 2 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₁, _, hm₁⟩ :=
    hurstHolder_common_first_stride_log_mean p a b M 1 2
      hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ :=
    hurstHolder_common_first_stride_log_mean p a b M 2 2
      hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hv₁.and (hv₂.and (hm₁.and hm₂)))
  refine ⟨max N₁ N₂, lt_of_lt_of_le hN₁ (le_max_left _ _),
    A₁, hA₁, C₁, hC₁, D₁, hD₁,
    A₂, hA₂, C₂, hC₂, D₂, hD₂,
    max N 2, le_max_right _ _, ?_⟩
  intro n hn hlog f hf hF m hm δ hδ hδhalf hnd hmd
  obtain ⟨hv1, hv2, hm1, hm2⟩ := hN n ((le_max_left N 2).trans hn)
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := averagedLocalWeights r n 2 m δ
  let a₁ := commonFirstStrideCoefficients n 1 2 (by norm_num)
  let a₂ := commonFirstStrideCoefficients n 2 2 (by norm_num)
  have hz₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hm1 f hf hF i).1
  have hz₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hm2 f hf hF i).1
  have hG₁ := gaussianLogStatistic_memLp_two v w a₁ hz₁
  have hG₂ := gaussianLogStatistic_memLp_two v w a₂ hz₂
  refine ⟨(hG₁.const_mul _).add (hG₂.const_mul _), ?_⟩
  have he := linearScaleCombination_variance
    (featureGaussian v) _ _ hG₁ hG₂ (Real.log n) hlog
  apply he.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add
      (hv1 f hf hF m hm δ hδ hδhalf ((le_max_left _ _).trans hnd) hmd)
      (hv2 f hf hF m hm δ hδ hδhalf ((le_max_right _ _).trans hnd) hmd))
    (by positivity)

end Hurst
