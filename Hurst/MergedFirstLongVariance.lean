import Hurst.FirstStrideLongRows
import Hurst.MergedWeights
import Hurst.CommonFirstVariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

def firstStrideLongRowBound (b C A : ℝ) (d n : ℕ) : ℝ :=
  2 * (4 * A) ^ 2 *
    (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1 +
      (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2) +
    2 * (n : ℝ) * (4 * gridCovarianceError b C n) ^ 2

theorem hurstHolder_merged_first_stride_log_variance_lt_one
    (p a b M : ℝ) (r d q : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (hd : 0 < d) (hq : d ≤ q) :
    ∃ N₀ > 0, ∃ A ≥ 1, ∃ C ≥ 0, ∃ D ≥ 0,
      ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ m : ℕ, 0 < m →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → N₀ ≤ (n : ℝ) * δ →
      1 ≤ (m : ℝ) * δ →
      Var[gaussianLogStatistic (averagedLocalWeights r n q m δ)
          (commonFirstStrideCoefficients n d q hq);
        featureGaussian
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤
        D / (n : ℝ) * firstStrideLongRowBound b C A d n := by
  obtain ⟨A, hA, C, hC, hrows⟩ :=
    hurstHolder_stride_first_correlation_rows_lt_one
      p a b M hp ha hb hab hM d hd
  obtain ⟨N₀, hN₀, W, hW, hw⟩ := averagedLocalWeights_uniform_bounds r q
  refine ⟨N₀, hN₀, A, hA, C, hC,
    12 * gaussianLogSquareVariance * (W * W), by
      have := gaussianLogSquareVariance_nonneg
      positivity, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop q] with n hnrows hnq
  intro f hf hF m hm δ hδ hδhalf hN hmd
  have hn0 : 0 < n := by omega
  let H := midpointSampleHurst f hf.1 n
  obtain ⟨hzero, hrow⟩ := hnrows f hf hF
  have hfeat : ∀ i,
      ∑ j, commonFirstStrideCoefficients n d q hq i j •
        gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [commonFirstStrideCoefficients,
      gridStrideFirst_feature_identity n d hn0 hd H]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne'
      (hzero _)
  obtain ⟨hl1, hmax⟩ := hw n m hn0 hnq hm δ hδ hδhalf hN hmd
  have hr : ∀ i,
      (∑ j, featureCorrelation (gridObservationFeatures n H)
        (commonFirstStrideCoefficients n d q hq i)
        (commonFirstStrideCoefficients n d q hq j) ^ 2) ≤
          firstStrideLongRowBound b C A d n := by
    intro i
    simp only [commonFirstStrideCoefficients,
      gridStrideFirst_correlation_identity n d hn0 hd H]
    exact finite_subfamily_square_rows _
      (commonFirstStrideIndex_injective n d q hq) _
      (firstStrideLongRowBound b C A d n) hrow i
  have hB : 0 ≤ firstStrideLongRowBound b C A d n := by
    unfold firstStrideLongRowBound gridCovarianceError
    positivity
  have he := gaussianLogStatistic_variance_row_bound
    (gridObservationFeatures n H)
    (averagedLocalWeights r n q m δ)
    (commonFirstStrideCoefficients n d q hq) hfeat
    (3 * W / (n : ℝ)) W (firstStrideLongRowBound b C A d n)
    (by positivity) hB hmax hl1 hr
  exact he.trans_eq (by ring)

end Hurst
