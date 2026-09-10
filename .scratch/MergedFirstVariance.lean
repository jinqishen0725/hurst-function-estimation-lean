import Hurst.CommonFirstVariance
import Hurst.MergedWeights

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst
theorem hurstHolder_merged_first_stride_log_variance (p a b M : ℝ) (r d q : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M)
    (hd : 0 < d) (hq : d ≤ q) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ m : ℕ, 0 < m →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → N₀ ≤ (n:ℝ)*δ → 1 ≤ (m:ℝ)*δ →
      Var[gaussianLogStatistic (averagedLocalWeights r n q m δ) (commonFirstStrideCoefficients n d q hq);
        featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤ C/(n:ℝ) := by
  obtain ⟨R, hR, hrows⟩ := hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM d hd
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := averagedLocalWeights_uniform_bounds r q
  refine ⟨N₀, hN₀, 12*gaussianLogSquareVariance*(D*D*R), by have := gaussianLogSquareVariance_nonneg; positivity, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop q] with n hrows hn
  intro f hf hF m hm δ hδ hδhalf hN hmd
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  let H := midpointSampleHurst f hf.1 n
  obtain ⟨hzero, hrow⟩ := hrows f hf hF
  have hfeat : ∀ i, ∑ j, commonFirstStrideCoefficients n d q hq i j • gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [commonFirstStrideCoefficients, gridStrideFirst_feature_identity n d hn0 hd H]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero _)
  obtain ⟨hl1, hmax⟩ := hw n m hn0 hn hm δ hδ hδhalf hN hmd
  have hr : ∀ i, (∑ j, featureCorrelation (gridObservationFeatures n H) (commonFirstStrideCoefficients n d q hq i)
      (commonFirstStrideCoefficients n d q hq j)^2) ≤ R := by
    intro i
    simp only [commonFirstStrideCoefficients, gridStrideFirst_correlation_identity n d hn0 hd H]
    exact finite_subfamily_square_rows _ (commonFirstStrideIndex_injective n d q hq) _ R hrow i
  have he := gaussianLogStatistic_variance_row_bound (gridObservationFeatures n H)
    (averagedLocalWeights r n q m δ) (commonFirstStrideCoefficients n d q hq) hfeat
    (3*D/(n:ℝ)) D R (by positivity) hR hmax hl1 hr
  exact he.trans_eq (by ring)


end Hurst
