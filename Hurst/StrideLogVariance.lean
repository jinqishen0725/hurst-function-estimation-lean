import Hurst.StrideCorrelationRows
import Hurst.StrideGrid
import Hurst.GridLogVariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

/-- The original Holder class supplies every premise of the actual q=2 correlation row estimate. -/
theorem hurstHolder_grid_stride_second_correlation_rows (p a b M : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      (∀ i, gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) i ≠ 0) ∧
      ∀ i : Fin (n - 2*d), (∑ j, vectorCorrelation (gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) i)
        (gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) j) ^ 2) ≤ R := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_grid_stride_second_remainder p a b M hp ha hb hab hM d hd
  obtain ⟨R, hR, hr⟩ := stride_second_grid_correlation_rows_of_perturbation a b C d hd ha hb hab hC
  refine ⟨R, hR, ?_⟩
  filter_upwards [hr, eventually_ge_atTop d] with n hn hn1
  intro f hf hF
  let H := midpointSampleHurst f hf.1 n
  apply hn (n - 2*d) (Nat.sub_le n (2*d)) (fun i => H (strideSecondLeft n d i))
    (fun i => hF (grid_mem n _ (by omega) (strideSecondLeft n d i).isLt)) (gridStrideSecondActual n d H)
  exact hc f hf hF n (by omega)

def gridStrideSecondCoefficients (n d : ℕ) (i : Fin (n - 2*d)) : EuclideanSpace ℝ (Fin n) :=
  observationDifferenceWeights (strideSecondMiddle n d i) (strideSecondRight n d i) -
    observationDifferenceWeights (strideSecondLeft n d i) (strideSecondMiddle n d i)

theorem gridStrideSecond_feature_identity (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - 2*d)) :
    (∑ j, gridStrideSecondCoefficients n d i j • gridObservationFeatures n H j) =
      (((d : ℝ) / n) ^ (H (strideSecondLeft n d i) : ℝ)) • gridStrideSecondActual n d H i := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  change (∑ j, (observationDifferenceWeights (strideSecondMiddle n d i) (strideSecondRight n d i) j -
      observationDifferenceWeights (strideSecondLeft n d i) (strideSecondMiddle n d i) j) • gridObservationFeatures n H j) = _
  simp only [sub_smul, Finset.sum_sub_distrib, observationDifferenceWeights_feature]
  unfold gridObservationFeatures gridStrideSecondActual
  rw [smul_smul, ← Real.rpow_add (show 0 < (d : ℝ) / n by positivity), add_neg_cancel, Real.rpow_zero, one_smul]
  unfold varyingSecondIncrement
  rw [grid_stride_middle, grid_stride_right]
  dsimp only [strideSecondLeft]
  module

theorem gridStrideSecond_correlation_identity (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (H : Fin n → Ioo (0 : ℝ) 1) (i j : Fin (n - 2*d)) :
    featureCorrelation (gridObservationFeatures n H) (gridStrideSecondCoefficients n d i) (gridStrideSecondCoefficients n d j) =
      vectorCorrelation (gridStrideSecondActual n d H i) (gridStrideSecondActual n d H j) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  change vectorCorrelation (∑ k, gridStrideSecondCoefficients n d i k • gridObservationFeatures n H k)
    (∑ k, gridStrideSecondCoefficients n d j k • gridObservationFeatures n H k) = _
  rw [gridStrideSecond_feature_identity n d hn hd H i, gridStrideSecond_feature_identity n d hn hd H j]
  exact vectorCorrelation_smul _ _ _ _ (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)

/-- Actual q=2 local-polynomial log variance over the whole original fixed-range Holder class. -/
theorem hurstHolder_grid_stride_second_log_variance (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      Var[gaussianLogStatistic (localPolynomialWeights r n (2*d) δ t) (gridStrideSecondCoefficients n d);
        featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤ C / ((n : ℝ) * δ) := by
  obtain ⟨R, hR, hrows⟩ := hurstHolder_grid_stride_second_correlation_rows p a b M hp ha hb hab hM d hd
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_uniform_stability r (2*d)
  refine ⟨N₀, hN₀, 4 * gaussianLogSquareVariance * (D * D * R), by have := gaussianLogSquareVariance_nonneg; positivity, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop (2*d)] with n hrows hn
  intro f hf hF δ t hδ hδhalf ht hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let H := midpointSampleHurst f hf.1 n
  have hn0 : 0 < n := by omega
  have hnf : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨hzero, hrow⟩ := hrows f hf hF
  have hfeat : ∀ i, ∑ j, gridStrideSecondCoefficients n d i j • gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [gridStrideSecond_feature_identity n d hn0 hd H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  obtain ⟨hdet, hmax, hl1, hmom⟩ := hw n hn0 hn δ t hδ hδhalf ht hN
  have hc := gaussianLogStatistic_variance_row_bound (gridObservationFeatures n H)
    (localPolynomialWeights r n (2*d) δ t) (gridStrideSecondCoefficients n d) hfeat
    (D / ((n : ℝ) * δ)) D R (by positivity) hR hmax hl1
    (by intro i; simpa only [gridStrideSecond_correlation_identity n d hn0 hd H] using hrow i)
  exact hc.trans_eq (by ring)

end Hurst
