import Hurst.SecondCorrelationRows
import Hurst.SecondGridActual
import Hurst.GridLogVariance

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

/-- The original Holder class supplies every premise of the actual q=2 correlation row estimate. -/
theorem hurstHolder_grid_second_correlation_rows (p a b M : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      (∀ i, gridSecondActual n (midpointSampleHurst f hf.1 n) i ≠ 0) ∧
      ∀ i : Fin (n - 2), (∑ j, vectorCorrelation (gridSecondActual n (midpointSampleHurst f hf.1 n) i)
        (gridSecondActual n (midpointSampleHurst f hf.1 n) j) ^ 2) ≤ R := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_grid_second_remainder p a b M hp ha hb hab hM
  obtain ⟨R, hR, hr⟩ := second_grid_correlation_rows_of_perturbation a b C ha hb hab hC
  refine ⟨R, hR, ?_⟩
  filter_upwards [hr, eventually_ge_atTop 1] with n hn hn1
  intro f hf hF
  let H := midpointSampleHurst f hf.1 n
  apply hn (n - 2) (Nat.sub_le n 2) (fun i => H (secondDiffLeft n i))
    (fun i => hF (grid_mem n _ (by omega) (secondDiffLeft n i).isLt)) (gridSecondActual n H)
  exact hc f hf hF n (by omega)

def gridSecondCoefficients (n : ℕ) (i : Fin (n - 2)) : EuclideanSpace ℝ (Fin n) :=
  observationDifferenceWeights (secondDiffMiddle n i) (secondDiffRight n i) -
    observationDifferenceWeights (secondDiffLeft n i) (secondDiffMiddle n i)

theorem gridSecond_feature_identity (n : ℕ) (hn : 0 < n) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - 2)) :
    (∑ j, gridSecondCoefficients n i j • gridObservationFeatures n H j) =
      ((1 / (n : ℝ)) ^ (H (secondDiffLeft n i) : ℝ)) • gridSecondActual n H i := by
  change (∑ j, (observationDifferenceWeights (secondDiffMiddle n i) (secondDiffRight n i) j -
      observationDifferenceWeights (secondDiffLeft n i) (secondDiffMiddle n i) j) • gridObservationFeatures n H j) = _
  simp only [sub_smul, Finset.sum_sub_distrib, observationDifferenceWeights_feature]
  unfold gridObservationFeatures gridSecondActual
  rw [smul_smul, ← Real.rpow_add (show 0 < 1 / (n : ℝ) by positivity), add_neg_cancel, Real.rpow_zero, one_smul]
  unfold varyingSecondIncrement
  rw [grid_second_middle_step, grid_second_right_step]
  dsimp only [secondDiffLeft]
  module

theorem gridSecond_correlation_identity (n : ℕ) (hn : 0 < n) (H : Fin n → Ioo (0 : ℝ) 1) (i j : Fin (n - 2)) :
    featureCorrelation (gridObservationFeatures n H) (gridSecondCoefficients n i) (gridSecondCoefficients n j) =
      vectorCorrelation (gridSecondActual n H i) (gridSecondActual n H j) := by
  change vectorCorrelation (∑ k, gridSecondCoefficients n i k • gridObservationFeatures n H k)
    (∑ k, gridSecondCoefficients n j k • gridObservationFeatures n H k) = _
  rw [gridSecond_feature_identity n hn H i, gridSecond_feature_identity n hn H j]
  exact vectorCorrelation_smul _ _ _ _ (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)

/-- Actual q=2 local-polynomial log variance over the whole original fixed-range Holder class. -/
theorem hurstHolder_grid_second_log_variance (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      Var[gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n);
        featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))] ≤ C / ((n : ℝ) * δ) := by
  obtain ⟨R, hR, hrows⟩ := hurstHolder_grid_second_correlation_rows p a b M hp ha hb hab hM
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_uniform_stability r 2
  refine ⟨N₀, hN₀, 4 * gaussianLogSquareVariance * (D * D * R), by have := gaussianLogSquareVariance_nonneg; positivity, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop 2] with n hrows hn
  intro f hf hF δ t hδ hδhalf ht hN
  let H := midpointSampleHurst f hf.1 n
  have hn0 : 0 < n := by omega
  have hnf : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨hzero, hrow⟩ := hrows f hf hF
  have hfeat : ∀ i, ∑ j, gridSecondCoefficients n i j • gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [gridSecond_feature_identity n hn0 H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  obtain ⟨hdet, hmax, hl1, hmom⟩ := hw n hn0 hn δ t hδ hδhalf ht hN
  have hc := gaussianLogStatistic_variance_row_bound (gridObservationFeatures n H)
    (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) hfeat
    (D / ((n : ℝ) * δ)) D R (by positivity) hR hmax hl1
    (by intro i; simpa only [gridSecond_correlation_identity n hn0 H] using hrow i)
  exact hc.trans_eq (by ring)

end Hurst
