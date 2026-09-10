import Hurst.GridCorrelationRows
import Hurst.GaussianLogRisk
import Hurst.LocalWeights

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem vectorCorrelation_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    vectorCorrelation (r • u) (s • v) = vectorCorrelation u v := by
  unfold vectorCorrelation
  rw [real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hs]
  calc
    _ = ((r * s) * ⟪u, v⟫) / ((r * s) * (‖u‖ * ‖v‖)) := by ring
    _ = _ := mul_div_mul_left _ _ (mul_pos hr hs).ne'

def gridDifferenceCoefficients (n : ℕ) (i : Fin (n - 1)) : EuclideanSpace ℝ (Fin n) :=
  observationDifferenceWeights (firstDiffLeft n i) (firstDiffRight n i)

def gridObservationFeatures (n : ℕ) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin n) : Lp ℂ 2 (volume : Measure ℝ) :=
  harmonizableFeature (H i) (grid n i.val)

theorem gridDifference_feature_identity (n : ℕ) (hn : 0 < n) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - 1)) :
    (∑ j, gridDifferenceCoefficients n i j • gridObservationFeatures n H j) =
      ((1 / (n : ℝ)) ^ (H (firstDiffLeft n i) : ℝ)) • gridActualIncrement n H i := by
  rw [gridDifferenceCoefficients, observationDifferenceWeights_feature]
  unfold gridObservationFeatures
  rw [grid_firstDifference_step n i]
  exact varyingIncrement_normalized_identity _ _ _ _ (by positivity)

theorem gridDifference_correlation_identity (n : ℕ) (hn : 0 < n) (H : Fin n → Ioo (0 : ℝ) 1) (i j : Fin (n - 1)) :
    featureCorrelation (gridObservationFeatures n H) (gridDifferenceCoefficients n i) (gridDifferenceCoefficients n j) =
      vectorCorrelation (gridActualIncrement n H i) (gridActualIncrement n H j) := by
  change vectorCorrelation (∑ k, gridDifferenceCoefficients n i k • gridObservationFeatures n H k)
    (∑ k, gridDifferenceCoefficients n j k • gridObservationFeatures n H k) = _
  rw [gridDifference_feature_identity n hn H i, gridDifference_feature_identity n hn H j]
  exact vectorCorrelation_smul _ _ _ _ (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)

/-- Actual correlated local-polynomial log variance; no row bound remains as a premise. -/
theorem actual_grid_local_log_variance (a b B : ℝ) (r : ℕ)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ H : Fin n → Ioo (0 : ℝ) 1,
      (∀ i, (H i : ℝ) ∈ Icc a b) →
      (∀ i : Fin (n - 1), |(H (firstDiffRight n i) : ℝ) - H (firstDiffLeft n i)| ≤ B / n) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      Var[gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n);
        featureGaussian (gridObservationFeatures n H)] ≤ C / ((n : ℝ) * δ) := by
  obtain ⟨R, hR, hrows⟩ := actual_grid_correlation_rows_eventually a b B ha hb hab hB
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_uniform_stability r 1
  refine ⟨N₀, hN₀, 4 * gaussianLogSquareVariance * (D * D * R), by have := gaussianLogSquareVariance_nonneg; positivity, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop 1] with n hrows hn
  intro H hH hstep δ t hδ hδhalf ht hN
  have hn0 : 0 < n := by omega
  have hnf : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨hzero, hrow⟩ := hrows H hH hstep
  have hfeat : ∀ i, ∑ j, gridDifferenceCoefficients n i j • gridObservationFeatures n H j ≠ 0 := by
    intro i
    rw [gridDifference_feature_identity n hn0 H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  obtain ⟨hdet, hmax, hl1, hmom⟩ := hw n hn0 hn δ t hδ hδhalf ht hN
  have hc := gaussianLogStatistic_variance_row_bound (gridObservationFeatures n H)
    (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) hfeat
    (D / ((n : ℝ) * δ)) D R (by positivity) hR hmax hl1
    (by intro i; simpa only [gridDifference_correlation_identity n hn0 H] using hrow i)
  exact hc.trans_eq (by ring)

end Hurst
