import Hurst.FirstStrideGrid
import Hurst.FirstStrideRows

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem gridStrideFirst_correlation_identity (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (H : Fin n → Ioo (0:ℝ) 1) (i j : Fin (n-d)) :
    featureCorrelation (gridObservationFeatures n H) (gridStrideFirstCoefficients n d i) (gridStrideFirstCoefficients n d j) =
      vectorCorrelation (gridStrideFirstActual n d H i) (gridStrideFirstActual n d H j) := by
  change vectorCorrelation (∑ k, gridStrideFirstCoefficients n d i k • gridObservationFeatures n H k)
    (∑ k, gridStrideFirstCoefficients n d j k • gridObservationFeatures n H k) = _
  rw [gridStrideFirst_feature_identity n d hn hd H i,gridStrideFirst_feature_identity n d hn hd H j]
  exact vectorCorrelation_smul _ _ _ _ (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)

theorem hurstHolder_stride_first_correlation_rows (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      (∀ i, gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i ≠ 0) ∧
      ∀ i : Fin (n-d), (∑ j, vectorCorrelation (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i)
        (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) j)^2) ≤ R := by
  obtain ⟨C,hC,hcov⟩ := hurstHolder_stride_first_covariance p a b M hp ha (by linarith) hab hM d hd
  obtain ⟨R,hR,hr⟩ := first_stride_rows_of_covariance a b C d hd ha hb hab hC
  refine ⟨R,hR,?_⟩
  filter_upwards [hr,eventually_ge_atTop 1] with n hn hn1
  intro f hf hF
  exact hn (n-d) (Nat.sub_le _ _) (fun i => midpointSampleHurst f hf.1 n (strideFirstLeft n d i))
    (fun i => hF (grid_mem n _ (by omega) (strideFirstLeft n d i).isLt))
    (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n)) (hcov n (by omega) f hf hF)

end Hurst
