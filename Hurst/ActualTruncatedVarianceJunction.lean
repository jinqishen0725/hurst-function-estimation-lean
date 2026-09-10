import Hurst.FiniteVarianceReindex
import Hurst.ActualFirstTruncatedVarianceLimit
import Hurst.ActualSecondTruncatedVarianceLimit

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Hurst

theorem vectorCorrelation_comm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) :
    vectorCorrelation u v = vectorCorrelation v u := by
  unfold vectorCorrelation
  rw [real_inner_comm, mul_comm]

/-- The finite q=1 lag approximation is exactly the scaled covariance matrix
restricted to pairs below the same distance cutoff. -/
theorem actualStrideFirst_finiteLag_eq_distance_sum
    (r K R n : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (δ : ℕ → ℝ) :
    (∑ k ∈ Finset.range R,
      actualStrideFirstTruncatedLagContribution r K f hf t δ n k) =
      (n : ℝ) * δ n *
        (∑ i, ∑ j, if Nat.dist i.val j.val < R then
          localPolynomialWeights r n 1 (δ n) t i *
          localPolynomialWeights r n 1 (δ n) t j *
          gaussianLogTruncationCovariance K
            (vectorCorrelation
              (gridStrideFirstActual n 1 (midpointSampleHurst f hf n) i)
              (gridStrideFirstActual n 1 (midpointSampleHurst f hf n) j))
        else 0) := by
  let w := localPolynomialWeights r n 1 (δ n) t
  let corr : Fin (n - 1) → Fin (n - 1) → ℝ := fun i j =>
    vectorCorrelation
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf n) i)
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf n) j)
  have hsym : ∀ i j,
      gaussianLogTruncationCovariance K (corr i j) =
      gaussianLogTruncationCovariance K (corr j i) := by
    intro i j
    rw [show corr i j = corr j i by
      exact vectorCorrelation_comm _ _]
  have hre := fin_weighted_distance_lt_sum_eq_zeroExtended_lags
    (n - 1) R w corr (gaussianLogTruncationCovariance K) hsym
  rw [hre, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold actualStrideFirstTruncatedLagContribution
  dsimp only [w, corr]
  ring_nf
  simp only [actualStrideFirstLagCorrelation, finZeroExtendedLagCorrelation]

/-- The finite q=2 lag approximation is exactly the scaled covariance matrix
restricted to pairs below the same distance cutoff. -/
theorem actualSecond_finiteLag_eq_distance_sum
    (r K R n : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (δ : ℕ → ℝ) :
    (∑ k ∈ Finset.range R,
      actualSecondTruncatedLagContribution r K f hf t δ n k) =
      (n : ℝ) * δ n *
        (∑ i, ∑ j, if Nat.dist i.val j.val < R then
          localPolynomialWeights r n 2 (δ n) t i *
          localPolynomialWeights r n 2 (δ n) t j *
          gaussianLogTruncationCovariance K
            (vectorCorrelation
              (gridSecondActual n (midpointSampleHurst f hf n) i)
              (gridSecondActual n (midpointSampleHurst f hf n) j))
        else 0) := by
  let w := localPolynomialWeights r n 2 (δ n) t
  let corr : Fin (n - 2) → Fin (n - 2) → ℝ := fun i j =>
    vectorCorrelation
      (gridSecondActual n (midpointSampleHurst f hf n) i)
      (gridSecondActual n (midpointSampleHurst f hf n) j)
  have hsym : ∀ i j,
      gaussianLogTruncationCovariance K (corr i j) =
      gaussianLogTruncationCovariance K (corr j i) := by
    intro i j
    rw [show corr i j = corr j i by
      exact vectorCorrelation_comm _ _]
  have hre := fin_weighted_distance_lt_sum_eq_zeroExtended_lags
    (n - 2) R w corr (gaussianLogTruncationCovariance K) hsym
  rw [hre, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold actualSecondTruncatedLagContribution
  dsimp only [w, corr]
  ring_nf
  simp only [actualSecondLagCorrelation, finZeroExtendedLagCorrelation]

end Hurst
