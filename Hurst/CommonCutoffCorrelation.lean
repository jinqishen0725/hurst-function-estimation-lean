import Hurst.CommonFirstVariance
import Hurst.CommonStrideVariance

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Hurst

theorem commonFirstStride_feature_nonzero
    {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hq : d ≤ q)
    (H : Fin n → Ioo (0 : ℝ) 1)
    (hz : ∀ i, gridStrideFirstActual n d H i ≠ 0) :
    ∀ i, ∑ j, commonFirstStrideCoefficients n d q hq i j •
      gridObservationFeatures n H j ≠ 0 := by
  intro i
  rw [commonFirstStrideCoefficients, gridStrideFirst_feature_identity n d hn hd H]
  exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hz _)

theorem commonFirstStride_pointwise
    {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hq : d ≤ q)
    (H : Fin n → Ioo (0 : ℝ) 1) (A e : ℝ) (u : ℕ → ℝ)
    (hp : ∀ i j : Fin (n - d),
      |vectorCorrelation (gridStrideFirstActual n d H i)
        (gridStrideFirstActual n d H j)| ≤ A * u (Nat.dist j.val i.val) + e) :
    ∀ i j : Fin (n - q),
      |featureCorrelation (gridObservationFeatures n H)
        (commonFirstStrideCoefficients n d q hq i)
        (commonFirstStrideCoefficients n d q hq j)| ≤
          A * u (Nat.dist j.val i.val) + e := by
  intro i j
  simp only [commonFirstStrideCoefficients,
    gridStrideFirst_correlation_identity n d hn hd H]
  exact hp (commonFirstStrideIndex n d q hq i) (commonFirstStrideIndex n d q hq j)

theorem commonFirstStride_square_rows
    {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hq : d ≤ q)
    (H : Fin n → Ioo (0 : ℝ) 1) (R : ℝ)
    (hr : ∀ i : Fin (n - d),
      ∑ j, vectorCorrelation (gridStrideFirstActual n d H i)
        (gridStrideFirstActual n d H j) ^ 2 ≤ R) :
    ∀ i : Fin (n - q),
      ∑ j, |featureCorrelation (gridObservationFeatures n H)
        (commonFirstStrideCoefficients n d q hq i)
        (commonFirstStrideCoefficients n d q hq j)| ^ 2 ≤ R := by
  intro i
  simp only [commonFirstStrideCoefficients,
    gridStrideFirst_correlation_identity n d hn hd H, sq_abs]
  exact finite_subfamily_square_rows _ (commonFirstStrideIndex_injective n d q hq)
    _ R hr i

theorem commonStride_feature_nonzero
    {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hq : 2 * d ≤ q)
    (H : Fin n → Ioo (0 : ℝ) 1)
    (hz : ∀ i, gridStrideSecondActual n d H i ≠ 0) :
    ∀ i, ∑ j, commonStrideCoefficients n d q hq i j •
      gridObservationFeatures n H j ≠ 0 := by
  intro i
  rw [commonStrideCoefficients, gridStrideSecond_feature_identity n d hn hd H]
  exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hz _)

theorem commonStride_pointwise
    {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hq : 2 * d ≤ q)
    (H : Fin n → Ioo (0 : ℝ) 1) (A e : ℝ) (u : ℕ → ℝ)
    (hp : ∀ i j : Fin (n - 2 * d),
      |vectorCorrelation (gridStrideSecondActual n d H i)
        (gridStrideSecondActual n d H j)| ≤ A * u (Nat.dist j.val i.val) + e) :
    ∀ i j : Fin (n - q),
      |featureCorrelation (gridObservationFeatures n H)
        (commonStrideCoefficients n d q hq i)
        (commonStrideCoefficients n d q hq j)| ≤
          A * u (Nat.dist j.val i.val) + e := by
  intro i j
  simp only [commonStrideCoefficients,
    gridStrideSecond_correlation_identity n d hn hd H]
  exact hp (commonStrideIndex n d q hq i) (commonStrideIndex n d q hq j)

theorem commonStride_square_rows
    {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hq : 2 * d ≤ q)
    (H : Fin n → Ioo (0 : ℝ) 1) (R : ℝ)
    (hr : ∀ i : Fin (n - 2 * d),
      ∑ j, vectorCorrelation (gridStrideSecondActual n d H i)
        (gridStrideSecondActual n d H j) ^ 2 ≤ R) :
    ∀ i : Fin (n - q),
      ∑ j, |featureCorrelation (gridObservationFeatures n H)
        (commonStrideCoefficients n d q hq i)
        (commonStrideCoefficients n d q hq j)| ^ 2 ≤ R := by
  intro i
  simp only [commonStrideCoefficients,
    gridStrideSecond_correlation_identity n d hn hd H, sq_abs]
  exact finite_subfamily_square_rows _ (commonStrideIndex_injective n d q hq)
    _ R hr i

end Hurst
