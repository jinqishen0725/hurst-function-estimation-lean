import Hurst.CorrelationTailTransfer
import Hurst.ActualPointwiseDecay
import Hurst.FirstStrideActualRows
import Hurst.SecondGridLogVariance
import Hurst.GridErrorLimit

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_stride_first_correlation_square_average_tail
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b)) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ((n - 1 : ℕ) : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist i.val j.val then
          |featureCorrelation
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
            (gridStrideFirstCoefficients n 1 i)
            (gridStrideFirstCoefficients n 1 j)| ^ 2 else 0) ≤ ε := by
  obtain ⟨A, hA, C, hC, hdec⟩ :=
    hurstHolder_stride_first_correlation_decay p a b M hp ha hb hab hM 1 (by norm_num)
  let e : ℕ → ℝ := fun n => 4 * gridCovarianceError b C n
  have he0 : ∀ᶠ n in atTop, 0 ≤ e n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [e]
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_nonneg (by linarith)
    positivity
  have hm : ∀ᶠ n in atTop, 0 < n - 1 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    omega
  have herate : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) * (e n) ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hcast : (((n - 1 : ℕ) : ℝ)) ≤ n := by exact_mod_cast Nat.sub_le n 1
      have hs : 0 ≤ (e n) ^ 2 := sq_nonneg _
      calc
        ((n - 1 : ℕ) : ℝ) * (e n) ^ 2 ≤ (n : ℝ) * (e n) ^ 2 :=
          mul_le_mul_of_nonneg_right hcast hs
        _ = 16 * ((n : ℝ) * (gridCovarianceError b C n) ^ 2) := by
          dsimp only [e]
          ring
    · simpa only [mul_zero] using
        (gridCovarianceError_square_row_tendsto b C hb).const_mul 16
  have herr : ∀ᶠ n in atTop, ∀ i j : Fin (n - 1),
      |featureCorrelation
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridStrideFirstCoefficients n 1 i) (gridStrideFirstCoefficients n 1 j)| ≤
        (4 * A) * strideFirstDecay b 1 (Nat.dist j.val i.val) + e n := by
    filter_upwards [hdec, eventually_ge_atTop 2] with n hn hn2
    obtain ⟨_, hrow⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i j
    simpa only [e, gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n)] using hrow i j
  exact correlation_square_average_tail_vanishes
    (fun n => n - 1)
    (fun n i j => featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1 i) (gridStrideFirstCoefficients n 1 j))
    (strideFirstDecay b 1) (strideFirstDecay_square_summable b hb 1 (by norm_num))
    (strideFirstDecay_nonneg b 1) (4 * A) (by positivity) e he0 hm herr herate

theorem hurstHolder_grid_second_correlation_square_average_tail
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b)) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ((n - 2 : ℕ) : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist i.val j.val then
          |featureCorrelation
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
            (gridSecondCoefficients n i) (gridSecondCoefficients n j)| ^ 2 else 0) ≤ ε := by
  obtain ⟨A, hA, C, hC, hdec⟩ :=
    hurstHolder_stride_second_correlation_decay p a b M hp ha hb hab hM 1 (by norm_num)
  let e : ℕ → ℝ := fun n => A * gridCovarianceError (1 / 2) C n
  have he0 : ∀ᶠ n in atTop, 0 ≤ e n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [e]
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  have hm : ∀ᶠ n in atTop, 0 < n - 2 := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    omega
  have herate : Tendsto (fun n : ℕ => ((n - 2 : ℕ) : ℝ) * (e n) ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hcast : (((n - 2 : ℕ) : ℝ)) ≤ n := by exact_mod_cast Nat.sub_le n 2
      have hs : 0 ≤ (e n) ^ 2 := sq_nonneg _
      calc
        ((n - 2 : ℕ) : ℝ) * (e n) ^ 2 ≤ (n : ℝ) * (e n) ^ 2 :=
          mul_le_mul_of_nonneg_right hcast hs
        _ = A ^ 2 * ((n : ℝ) * (gridCovarianceError (1 / 2) C n) ^ 2) := by
          dsimp only [e]
          ring
    · simpa only [mul_zero] using
        (gridCovarianceError_square_row_tendsto (1 / 2) C (by norm_num)).const_mul (A ^ 2)
  have herr : ∀ᶠ n in atTop, ∀ i j : Fin (n - 2),
      |featureCorrelation
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridSecondCoefficients n i) (gridSecondCoefficients n j)| ≤
        A * strideSecondDecay b 1 (Nat.dist j.val i.val) + e n := by
    filter_upwards [hdec, eventually_ge_atTop 3] with n hn hn3
    obtain ⟨_, hrow⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i j
    have hh := hrow i j
    change |featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideSecondCoefficients n 1 i) (gridStrideSecondCoefficients n 1 j)| ≤ _
    rw [gridStrideSecond_correlation_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n)]
    exact hh
  exact correlation_square_average_tail_vanishes
    (fun n => n - 2)
    (fun n i j => featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n i) (gridSecondCoefficients n j))
    (strideSecondDecay b 1) (strideSecondDecay_square_summable b hb 1 (by norm_num))
    (strideSecondDecay_nonneg b 1) A hA e he0 hm herr herate

end Hurst
