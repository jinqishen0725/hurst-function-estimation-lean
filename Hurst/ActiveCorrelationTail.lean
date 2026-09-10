import Hurst.ActiveWindowGeometry
import Hurst.ActiveWindowDistance
import Hurst.ActualPointwiseDecay
import Hurst.CorrelationTailTransfer
import Hurst.GridErrorLimit
import Hurst.SecondGridLogVariance

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem gridStrideSecondCoefficients_one (n : ℕ) :
    gridStrideSecondCoefficients n 1 = gridSecondCoefficients n := by
  funext i
  unfold gridStrideSecondCoefficients gridSecondCoefficients
  congr 2 <;> apply Fin.ext <;> rfl

/-- Replacing the full grid row by the active local-weight window preserves a
vanishing `m_n e_n^2` perturbation rate. -/
theorem localWeightActiveSet_card_mul_sq_tendsto_zero
    (q : ℕ) (δ : ℕ → ℝ) (t : ℝ) (e : ℕ → ℝ)
    (he0 : ∀ᶠ n in atTop, 0 ≤ e n)
    (he : Tendsto (fun n : ℕ => (n : ℝ) * (e n) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n q (δ n) t).card : ℝ) * (e n) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [he0] with n hen
    have hcardNat : (localWeightActiveSet n q (δ n) t).card ≤ n := by
      calc
        (localWeightActiveSet n q (δ n) t).card ≤ Fintype.card (Fin (n - q)) :=
          Finset.card_le_univ _
        _ = n - q := Fintype.card_fin _
        _ ≤ n := Nat.sub_le _ _
    have hcard : ((localWeightActiveSet n q (δ n) t).card : ℝ) ≤ n := by
      exact_mod_cast hcardNat
    exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  · exact he

/-- The exact B&S covariance-square tail condition on the increasing active
q=1 local window.  All distances here are active ranks, as required after
reindexing the row. -/
theorem hurstHolder_stride_first_active_correlation_square_average_tail
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ)⁻¹ *
        ∑ i, ∑ j,
          (if K < Nat.dist i.val j.val then
            |featureCorrelation
              (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
              (gridStrideFirstCoefficients n 1
                (localWeightActiveIndex n 1 (δ n) t i))
              (gridStrideFirstCoefficients n 1
                (localWeightActiveIndex n 1 (δ n) t j))| ^ 2 else 0) ≤ ε := by
  obtain ⟨A, hA, C, hC, hdec⟩ :=
    hurstHolder_stride_first_correlation_decay p a b M hp ha hb hab hM 1
      (by norm_num)
  let e : ℕ → ℝ := fun n => 4 * gridCovarianceError b C n
  have he0 : ∀ᶠ n in atTop, 0 ≤ e n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [e]
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  have hgeom := localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos hδ0 hN
  have herateFull : Tendsto (fun n : ℕ => (n : ℝ) * (e n) ^ 2)
      atTop (nhds 0) := by
    simpa only [e, mul_zero, show ∀ n : ℕ,
        (n : ℝ) * (4 * gridCovarianceError b C n) ^ 2 =
          16 * ((n : ℝ) * (gridCovarianceError b C n) ^ 2) by
            intro n; ring] using
      (gridCovarianceError_square_row_tendsto b C hb).const_mul 16
  have herate := localWeightActiveSet_card_mul_sq_tendsto_zero 1 δ t e he0 herateFull
  have herr : ∀ᶠ n in atTop,
      ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridStrideFirstCoefficients n 1
            (localWeightActiveIndex n 1 (δ n) t i))
          (gridStrideFirstCoefficients n 1
            (localWeightActiveIndex n 1 (δ n) t j))| ≤
          (4 * A) * strideFirstDecay b 1 (Nat.dist j.val i.val) + e n := by
    filter_upwards [hdec, hδpos, hgeom.1, eventually_ge_atTop 2] with
        n hn hnδ hncard hn2
    obtain ⟨_, hrow⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i j
    have hh := hrow
      (localWeightActiveIndex n 1 (δ n) t i)
      (localWeightActiveIndex n 1 (δ n) t j)
    rw [localWeightActiveIndex_physical_dist_eq_rank_dist
      n 1 hn0 (δ n) t hnδ hncard j i] at hh
    simpa only [e, gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n)] using hh
  exact correlation_square_average_tail_vanishes
    (fun n => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n i j => featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridStrideFirstCoefficients n 1
        (localWeightActiveIndex n 1 (δ n) t i))
      (gridStrideFirstCoefficients n 1
        (localWeightActiveIndex n 1 (δ n) t j)))
    (strideFirstDecay b 1) (strideFirstDecay_square_summable b hb 1 (by norm_num))
    (strideFirstDecay_nonneg b 1) (4 * A) (by positivity) e he0 hgeom.1 herr herate

/-- The exact B&S covariance-square tail condition on the increasing active
q=2 local window. -/
theorem hurstHolder_grid_second_active_correlation_square_average_tail
    (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 2 (δ n) t).card : ℝ)⁻¹ *
        ∑ i, ∑ j,
          (if K < Nat.dist i.val j.val then
            |featureCorrelation
              (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
              (gridSecondCoefficients n
                (localWeightActiveIndex n 2 (δ n) t i))
              (gridSecondCoefficients n
                (localWeightActiveIndex n 2 (δ n) t j))| ^ 2 else 0) ≤ ε := by
  obtain ⟨A, hA, C, hC, hdec⟩ :=
    hurstHolder_stride_second_correlation_decay p a b M hp ha hb hab hM 1
      (by norm_num)
  let e : ℕ → ℝ := fun n => A * gridCovarianceError (1 / 2) C n
  have he0 : ∀ᶠ n in atTop, 0 ≤ e n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [e]
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  have hgeom := localWeightActiveSet_card_ratio_tendsto_two 2 t ht δ hδpos hδ0 hN
  have herateFull : Tendsto (fun n : ℕ => (n : ℝ) * (e n) ^ 2)
      atTop (nhds 0) := by
    simpa only [e, mul_zero, show ∀ n : ℕ,
        (n : ℝ) * (A * gridCovarianceError (1 / 2) C n) ^ 2 =
          A ^ 2 * ((n : ℝ) * (gridCovarianceError (1 / 2) C n) ^ 2) by
            intro n; ring] using
      (gridCovarianceError_square_row_tendsto (1 / 2) C (by norm_num)).const_mul (A ^ 2)
  have herate := localWeightActiveSet_card_mul_sq_tendsto_zero 2 δ t e he0 herateFull
  have herr : ∀ᶠ n in atTop,
      ∀ i j : Fin (localWeightActiveSet n 2 (δ n) t).card,
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridSecondCoefficients n
            (localWeightActiveIndex n 2 (δ n) t i))
          (gridSecondCoefficients n
            (localWeightActiveIndex n 2 (δ n) t j))| ≤
          A * strideSecondDecay b 1 (Nat.dist j.val i.val) + e n := by
    filter_upwards [hdec, hδpos, hgeom.1, eventually_ge_atTop 3] with
        n hn hnδ hncard hn3
    obtain ⟨_, hrow⟩ := hn f hf hF
    have hn0 : 0 < n := by omega
    intro i j
    have hh := hrow
      (localWeightActiveIndex n 2 (δ n) t i)
      (localWeightActiveIndex n 2 (δ n) t j)
    rw [localWeightActiveIndex_physical_dist_eq_rank_dist
      n 2 hn0 (δ n) t hnδ hncard j i] at hh
    rw [← gridStrideSecondCoefficients_one n,
      gridStrideSecond_correlation_identity n 1 hn0 (by norm_num)
        (midpointSampleHurst f hf.1 n)]
    simpa only [e] using hh
  exact correlation_square_average_tail_vanishes
    (fun n => (localWeightActiveSet n 2 (δ n) t).card)
    (fun n i j => featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridSecondCoefficients n
        (localWeightActiveIndex n 2 (δ n) t i))
      (gridSecondCoefficients n
        (localWeightActiveIndex n 2 (δ n) t j)))
    (strideSecondDecay b 1) (strideSecondDecay_square_summable b hb 1 (by norm_num))
    (strideSecondDecay_nonneg b 1) A hA e he0 hgeom.1 herr herate

end Hurst
