import Hurst.FullVarianceGeneric
import Hurst.FrozenLagSummability
import Hurst.ActualTruncatedVarianceJunction

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Scaled full q=1 covariance matrix for the finite Hermite truncation. -/
def actualStrideFirstFullTruncatedCovariance
    (r K : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * δ n * ∑ i, ∑ j,
    localPolynomialWeights r n 1 (δ n) t i *
      localPolynomialWeights r n 1 (δ n) t j *
        gaussianLogTruncationCovariance K
          (vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf n) i)
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf n) j))

theorem hurstHolder_stride_first_full_truncatedCovariance_tendsto
    (p a b M : ℝ) (r K : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (actualStrideFirstFullTruncatedCovariance r K f hf.1 t δ)
      atTop (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ∑' k : ℕ, (if k = 0 then 1 else 2) *
          gaussianLogTruncationCovariance K
            (firstIncrementLagCorrelation (f t) k))) := by
  let scale : ℕ → ℝ := fun n => (n : ℝ) * δ n
  let corr : ∀ n, Fin (n - 1) → Fin (n - 1) → ℝ := fun n i j =>
    vectorCorrelation
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) i)
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) j)
  let approx : ℕ → ℕ → ℝ := fun R n =>
    ∑ k ∈ Finset.range (R + 1),
      actualStrideFirstTruncatedLagContribution r K f hf.1 t δ n k
  let lim : ℕ → ℝ := fun R =>
    (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
      ∑ k ∈ Finset.range (R + 1), (if k = 0 then 1 else 2) *
        gaussianLogTruncationCovariance K
          (firstIncrementLagCorrelation (f t) k)
  apply tendsto_of_finiteCutoff_and_uniformTail
    (actualStrideFirstFullTruncatedCovariance r K f hf.1 t δ)
    approx lim
  · intro R
    exact hurstHolder_stride_first_finiteLag_truncatedVariance_tendsto
      p a b M r K (R + 1) hp ha (by linarith) hab hM f hf hF t ht
      δ hδpos hδ hN
  · intro ε hε
    have hcorr : ∀ n i j, |corr n i j| ≤ 1 := by
      intro n i j
      dsimp only [corr]
      simpa only [vectorCorrelation] using
        abs_real_inner_div_norm_mul_norm_le_one
          (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) i)
          (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) j)
    have hrow := hurstHolder_stride_first_correlation_square_row_tail
      p a b M hp ha hb hab hM f hf hF
    have hut := localPolynomialWeights_truncationCovariance_uniform_tail
      r 1 K t ⟨ht.1.le, ht.2.le⟩ δ hδpos hδ hN corr hcorr hrow ε hε
    filter_upwards [hut] with R hR
    filter_upwards [hR, hδpos, eventually_ge_atTop 1] with n hn hnδ hn1
    have hspos : 0 < scale n := by dsimp only [scale]; positivity
    have hj := actualStrideFirst_finiteLag_eq_distance_sum
      r K (R + 1) n f hf.1 t δ
    dsimp only [approx]
    rw [hj]
    unfold actualStrideFirstFullTruncatedCovariance
    dsimp only [corr, scale] at hn hspos ⊢
    let F : Fin (n - 1) → Fin (n - 1) → ℝ := fun i j =>
      localPolynomialWeights r n 1 (δ n) t i *
        localPolynomialWeights r n 1 (δ n) t j *
          gaussianLogTruncationCovariance K
            (vectorCorrelation
              (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) i)
              (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) j))
    have hsplit := finite_double_sum_sub_distance_lt_succ_eq_tail
      (n - 1) R F
    change |((n : ℝ) * δ n) * (∑ i, ∑ j, F i j) -
      ((n : ℝ) * δ n) *
        (∑ i, ∑ j, if Nat.dist i.val j.val < R + 1 then F i j else 0)| < ε
    rw [← mul_sub, abs_mul, abs_of_pos hspos, hsplit]
    simpa only [F, Nat.dist_comm] using hn
  · have hsum := (firstIncrement_symmetric_truncationCovariance_summable
      K (f t) (ha.trans_le (hF ht).1) (lt_of_le_of_lt (hF ht).2 hb)).hasSum.tendsto_sum_nat
    have hsucc : Tendsto (fun R : ℕ => R + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (fun R => Nat.le_add_right R 1) tendsto_id
    simpa only [lim, Function.comp_apply] using
      (hsum.comp hsucc).const_mul
        (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2)

/-- Scaled full q=2 covariance matrix for the finite Hermite truncation. -/
def actualSecondFullTruncatedCovariance
    (r K : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * δ n * ∑ i, ∑ j,
    localPolynomialWeights r n 2 (δ n) t i *
      localPolynomialWeights r n 2 (δ n) t j *
        gaussianLogTruncationCovariance K
          (vectorCorrelation
            (gridSecondActual n (midpointSampleHurst f hf n) i)
            (gridSecondActual n (midpointSampleHurst f hf n) j))

theorem hurstHolder_grid_second_full_truncatedCovariance_tendsto
    (p a b M : ℝ) (r K : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (actualSecondFullTruncatedCovariance r K f hf.1 t δ)
      atTop (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ∑' k : ℕ, (if k = 0 then 1 else 2) *
          gaussianLogTruncationCovariance K
            (secondIncrementLagCorrelation (f t) k))) := by
  let corr : ∀ n, Fin (n - 2) → Fin (n - 2) → ℝ := fun n i j =>
    vectorCorrelation
      (gridSecondActual n (midpointSampleHurst f hf.1 n) i)
      (gridSecondActual n (midpointSampleHurst f hf.1 n) j)
  let approx : ℕ → ℕ → ℝ := fun R n =>
    ∑ k ∈ Finset.range (R + 1),
      actualSecondTruncatedLagContribution r K f hf.1 t δ n k
  let lim : ℕ → ℝ := fun R =>
    (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
      ∑ k ∈ Finset.range (R + 1), (if k = 0 then 1 else 2) *
        gaussianLogTruncationCovariance K
          (secondIncrementLagCorrelation (f t) k)
  apply tendsto_of_finiteCutoff_and_uniformTail
    (actualSecondFullTruncatedCovariance r K f hf.1 t δ)
    approx lim
  · intro R
    exact hurstHolder_grid_second_finiteLag_truncatedVariance_tendsto
      p a b M r K (R + 1) hp ha hb hab hM f hf hF t ht δ hδpos hδ hN
  · intro ε hε
    have hcorr : ∀ n i j, |corr n i j| ≤ 1 := by
      intro n i j
      dsimp only [corr]
      simpa only [vectorCorrelation] using
        abs_real_inner_div_norm_mul_norm_le_one
          (gridSecondActual n (midpointSampleHurst f hf.1 n) i)
          (gridSecondActual n (midpointSampleHurst f hf.1 n) j)
    have hrow : ∀ ε > 0, ∃ R : ℕ, ∀ᶠ n in atTop, ∀ i,
        ∑ j, (if R < Nat.dist j.val i.val then |corr n i j| ^ 2 else 0) ≤ ε := by
      intro η hη
      obtain ⟨R, hR⟩ := hurstHolder_grid_second_correlation_square_row_tail
        p a b M hp ha hb hab hM f hf hF η hη
      refine ⟨R, ?_⟩
      filter_upwards [hR, eventually_ge_atTop 1] with n hn hn1
      intro i
      simpa only [corr, gridSecond_correlation_identity n (by omega)
        (midpointSampleHurst f hf.1 n)] using hn i
    have hut := localPolynomialWeights_truncationCovariance_uniform_tail
      r 2 K t ⟨ht.1.le, ht.2.le⟩ δ hδpos hδ hN corr hcorr hrow ε hε
    filter_upwards [hut] with R hR
    filter_upwards [hR, hδpos, eventually_ge_atTop 1] with n hn hnδ hn1
    have hspos : 0 < (n : ℝ) * δ n := by positivity
    have hj := actualSecond_finiteLag_eq_distance_sum
      r K (R + 1) n f hf.1 t δ
    dsimp only [approx]
    rw [hj]
    unfold actualSecondFullTruncatedCovariance
    dsimp only [corr] at hn ⊢
    let F : Fin (n - 2) → Fin (n - 2) → ℝ := fun i j =>
      localPolynomialWeights r n 2 (δ n) t i *
        localPolynomialWeights r n 2 (δ n) t j *
          gaussianLogTruncationCovariance K
            (vectorCorrelation
              (gridSecondActual n (midpointSampleHurst f hf.1 n) i)
              (gridSecondActual n (midpointSampleHurst f hf.1 n) j))
    have hsplit := finite_double_sum_sub_distance_lt_succ_eq_tail
      (n - 2) R F
    change |((n : ℝ) * δ n) * (∑ i, ∑ j, F i j) -
      ((n : ℝ) * δ n) *
        (∑ i, ∑ j, if Nat.dist i.val j.val < R + 1 then F i j else 0)| < ε
    rw [← mul_sub, abs_mul, abs_of_pos hspos, hsplit]
    simpa only [F, Nat.dist_comm] using hn
  · have hsum := (secondIncrement_symmetric_truncationCovariance_summable
      K (f t) (ha.trans_le (hF ht).1) (lt_of_le_of_lt (hF ht).2 hb)).hasSum.tendsto_sum_nat
    have hsucc : Tendsto (fun R : ℕ => R + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (fun R => Nat.le_add_right R 1) tendsto_id
    simpa only [lim, Function.comp_apply] using
      (hsum.comp hsucc).const_mul
        (∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2)

end Hurst
