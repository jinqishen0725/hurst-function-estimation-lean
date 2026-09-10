import Hurst.ActualFullTruncatedCovarianceLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- The q=1 finite-Hermite variance has the frozen long-run variance limit. -/
theorem hurstHolder_stride_first_full_truncatedVariance_tendsto
    (p a b M : ℝ) (r K : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => Var[fun x => Real.sqrt ((n : ℝ) * δ n) *
      gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (δ n) t)
        (gridStrideFirstCoefficients n 1) K x;
          featureGaussian (gridObservationFeatures n
            (midpointSampleHurst f hf.1 n))]) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ∑' k : ℕ, (if k = 0 then 1 else 2) *
          gaussianLogTruncationCovariance K
            (firstIncrementLagCorrelation (f t) k))) := by
  have hcov := hurstHolder_stride_first_full_truncatedCovariance_tendsto
    p a b M r K hp ha hb hab hM f hf hF t ht δ hδpos hδ hN
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM 1 (by norm_num)
  apply hcov.congr'
  filter_upwards [hrows, hδpos, eventually_ge_atTop 1] with n hn hnδ hn1
  obtain ⟨hzero, _⟩ := hn f hf hF
  have hn0 : 0 < n := by omega
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := localPolynomialWeights r n 1 (δ n) t
  let c := gridStrideFirstCoefficients n 1
  have hfeat : ∀ i, ∑ j, c i j • v j ≠ 0 := by
    intro i
    dsimp only [c, v]
    rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n) i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  rw [variance_const_mul,
    featureGaussian_logTruncation_variance v w c hfeat K,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hnδ.le)]
  unfold actualStrideFirstFullTruncatedCovariance
  dsimp only [v, w, c]
  simp only [gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
    (midpointSampleHurst f hf.1 n)]

/-- The q=2 finite-Hermite variance has the frozen long-run variance limit. -/
theorem hurstHolder_grid_second_full_truncatedVariance_tendsto
    (p a b M : ℝ) (r K : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (nhds 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => Var[fun x => Real.sqrt ((n : ℝ) * δ n) *
      gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 2 (δ n) t) (gridSecondCoefficients n) K x;
          featureGaussian (gridObservationFeatures n
            (midpointSampleHurst f hf.1 n))]) atTop
      (nhds ((∫ x in (-1 : ℝ)..1, equivalentKernel r x ^ 2) *
        ∑' k : ℕ, (if k = 0 then 1 else 2) *
          gaussianLogTruncationCovariance K
            (secondIncrementLagCorrelation (f t) k))) := by
  have hcov := hurstHolder_grid_second_full_truncatedCovariance_tendsto
    p a b M r K hp ha hb hab hM f hf hF t ht δ hδpos hδ hN
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_grid_second_correlation_rows p a b M hp ha hb hab hM
  apply hcov.congr'
  filter_upwards [hrows, hδpos, eventually_ge_atTop 2] with n hn hnδ hn2
  obtain ⟨hzero, _⟩ := hn f hf hF
  have hn0 : 0 < n := by omega
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := localPolynomialWeights r n 2 (δ n) t
  let c := gridSecondCoefficients n
  have hfeat : ∀ i, ∑ j, c i j • v j ≠ 0 := by
    intro i
    dsimp only [c, v]
    rw [gridSecond_feature_identity n hn0
      (midpointSampleHurst f hf.1 n) i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  rw [variance_const_mul,
    featureGaussian_logTruncation_variance v w c hfeat K,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hnδ.le)]
  unfold actualSecondFullTruncatedCovariance
  dsimp only [v, w, c]
  simp only [gridSecond_correlation_identity n hn0
    (midpointSampleHurst f hf.1 n)]

end Hurst
