import Hurst.FeatureHermiteApproximation
import Hurst.WeightEnergy
import Hurst.SecondGridLogVariance
import Hurst.FirstStrideActualRows

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_grid_second_log_truncation_error (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ → ∀ K : ℕ,
      (n : ℝ)*δ*(∫ x,(gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
        gaussianLogTruncationStatistic (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) K x)^2
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
      C*‖hermiteTail gaussianLogLp K‖^2 := by
  obtain ⟨R,hR,hrows⟩ := hurstHolder_grid_second_correlation_rows p a b M hp ha hb hab hM
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_energy r 2
  refine ⟨N₀,hN₀,R*D,mul_nonneg hR hD.le,?_⟩
  filter_upwards [hrows,eventually_ge_atTop 2] with n hrows hn
  intro f hf hF δ t hδ hδhalf ht hN K
  let H := midpointSampleHurst f hf.1 n
  have hn0 : 0<n := by omega
  have hnf : (0:ℝ)<n := by exact_mod_cast hn0
  obtain ⟨hzero,hrow⟩ := hrows f hf hF
  have hfeat : ∀ i,∑ j,gridSecondCoefficients n i j • gridObservationFeatures n H j≠0 := by
    intro i
    rw [gridSecond_feature_identity n hn0 H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  have he := featureGaussian_log_truncation_error (gridObservationFeatures n H)
    (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) hfeat R
    (by intro i; simpa only [gridSecond_correlation_identity n hn0 H] using hrow i) K
  have hew := hw n hn0 hn δ t hδ hδhalf ht hN
  calc
    _ ≤ (n:ℝ)*δ*(‖hermiteTail gaussianLogLp K‖^2*R*∑ i,localPolynomialWeights r n 2 δ t i^2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (‖hermiteTail gaussianLogLp K‖^2*R)*((n:ℝ)*δ*∑ i,localPolynomialWeights r n 2 δ t i^2) := by ring
    _ ≤ (‖hermiteTail gaussianLogLp K‖^2*R)*D :=
      mul_le_mul_of_nonneg_left hew (mul_nonneg (sq_nonneg _) hR)
    _ = _ := by ring

theorem hurstHolder_stride_first_log_truncation_error (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0<d) :
    ∃ N₀ > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ → ∀ K : ℕ,
      (n : ℝ)*δ*(∫ x,(gaussianLogStatistic (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
        gaussianLogTruncationStatistic (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) K x)^2
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
      C*‖hermiteTail gaussianLogLp K‖^2 := by
  obtain ⟨R,hR,hrows⟩ := hurstHolder_stride_first_correlation_rows p a b M hp ha hb hab hM d hd
  obtain ⟨N₀,hN₀,D,hD,hw⟩ := localPolynomialWeights_energy r d
  refine ⟨N₀,hN₀,R*D,mul_nonneg hR hD.le,?_⟩
  filter_upwards [hrows,eventually_ge_atTop d] with n hrows hn
  intro f hf hF δ t hδ hδhalf ht hN K
  let H := midpointSampleHurst f hf.1 n
  have hn0 : 0<n := by omega
  have hnf : (0:ℝ)<n := by exact_mod_cast hn0
  obtain ⟨hzero,hrow⟩ := hrows f hf hF
  have hfeat : ∀ i,∑ j,gridStrideFirstCoefficients n d i j • gridObservationFeatures n H j≠0 := by
    intro i
    rw [gridStrideFirst_feature_identity n d hn0 hd H i]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hzero i)
  have he := featureGaussian_log_truncation_error (gridObservationFeatures n H)
    (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) hfeat R
    (by intro i; simpa only [gridStrideFirst_correlation_identity n d hn0 hd H] using hrow i) K
  have hew := hw n hn0 hn δ t hδ hδhalf ht hN
  calc
    _ ≤ (n:ℝ)*δ*(‖hermiteTail gaussianLogLp K‖^2*R*∑ i,localPolynomialWeights r n d δ t i^2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (‖hermiteTail gaussianLogLp K‖^2*R)*((n:ℝ)*δ*∑ i,localPolynomialWeights r n d δ t i^2) := by ring
    _ ≤ (‖hermiteTail gaussianLogLp K‖^2*R)*D :=
      mul_le_mul_of_nonneg_left hew (mul_nonneg (sq_nonneg _) hR)
    _ = _ := by ring

theorem hurstHolder_grid_second_log_truncation_uniform (p a b M : ℝ) (r : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∀ ε : ℝ, 0<ε → ∃ K₀ : ℕ, ∀ K≥K₀, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      (n : ℝ)*δ*(∫ x,(gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
        gaussianLogTruncationStatistic (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) K x)^2
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) < ε := by
  obtain ⟨N₀,hN₀,C,hC,he⟩ := hurstHolder_grid_second_log_truncation_error p a b M r hp ha hb hab hM
  refine ⟨N₀,hN₀,?_⟩
  intro ε hε
  have ht : Tendsto (fun K => C*‖hermiteTail gaussianLogLp K‖^2) atTop (𝓝 0) := by
    simpa using (hermiteTail_norm_sq_tendsto gaussianLogLp).const_mul C
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨K₀,?_⟩
  intro K hK
  filter_upwards [he] with n hn
  intro f hf hF δ t hδ hδ2 htt hN
  exact (hn f hf hF δ t hδ hδ2 htt hN K).trans_lt (hK₀ K hK)

theorem hurstHolder_stride_first_log_truncation_uniform (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0<d) :
    ∃ N₀ > 0, ∀ ε : ℝ, 0<ε → ∃ K₀ : ℕ, ∀ K≥K₀, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      (n : ℝ)*δ*(∫ x,(gaussianLogStatistic (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
        gaussianLogTruncationStatistic (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n d δ t) (gridStrideFirstCoefficients n d) K x)^2
            ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) < ε := by
  obtain ⟨N₀,hN₀,C,hC,he⟩ := hurstHolder_stride_first_log_truncation_error p a b M r hp ha hb hab hM d hd
  refine ⟨N₀,hN₀,?_⟩
  intro ε hε
  have ht : Tendsto (fun K => C*‖hermiteTail gaussianLogLp K‖^2) atTop (𝓝 0) := by
    simpa using (hermiteTail_norm_sq_tendsto gaussianLogLp).const_mul C
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨K₀,?_⟩
  intro K hK
  filter_upwards [he] with n hn
  intro f hf hF δ t hδ hδ2 htt hN
  exact (hn f hf hF δ t hδ hδ2 htt hN K).trans_lt (hK₀ K hK)

end Hurst
