import Hurst.ActualMemoryMainline
import Hurst.WeightedQuadraticLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem hurstHolder_q1_conditional_weighted_memory_mainline (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (δ₁ δ₂ A : ℕ → ℝ) (m : ℕ → ℕ)
    (hA : ∀ᶠ n in atTop,0≤A n)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ) (β : ℝ)
    (htail : Tendsto (fun n => (A n)^2*(∑ i,∑ j,|localPolynomialWeights r n 1 (δ₂ n) t i| * |localPolynomialWeights r n 1 (δ₂ n) t j| *
      |featureCorrelation (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridDifferenceCoefficients n i) (gridDifferenceCoefficients n j)|^4)) atTop (𝓝 0))
    (hquad : TendstoInDistribution (fun n x => A n*gaussianLogQuadraticStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P')
    (hmean : Tendsto (fun n : ℕ => A n*((∫ x,
      gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
          calibrationOne (Real.log n) gaussianLogSquareMean (f t))) atTop (𝓝 β))
    (hQ : Tendsto (fun n : ℕ => A n*(∫ x,
      (gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x-
        calibrationOne (Real.log n) gaussianLogSquareMean (f t))^2
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/Real.log n) atTop (𝓝 0))
    (hscale : Tendsto (fun n => A n*(∫ x,|q1LogScaleEstimator r n (m n) (δ₁ n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1LocalEstimator r n (δ₂ n) t x-f t)) atTop
      (fun z => -Z z-β) (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop
      (fun z => -Z z-β) (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let X := fun n => gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n)
  let S := fun n => q1LogScaleEstimator r n (m n) (δ₁ n)
  obtain ⟨C,hC,hmean0⟩ := hurstHolder_stride_first_log_mean p a b M hp ha hb hab hM 1 (by norm_num)
  have hfeat : ∀ᶠ n in atTop,∀ i,∑ j,gridDifferenceCoefficients n i j • v n j≠0 := by
    filter_upwards [hmean0] with n hn
    exact fun i => (hn f hf hF i).1
  have hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n) := by
    filter_upwards [hfeat] with n hn
    exact gaussianLogStatistic_memLp_two _ _ _ hn
  have hS := hurstHolder_q1_scale_memLp_eventually p a b M hp ha hb hab hM f hf hF r m δ₁
  have hlogCLT := featureGaussian_log_limit_of_quadratic_weighted_limit P' (fun n => Fin (n-1)) v
    (fun n => localPolynomialWeights r n 1 (δ₂ n) t) gridDifferenceCoefficients A Z hfeat htail hquad
  have hXm (n : ℕ) : AEMeasurable (X n) (P n) := by dsimp [X]; unfold gaussianLogStatistic; fun_prop
  have hknown := linearCalibration_limit P P' X (f t) gaussianLogSquareMean (hf.1 ht) hXm hX A hA Z β hlogCLT hmean hQ
  refine ⟨hknown,?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hm' (n : ℕ) : AEMeasurable (fun x => 2*A n*Real.log n*(boundedInverse
      (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (X n x-S n x)-f t)) (P n) := by
    by_cases hn : 1<n
    · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n)
        (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn
        (calibrationOne_strongDecrease _ _ _ _)).continuous.measurable
      have hs : AEMeasurable (S n) (P n) := (q1LogScaleEstimator_measurable _ _ _ _).aemeasurable
      exact (((hi.comp_aemeasurable ((hXm n).sub hs)).sub aemeasurable_const).const_mul _)
    · have hn' : n≤1 := by omega
      have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
      simp only [hl,mul_zero,zero_mul]
      exact aemeasurable_const
  exact boundedInverse_scale_distribution_transfer P P' (fun z => -Z z-β) X S
    (fun n => calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 0 (fun n => Real.log n) A (fun _ => f t)
    hX hS (hlog.eventually_gt_atTop 0) hA (by norm_num)
    (fun n => (calibrationOne_continuous _ _).continuousOn) (fun n => calibrationOne_strongDecrease _ _ _ _)
    hm' (by simpa only [sub_zero] using hscale) (by simp only [sub_zero]; convert hknown using 1 <;> rfl)

end Hurst
