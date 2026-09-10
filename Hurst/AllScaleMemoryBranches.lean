import Hurst.AllScaleMemoryMainline
import Hurst.ActualMemoryBranches

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem hurstHolder_q1_conditional_all_scale_critical_mainline (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (δ₁ δ₂ : ℕ → ℝ) (m : ℕ → ℕ)
    (hcrit : f t=3/4)
    (hδ₁ : ∀ᶠ n in atTop,0<δ₁ n) (hδ₁0 : Tendsto δ₁ atTop (𝓝 0))
    (hN₁ : Tendsto (fun n : ℕ => (n:ℝ)*δ₁ n) atTop atTop)
    (hδ₂ : ∀ᶠ n in atTop,0<δ₂ n) (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hN₂ : Tendsto (fun n : ℕ => (n:ℝ)*δ₂ n) atTop atTop)
    (hm : ∀ᶠ n in atTop,0<m n) (σ : ℝ) (hσ : σ≠0)
    
    (htail : Tendsto (fun (n : ℕ) => ((firstCriticalNormalization n (δ₂ n)))^2*(∑ i,∑ j,|localPolynomialWeights r n 1 (δ₂ n) t i| * |localPolynomialWeights r n 1 (δ₂ n) t j| *
      |featureCorrelation (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridDifferenceCoefficients n i) (gridDifferenceCoefficients n j)|^4)) atTop (𝓝 0))
    (hquad : TendstoInDistribution (fun (n : ℕ) x => (firstCriticalNormalization n (δ₂ n))*gaussianLogQuadraticStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x) atTop (fun z : ℝ => Real.sqrt (firstCriticalVariance r)*z)
      (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1))
    (hmean : Tendsto (fun n : ℕ => (firstCriticalNormalization n (δ₂ n))*((∫ x,
      gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
          calibrationOne (Real.log n) gaussianLogSquareMean (f t))) atTop (𝓝 0))
    (hQ : Tendsto (fun n : ℕ => (firstCriticalNormalization n (δ₂ n))*(∫ x,
      (gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x-
        calibrationOne (Real.log n) gaussianLogSquareMean (f t))^2
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/Real.log n) atTop (𝓝 0))
    (hscale : Tendsto (fun (n : ℕ) => (firstCriticalNormalization n (δ₂ n))*(∫ x,|q1LogScaleEstimator r n (m n) (δ₁ n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstCriticalNormalization n (δ₂ n))*Real.log n*(q1LocalEstimator r n (δ₂ n) t (σ⁻¹ • x)-f t)) atTop
      (fun z => -(Real.sqrt (firstCriticalVariance r)*z)) (fun (n : ℕ) => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstCriticalNormalization n (δ₂ n))*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop
      (fun z => -(Real.sqrt (firstCriticalVariance r)*z)) (fun (n : ℕ) => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  have hh := hurstHolder_q1_conditional_all_scale_memory_mainline p a b M r hp ha hb hab hM f hf hF t ht
    δ₁ δ₂ (fun (n : ℕ) => firstCriticalNormalization n (δ₂ n)) m (Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)) hδ₁ hδ₁0 hN₁ hδ₂ hδ₂0 hN₂ hm σ hσ
    (gaussianReal 0 1) (fun z : ℝ => Real.sqrt (firstCriticalVariance r)*z) 0 htail hquad hmean hQ hscale
  simpa only [sub_zero] using hh

theorem hurstHolder_q1_conditional_all_scale_long_mainline (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (δ₁ δ₂ : ℕ → ℝ) (m : ℕ → ℕ)
    (hlong : 3/4<f t)
    (hδ₁ : ∀ᶠ n in atTop,0<δ₁ n) (hδ₁0 : Tendsto δ₁ atTop (𝓝 0))
    (hN₁ : Tendsto (fun n : ℕ => (n:ℝ)*δ₁ n) atTop atTop)
    (hδ₂ : ∀ᶠ n in atTop,0<δ₂ n) (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hN₂ : Tendsto (fun n : ℕ => (n:ℝ)*δ₂ n) atTop atTop)
    (hm : ∀ᶠ n in atTop,0<m n) (σ : ℝ) (hσ : σ≠0)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Q : Ω' → ℝ)
    (htail : Tendsto (fun (n : ℕ) => ((firstLongNormalization (f t) n (δ₂ n)))^2*(∑ i,∑ j,|localPolynomialWeights r n 1 (δ₂ n) t i| * |localPolynomialWeights r n 1 (δ₂ n) t j| *
      |featureCorrelation (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridDifferenceCoefficients n i) (gridDifferenceCoefficients n j)|^4)) atTop (𝓝 0))
    (hquad : TendstoInDistribution (fun (n : ℕ) x => (firstLongNormalization (f t) n (δ₂ n))*gaussianLogQuadraticStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x) atTop Q
      (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P')
    (hmean : Tendsto (fun n : ℕ => (firstLongNormalization (f t) n (δ₂ n))*((∫ x,
      gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-
          calibrationOne (Real.log n) gaussianLogSquareMean (f t))) atTop (𝓝 0))
    (hQ : Tendsto (fun n : ℕ => (firstLongNormalization (f t) n (δ₂ n))*(∫ x,
      (gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n) x-
        calibrationOne (Real.log n) gaussianLogSquareMean (f t))^2
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/Real.log n) atTop (𝓝 0))
    (hscale : Tendsto (fun (n : ℕ) => (firstLongNormalization (f t) n (δ₂ n))*(∫ x,|q1LogScaleEstimator r n (m n) (δ₁ n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstLongNormalization (f t) n (δ₂ n))*Real.log n*(q1LocalEstimator r n (δ₂ n) t (σ⁻¹ • x)-f t)) atTop
      (fun z => -Q z) (fun (n : ℕ) => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstLongNormalization (f t) n (δ₂ n))*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop
      (fun z => -Q z) (fun (n : ℕ) => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' := by
  have hA : ∀ᶠ n in atTop,0≤firstLongNormalization (f t) n (δ₂ n) := by
    filter_upwards [hδ₂] with n hn
    exact Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) hn.le) _
  have hh := hurstHolder_q1_conditional_all_scale_memory_mainline p a b M r hp ha hb hab hM f hf hF t ht
    δ₁ δ₂ (fun (n : ℕ) => firstLongNormalization (f t) n (δ₂ n)) m hA hδ₁ hδ₁0 hN₁ hδ₂ hδ₂0 hN₂ hm σ hσ
    P' Q 0 htail hquad hmean hQ hscale
  simpa only [sub_zero] using hh

end Hurst
