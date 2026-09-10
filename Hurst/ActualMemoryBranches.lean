import Hurst.ActualMemoryMainline
import Hurst.EquivalentKernel

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

def firstCriticalNormalization (n : ℕ) (δ : ℝ) : ℝ := Real.sqrt ((n:ℝ)*δ/Real.log ((n:ℝ)*δ))
def firstLongNormalization (h : ℝ) (n : ℕ) (δ : ℝ) : ℝ := ((n:ℝ)*δ)^(2-2*h)
def firstCriticalVariance (r : ℕ) : ℝ := (9/16)*(∫ z in Icc (-1:ℝ) 1,(equivalentKernel r z)^2)

theorem hurstHolder_q1_conditional_critical_mainline (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (δ₁ δ₂ R : ℕ → ℝ) (m : ℕ → ℕ)
    (hcrit : f t=3/4)
    
    (hrows : ∀ᶠ n in atTop,∀ i,∑ j,|featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridDifferenceCoefficients n i) (gridDifferenceCoefficients n j)|^4≤R n)
    (htail : Tendsto (fun (n : ℕ) => ((firstCriticalNormalization n (δ₂ n)))^2*R n*∑ i,localPolynomialWeights r n 1 (δ₂ n) t i^2) atTop (𝓝 0))
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
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstCriticalNormalization n (δ₂ n))*Real.log n*(q1LocalEstimator r n (δ₂ n) t x-f t)) atTop
      (fun z => -(Real.sqrt (firstCriticalVariance r)*z)) (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstCriticalNormalization n (δ₂ n))*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop
      (fun z => -(Real.sqrt (firstCriticalVariance r)*z)) (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) := by
  have hh := hurstHolder_q1_conditional_memory_mainline p a b M r hp ha hb hab hM f hf hF t ht
    δ₁ δ₂ (fun (n : ℕ) => firstCriticalNormalization n (δ₂ n)) R m (Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)) (gaussianReal 0 1) (fun z : ℝ => Real.sqrt (firstCriticalVariance r)*z) 0 hrows htail hquad hmean hQ hscale
  simpa only [sub_zero] using hh

theorem hurstHolder_q1_conditional_long_mainline (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (δ₁ δ₂ R : ℕ → ℝ) (m : ℕ → ℕ)
    (hlong : 3/4<f t) (hδ : ∀ᶠ n in atTop,0≤δ₂ n)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Q : Ω' → ℝ)
    (hrows : ∀ᶠ n in atTop,∀ i,∑ j,|featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (gridDifferenceCoefficients n i) (gridDifferenceCoefficients n j)|^4≤R n)
    (htail : Tendsto (fun (n : ℕ) => ((firstLongNormalization (f t) n (δ₂ n)))^2*R n*∑ i,localPolynomialWeights r n 1 (δ₂ n) t i^2) atTop (𝓝 0))
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
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstLongNormalization (f t) n (δ₂ n))*Real.log n*(q1LocalEstimator r n (δ₂ n) t x-f t)) atTop
      (fun z => -Q z) (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*(firstLongNormalization (f t) n (δ₂ n))*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop
      (fun z => -Q z) (fun (n : ℕ) => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  have hA : ∀ᶠ n in atTop,0≤firstLongNormalization (f t) n (δ₂ n) := by
    filter_upwards [hδ] with n hn
    exact Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) hn) _
  have hh := hurstHolder_q1_conditional_memory_mainline p a b M r hp ha hb hab hM f hf hF t ht
    δ₁ δ₂ (fun (n : ℕ) => firstLongNormalization (f t) n (δ₂ n)) R m hA P' Q 0 hrows htail hquad hmean hQ hscale
  simpa only [sub_zero] using hh

end Hurst
