import Hurst.ActualWeightedMemoryMainline
import Hurst.TwoBandwidthScale
import Hurst.EventualWeightMass

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem hurstHolder_q1_conditional_all_scale_memory_mainline (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (δ₁ δ₂ A : ℕ → ℝ) (m : ℕ → ℕ)
    (hA : ∀ᶠ n in atTop,0≤A n)
    (hδ₁ : ∀ᶠ n in atTop,0<δ₁ n) (hδ₁0 : Tendsto δ₁ atTop (𝓝 0))
    (hN₁ : Tendsto (fun n : ℕ => (n:ℝ)*δ₁ n) atTop atTop)
    (hδ₂ : ∀ᶠ n in atTop,0<δ₂ n) (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hN₂ : Tendsto (fun n : ℕ => (n:ℝ)*δ₂ n) atTop atTop)
    (hm : ∀ᶠ n in atTop,0<m n) (σ : ℝ) (hσ : σ≠0)
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
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1LocalEstimator r n (δ₂ n) t (σ⁻¹ • x)-f t)) atTop
      (fun z => -Z z-β) (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop
      (fun z => -Z z-β) (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' := by
  have hh := hurstHolder_q1_conditional_weighted_memory_mainline p a b M r hp ha hb hab hM f hf hF t ht
    δ₁ δ₂ A m hA P' Z β htail hquad hmean hQ hscale
  refine ⟨?_,?_⟩
  · apply featureGaussian_known_scale_distribution P'
      (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)) _ _ _ σ hσ hh.1
    intro n
    exact normalized_q1_inverse_measurable n
      (gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n))
      (by unfold gaussianLogStatistic; fun_prop) (A n) (f t)
  · exact hurstHolder_q1_twoBandwidth_scale_distribution_transfer p a b M r hp ha hb hab hM f hf hF
      t δ₁ δ₂ A m σ hσ
      ((localPolynomialWeights_eventual_mass r 1 δ₂ hδ₂ hδ₂0 hN₂).mono (fun n hn => hn t ⟨ht.1.le,ht.2.le⟩))
      (averagedLocalWeights_eventual_mass r 2 m δ₁ hm hδ₁ hδ₁0 hN₁) P' _ hh.2

end Hurst
