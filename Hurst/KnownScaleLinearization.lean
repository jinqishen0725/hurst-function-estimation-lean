import Hurst.SecondEstimatorLinearization
import Hurst.FirstEstimatorLinearization
import Hurst.KnownScaleRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q2_known_scale_L1_linearization (a b M u : ℝ) (r : ℕ) (hr : 1≤r)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hu : u<1)
    (σ : ℝ) (hσ : σ≠0) (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u) :
    Tendsto (fun n : ℕ => (∫ x,|q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t (σ⁻¹ • x)-f t+
      (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridSecondCoefficients n) (σ⁻¹ • x)-
          (calibrationTwo (Real.log n) gaussianLogSquareMean (f t)))/(2*Real.log n)|
      ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop (𝓝 0) := by
  convert hurstHolder_q2_L1_linearization a b M u r hr ha hb hab hM hu f hf hF hfc t ht htu using 1
  funext n
  congr 1
  exact featureGaussian_known_scale_integral (gridObservationFeatures n (midpointSampleHurst f hf.1 n)) σ hσ (fun x => |q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t+
      (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridSecondCoefficients n) x-
          calibrationTwo (Real.log n) gaussianLogSquareMean (f t))/(2*Real.log n)|)

theorem hurstHolder_q1_known_scale_L1_linearization (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (σ : ℝ) (hσ : σ≠0) (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n : ℕ => (∫ x,|q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t (σ⁻¹ • x)-f t+
      (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridDifferenceCoefficients n) (σ⁻¹ • x)-
          (calibrationOne (Real.log n) gaussianLogSquareMean (f t)))/(2*Real.log n)|
      ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop (𝓝 0) := by
  convert hurstHolder_q1_L1_linearization a b M r ha hb hab hM f hf hF hfc t ht using 1
  funext n
  congr 1
  exact featureGaussian_known_scale_integral (gridObservationFeatures n (midpointSampleHurst f hf.1 n)) σ hσ (fun x => |q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t+
      (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridDifferenceCoefficients n) x-
          calibrationOne (Real.log n) gaussianLogSquareMean (f t))/(2*Real.log n)|)

end Hurst
