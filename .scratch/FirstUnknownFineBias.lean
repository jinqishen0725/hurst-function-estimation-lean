import Hurst.FirstUnknownConditionalBias
import Hurst.FirstScaleNegligible

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_unknown_expected_bias_leading (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n : ℕ => ((∫ x,q1UnknownLocalEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-f t)/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop
      (𝓝 ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))) := by
  exact hurstHolder_q1_unknown_bias_of_scale_L1 a b M r ha hb hab hM f hf hF hfc t ht
    (hurstHolder_q1_scale_L1_negligible a b M r ha hb hab hM f hf hF)

end Hurst
