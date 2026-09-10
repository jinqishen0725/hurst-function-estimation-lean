import Hurst.SecondEstimatorBias
import Hurst.FirstEstimatorBias
import Hurst.KnownScaleRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q2_known_scale_expected_bias_leading (a b M u : ℝ) (r : ℕ) (hr : 1≤r)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hu : u<1)
    (σ : ℝ) (hσ : σ≠0) (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u) :
    Tendsto (fun n : ℕ => ((∫ x,q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t (σ⁻¹ • x)
      ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))-f t)/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop
      (𝓝 ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))) := by
  simp_rw [featureGaussian_known_scale_integral _ σ hσ]
  exact hurstHolder_q2_expected_bias_leading a b M u r hr ha hb hab hM hu f hf hF hfc t ht htu

theorem hurstHolder_q1_known_scale_expected_bias_leading (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (σ : ℝ) (hσ : σ≠0) (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n : ℕ => ((∫ x,q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t (σ⁻¹ • x)
      ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))-f t)/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop
      (𝓝 ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))) := by
  simp_rw [featureGaussian_known_scale_integral _ σ hσ]
  exact hurstHolder_q1_expected_bias_leading a b M r ha hb hab hM f hf hF hfc t ht

end Hurst
