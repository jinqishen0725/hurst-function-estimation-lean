import Hurst.SecondUnknownConditionalBias
import Hurst.SecondUnknownScaleTests

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem hurstHolder_q2_unknown_scale_expected_bias_of_scale_L1 (a b M u : ℝ) (r : ℕ) (hr : 1≤r)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hu : u<1) (hbu : b<u)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u)
    (σ : ℝ) (hσ : σ≠0)
    (hscale : Tendsto (fun n : ℕ => (∫ x,|q2LogScaleEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((∫ x,q2UnknownLocalEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x
      ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))-f t)/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop
      (𝓝 ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))) := by
  have hunit := hurstHolder_q2_unknown_bias_of_scale_L1 a b M u r hr ha hb hab hM hu hbu f hf hF hfc t ht htu hscale
  have hp2 : (2:ℝ)≤(r:ℝ)+1 := by exact_mod_cast (show 2≤r+1 by omega)
  have he := hurstHolder_q2_unknown_scale_test_eq ((r:ℝ)+1) a b M (a/2) u r hp2 ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
  apply hunit.congr'
  filter_upwards [he] with n hn
  have hh := hn σ hσ (fun z => z)
  rw [hh]

end Hurst
