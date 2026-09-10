import Hurst.FirstUnknownFineBias
import Hurst.FirstUnknownScaleTests

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_unknown_scale_expected_bias_leading (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (σ : ℝ) (hσ : σ≠0) (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n : ℕ => ((∫ x,q1UnknownLocalEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x
      ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))-f t)/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop
      (𝓝 ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))) := by
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have he := hurstHolder_q1_unknown_scale_test_eq ((r:ℝ)+1) a b M r hp ha (by linarith) hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hu := hurstHolder_q1_unknown_expected_bias_leading a b M r ha hb hab hM f hf hF hfc t ht
  apply hu.congr'
  filter_upwards [he] with n hn
  exact congrArg (fun z : ℝ => (z-f t)/(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) (hn σ hσ (fun y => y)).symm

end Hurst
