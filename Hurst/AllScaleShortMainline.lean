import Hurst.ActualShortMainline
import Hurst.AllScaleDistributionTransfer
import Hurst.KnownScaleDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem hurstHolder_q1_conditional_all_scale_short_mainline (a b M : ℝ) (r : ℕ) 
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) 
    (σ : ℝ) (hσ : σ≠0) (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hpoly : ∀ k,TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridStrideFirstCoefficients n 1) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t (σ⁻¹ • x)-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q1UnknownLocalEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  have hh := hurstHolder_q1_conditional_short_mainline a b M r  ha hb hab hM f hf hF hfc t ht  V Vk hV hpoly 
  refine ⟨?_,?_⟩
  · apply featureGaussian_known_scale_distribution (gaussianReal 0 1)
      (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)) _ _ _ σ hσ hh.1
    intro n
    exact normalized_q1_inverse_measurable n 
      (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridDifferenceCoefficients n))
      (by unfold gaussianLogStatistic; fun_prop) _ (f t)
  · exact hurstHolder_q1_unknown_scale_distribution_transfer ((r:ℝ)+1) a b M r 
      (by linarith [Nat.cast_nonneg (α:=ℝ) r]) ha (by linarith) hab hM
      f hf hF t ⟨ht.1.le,ht.2.le⟩
      (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) σ hσ (gaussianReal 0 1) _ hh.2

theorem hurstHolder_q2_conditional_all_scale_short_mainline (a b M : ℝ) (r : ℕ) (u : ℝ) (hr : 1≤r) (hu : u<1) (hbu : b<u)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u)
    (σ : ℝ) (hσ : σ≠0) (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hpoly : ∀ k,TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1))
    (hscale : Tendsto (fun n : ℕ => (∫ x,|q2LogScaleEstimator (a/2) u r n
      (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x|
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t (σ⁻¹ • x)-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q2UnknownLocalEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  have hh := hurstHolder_q2_conditional_short_mainline a b M r u hr hu hbu ha hb hab hM f hf hF hfc t ht htu V Vk hV hpoly hscale
  have hu0 : 0≤u := by linarith
  refine ⟨?_,?_⟩
  · apply featureGaussian_known_scale_distribution (gaussianReal 0 1)
      (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)) _ _ _ σ hσ hh.1
    intro n
    exact normalized_q2_inverse_measurable n u hu0 hu
      (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n))
      (by unfold gaussianLogStatistic; fun_prop) _ (f t)
  · exact hurstHolder_q2_unknown_scale_distribution_transfer ((r:ℝ)+1) a b M r (a/2) u hu0 hu
      (by exact_mod_cast (show 2≤r+1 by omega)) ha (hb) hab hM
      f hf hF t ⟨ht.1.le,ht.2.le⟩
      (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) σ hσ (gaussianReal 0 1) _ hh.2

/-- The q=2 all-scale short-memory theorem after discharging scale smallness
from the actual observation model. -/
theorem hurstHolder_q2_all_scale_short_mainline
    (a b M : ℝ) (r : ℕ) (u : ℝ) (hr : 1 ≤ r) (hu : u < 1) (hbu : b < u)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass ((r : ℝ) + 1) M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r + 1) f (Ioo (0 : ℝ) 1))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (htu : f t < u)
    (σ : ℝ) (hσ : σ ≠ 0)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hpoly : ∀ k, TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        gaussianLogTruncationStatistic
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r : ℝ) + 1) n) t)
          (gridSecondCoefficients n) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k) * z)
      (fun n => featureGaussian
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
      (gaussianReal 0 1)) :
    TendstoInDistribution
      (fun (n : ℕ) x => 2 * Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        Real.log n * (q2LocalEstimator u r n
          (optimalLocalBandwidth ((r : ℝ) + 1) n) t (σ⁻¹ • x) - f t)) atTop
      (fun z : ℝ => -(Real.sqrt V * z) +
        2 * ((iteratedDeriv (r + 1) f t / ((r + 1).factorial : ℝ)) *
          equivalentKernelMoment r (r + 1)))
      (fun n => featureGaussian
        (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))
      (gaussianReal 0 1) ∧
    TendstoInDistribution
      (fun (n : ℕ) x => 2 * Real.sqrt ((n : ℝ) * optimalLocalBandwidth ((r : ℝ) + 1) n) *
        Real.log n * (q2UnknownLocalEstimator (a / 2) u r n
          (scaleAverageResolution ((r : ℝ) + 1) n)
          (optimalLocalBandwidth ((r : ℝ) + 1) n) t x - f t)) atTop
      (fun z : ℝ => -(Real.sqrt V * z) +
        2 * ((iteratedDeriv (r + 1) f t / ((r + 1).factorial : ℝ)) *
          equivalentKernelMoment r (r + 1)))
      (fun n => featureGaussian
        (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))
      (gaussianReal 0 1) :=
  hurstHolder_q2_conditional_all_scale_short_mainline a b M r u hr hu hbu
    ha hb hab hM f hf hF hfc t ht htu σ hσ V Vk hV hpoly
    (hurstHolder_q2_scale_L1_negligible a b M r u hr ha hb hab hM hu hbu f hf hF)

end Hurst
