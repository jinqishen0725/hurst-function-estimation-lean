import Hurst.ActualOptimalCLT
import Hurst.ActualUnknownConditionalLimits
import Hurst.FirstScaleNegligible

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem hurstHolder_q1_conditional_short_mainline (a b M : ℝ) (r : ℕ) 
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) 
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hpoly : ∀ k,TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridStrideFirstCoefficients n 1) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1)) :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q1UnknownLocalEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) := by
  obtain ⟨hδ,hδ0,hN,_,_⟩ := optimalLocalBandwidth_bias_conditions r b hb
  have hlogCLT := hurstHolder_stride_first_CLT_of_polynomial_limits
    ((r:ℝ)+1) a b M r (by linarith [Nat.cast_nonneg (α := ℝ) r]) ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
    (optimalLocalBandwidth ((r:ℝ)+1)) hδ hδ0 hN V Vk hV hpoly
  have hknown := hurstHolder_q1_CLT_of_log_CLT a b M r  ha hb hab hM f hf hF hfc t ht 
    (gaussianReal 0 1) (fun z : ℝ => Real.sqrt V*z) hlogCLT
  have hscale := hurstHolder_q1_scale_L1_negligible a b M r ha hb hab hM f hf hF
  have hs : Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (∫ x,|q1LogScaleEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x| ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0) := by
    apply hscale.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hb := optimalLocalBandwidth_fluctuation_balance r n hn
    have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hd := optimalLocalBandwidth_pos ((r:ℝ)+1) n hn
    have hc : Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)=
        1/(Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) := by
      apply (eq_div_iff (mul_pos hl (pow_pos hd _)).ne').mpr
      nlinarith [hb]
    rw [hc]
    ring
  refine ⟨hknown,?_⟩
  exact hurstHolder_q1_unknown_distribution_of_inputs a b M  r 
    ha hb hab hM  f hf hF t ht 
    (gaussianReal 0 1) _ (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n))
    (Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)) hs hknown

theorem hurstHolder_q2_conditional_short_mainline (a b M : ℝ) (r : ℕ) (u : ℝ) (hr : 1≤r) (hu : u<1) (hbu : b<u)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u)
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
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
      (q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) ∧
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q2UnknownLocalEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z : ℝ => -(Real.sqrt V*z)+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) := by
  obtain ⟨hδ,hδ0,hN,_,_⟩ := optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  have hlogCLT := hurstHolder_grid_second_CLT_of_polynomial_limits
    ((r:ℝ)+1) a b M r (by exact_mod_cast (show 2≤r+1 by omega)) ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
    (optimalLocalBandwidth ((r:ℝ)+1)) hδ hδ0 hN V Vk hV hpoly
  have hknown := hurstHolder_q2_CLT_of_log_CLT a b M r u hr hu ha hb hab hM f hf hF hfc t ht htu
    (gaussianReal 0 1) (fun z : ℝ => Real.sqrt V*z) hlogCLT
  have hs : Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (∫ x,|q2LogScaleEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x| ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0) := by
    apply hscale.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hb := optimalLocalBandwidth_fluctuation_balance r n hn
    have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hd := optimalLocalBandwidth_pos ((r:ℝ)+1) n hn
    have hc : Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)=
        1/(Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) := by
      apply (eq_div_iff (mul_pos hl (pow_pos hd _)).ne').mpr
      nlinarith [hb]
    rw [hc]
    ring
  refine ⟨hknown,?_⟩
  exact hurstHolder_q2_unknown_distribution_of_inputs a b M u r hr
    ha hb hab hM hu hbu f hf hF t ht htu
    (gaussianReal 0 1) _ (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n))
    (Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)) hs hknown

end Hurst
