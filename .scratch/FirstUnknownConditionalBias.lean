import Hurst.OracleScaleBias
import Hurst.FirstEstimatorBias
import Hurst.ActualScaleIntegrability
import Hurst.FirstUnknownEstimator
import Hurst.ScaleBandwidth

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_unknown_bias_of_scale_L1 (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hscale : Tendsto (fun n : ℕ => (∫ x,|q1LogScaleEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((∫ x,q1UnknownLocalEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))-f t)/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop
      (𝓝 ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))) := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hρpos : ∀ᶠ n in atTop,0<ρ n :=
    (optimalLocalBandwidth_bias_conditions r 0 (by norm_num)).1.mono (fun n hn => pow_pos hn _)
  obtain ⟨V,hV,hvar⟩ := hurstHolder_stride_first_optimal_log_variance a b M r 1 ha hb hab hM (by norm_num) f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hS := hurstHolder_q1_scale_memLp_eventually ((r:ℝ)+1) a b M hp ha (by linarith) hab hM f hf hF r
    (scaleAverageResolution ((r:ℝ)+1)) (optimalLocalBandwidth ((r:ℝ)+1))
  have hknown := hurstHolder_q1_expected_bias_leading a b M r ha hb hab hM f hf hF hfc t ht
  have he := boundedInverse_scale_bias_transfer P
    (fun n => gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridDifferenceCoefficients n))
    (fun n => q1LogScaleEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n))
    (fun n => calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 0 (f t)
    ((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1))
    (fun n => Real.log n) ρ (hvar.mono (fun n hn => hn.1)) hS (hlog.eventually_gt_atTop 0) hρpos
    (by norm_num) (fun n => (calibrationOne_continuous _ _).continuousOn)
    (fun n => calibrationOne_strongDecrease _ _ _ _) (by simpa only [sub_zero] using hscale)
    (by simp only [sub_zero]; convert hknown using 1 <;> rfl)
  exact he

end Hurst
