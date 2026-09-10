from pathlib import Path
s='''import Hurst.ActualOptimalCLT
import Hurst.ActualUnknownConditionalLimits
import Hurst.FirstScaleNegligible

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst
'''
for q in [1,2]:
 extra='(u : ℝ) (hr : 1≤r) (hu : u<1) (hbu : b<u)' if q==2 else ''
 coeff='(gridStrideFirstCoefficients n 1)' if q==1 else '(gridSecondCoefficients n)'
 est=f'q{q}LocalEstimator '+('u ' if q==2 else '')
 unknown=f'q{q}UnknownLocalEstimator '+('(a/2) u ' if q==2 else '')
 htu='(htu : f t<u)' if q==2 else ''
 aclass='(by linarith [Nat.cast_nonneg (α := ℝ) r])' if q==1 else '(by exact_mod_cast (show 2≤r+1 by omega))'
 sig=f'''
theorem hurstHolder_q{q}_conditional_short_mainline (a b M : ℝ) (r : ℕ) {extra}
    (ha : 0<a) (hb : b<{'3/4' if q==1 else '1'}) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) {htu}
    (V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hpoly : ∀ k,TendstoInDistribution
      (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*gaussianLogTruncationStatistic
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (localPolynomialWeights r n {q} (optimalLocalBandwidth ((r:ℝ)+1) n) t) {coeff} k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1))'''
 if q==2:
  sig+='''
    (hscale : Tendsto (fun n : ℕ => (∫ x,|q2LogScaleEstimator (a/2) u r n
      (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x|
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop (𝓝 0))'''
 s+=sig+' :\n'
 for j in [0,1]:
  var=est+'r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x' if j==0 else unknown+'r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x'
  s+=f'''    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      ({var}-f t)) atTop
      (fun z : ℝ => -Real.sqrt V*z+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1)'''+(' ∧\n' if j==0 else ' := by\n')
 s+=f'''  obtain ⟨hδ,hδ0,hN,_,_⟩ := optimalLocalBandwidth_bias_conditions r {'b hb' if q==1 else '0 (by norm_num)'}
  have hlogCLT := hurstHolder_{'stride_first' if q==1 else 'grid_second'}_CLT_of_polynomial_limits
    ((r:ℝ)+1) a b M r {aclass} ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
    (optimalLocalBandwidth ((r:ℝ)+1)) hδ hδ0 hN V Vk hV hpoly
  have hknown := hurstHolder_q{q}_CLT_of_log_CLT a b M r {'u hr hu' if q==2 else ''} ha hb hab hM f hf hF hfc t ht {'htu' if q==2 else ''}
    (gaussianReal 0 1) (fun z : ℝ => Real.sqrt V*z) hlogCLT
'''
 if q==1:
  s+='''  have hscale := hurstHolder_q1_scale_L1_negligible a b M r ha hb hab hM f hf hF
'''
 scalefun=f'q{q}LogScaleEstimator '+('(a/2) u ' if q==2 else '')+'r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x'
 s+=f'''  have hs : Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (∫ x,|{scalefun}| ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0) := by
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
  exact hurstHolder_q{q}_unknown_distribution_of_inputs a b M {'u' if q==2 else ''} r {'hr' if q==2 else ''}
    ha hb hab hM {'hu hbu' if q==2 else ''} f hf hF t ht {'htu' if q==2 else ''}
    (gaussianReal 0 1) _ (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n))
    (Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)) hs hknown
'''
s+='\nend Hurst\n';Path('.scratch/ActualShortMainline.lean').write_text(s)
