from pathlib import Path
src=Path('Hurst/ActualShortMainline.lean').read_text()
out='''import Hurst.ActualShortMainline
import Hurst.DistributionShift
import Hurst.KnownScaleDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst
'''
for q in [1,2]:
 start=src.index(f'theorem hurstHolder_q{q}_conditional_short_mainline');end=src.index(' := by',start)
 sig=src[start:end];cut=sig.rindex(' :\n');head=sig[:cut]
 if q==2:head=head[:head.index('    (hscale :')]
 head=head.replace(f'conditional_short_mainline',f'conditional_raw_optimal_CLT').replace('(V : ℝ)','(σ : ℝ) (hσ : σ≠0) (V : ℝ)')
 coeff='gridStrideFirstCoefficients n 1' if q==1 else 'gridSecondCoefficients n'
 cal='calibrationOne' if q==1 else 'calibrationTwo'
 out+='\n'+head+f''' :
    TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (gaussianLogStatistic (localPolynomialWeights r n {q} (optimalLocalBandwidth ((r:ℝ)+1) n) t) ({coeff}) (σ⁻¹ • x)-
        {cal} (Real.log n) gaussianLogSquareMean (f t))) atTop
      (fun z : ℝ => Real.sqrt V*z-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let G := fun n => gaussianLogStatistic (localPolynomialWeights r n {q} (optimalLocalBandwidth ((r:ℝ)+1) n) t) ({coeff})
  let A := fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  obtain ⟨hδ,hδ0,hN,_,_⟩ := optimalLocalBandwidth_bias_conditions r {'b hb' if q==1 else '0 (by norm_num)'}
  have hCLT := hurstHolder_{'stride_first' if q==1 else 'grid_second'}_CLT_of_polynomial_limits
    ((r:ℝ)+1) a b M r ({'by linarith [Nat.cast_nonneg (α:=ℝ) r]' if q==1 else 'by exact_mod_cast (show 2≤r+1 by omega)'}) ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
    (optimalLocalBandwidth ((r:ℝ)+1)) hδ hδ0 hN V Vk hV hpoly
  have hmean : Tendsto (fun n : ℕ => ((∫ x,G n x ∂P n)-{cal} (Real.log n) gaussianLogSquareMean (f t))/(Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
'''
 if q==1:
  out+='''    have he := hurstHolder_stride_first_log_mean_leading_optimal a b M r 1 ha hb hab hM (by norm_num) f hf hF hfc t ht
    simp only [Nat.cast_one,Real.log_one,mul_zero,add_zero] at he
    convert he using 1 <;> first | rfl | (funext n; dsimp [G,P,ρ,calibrationOne,strideFirstGridLogExpectation]; congr 1; ring)
'''
 else:
  out+='''    convert hurstHolder_second_log_mean_leading_optimal a b M r hr ha hb hab hM f hf hF hfc t ht using 1 <;> first | rfl
      | (funext n; dsimp [G,P,ρ,calibrationTwo,q2LogCorrection,secondGridLogExpectation]; congr 1; ring)
'''
 out+=f'''  have hb' : Tendsto (fun n : ℕ => A n*((∫ x,G n x ∂P n)-{cal} (Real.log n) gaussianLogSquareMean (f t))) atTop (𝓝 (-2*R)) := by
    apply hmean.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hb := optimalLocalBandwidth_fluctuation_balance r n hn
    have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hd := optimalLocalBandwidth_pos ((r:ℝ)+1) n hn
    have hc : A n=1/(Real.log n*ρ n) := by
      apply (eq_div_iff (mul_pos hl (pow_pos hd _)).ne').mpr
      dsimp [A,ρ]
      nlinarith [hb]
    rw [hc]
    ring
  have hshift := distribution_add_deterministic P (gaussianReal 0 1) _ _ _ (-2*R) hCLT hb'
  have hunit : TendstoInDistribution (fun (n : ℕ) x => A n*(G n x-{cal} (Real.log n) gaussianLogSquareMean (f t))) atTop
      (fun z : ℝ => Real.sqrt V*z-2*R) P (gaussianReal 0 1) := by
    convert hshift using 1 <;> first | rfl | (funext n x; dsimp [G,P,A]; ring) | (funext z; ring)
  exact featureGaussian_known_scale_distribution (gaussianReal 0 1)
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)) _
    (fun n => by dsimp [G,A]; unfold gaussianLogStatistic; fun_prop) _ σ hσ hunit
'''
out+='\nend Hurst\n';Path('.scratch/ActualRawOptimalCLT.lean').write_text(out)
