from pathlib import Path
s='''import Hurst.OptimalEstimatorDistribution
import Hurst.ActualConditionalCLT
import Hurst.FirstEstimatorLinearization
import Hurst.SecondEstimatorLinearization
import Hurst.OptimalNormalization

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst
'''
for q in [1,2]:
 coeff='(gridDifferenceCoefficients n)' if q==1 else '(gridSecondCoefficients n)'
 est=f'q{q}LocalEstimator '+('u ' if q==2 else '')
 extra='(u : ℝ) (hr : 1≤r) (hu : u<1)' if q==2 else ''
 htu='(htu : f t<u)' if q==2 else ''
 cal='calibrationOne' if q==1 else 'calibrationTwo'
 top='1' if q==1 else 'u'
 hc='(calibrationOne_continuous _ _).continuousOn' if q==1 else 'calibrationTwo_continuousOn _ _ u hu'
 hdecr='calibrationOne_strongDecrease _ _ _ _' if q==1 else 'calibrationTwo_strongDecrease _ _ u hu'
 var='hurstHolder_stride_first_optimal_log_variance a b M r 1 ha hb hab hM (by norm_num) f hf hF t ⟨ht.1.le,ht.2.le⟩' if q==1 else 'hurstHolder_second_optimal_log_variance a b M r hr ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩'
 lin='hurstHolder_q1_L1_linearization a b M r ha hb hab hM f hf hF hfc t ht' if q==1 else 'hurstHolder_q2_L1_linearization a b M u r hr ha hb hab hM hu f hf hF hfc t ht htu'
 s+=f'''
theorem hurstHolder_q{q}_CLT_of_log_CLT (a b M : ℝ) (r : ℕ) {extra}
    (ha : 0<a) (hb : b<{'3/4' if q==1 else '1'}) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) {htu}
    {{Ω' : Type*}} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (hCLT : TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (gaussianLogStatistic (localPolynomialWeights r n {q} (optimalLocalBandwidth ((r:ℝ)+1) n) t) {coeff} x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n {q} (optimalLocalBandwidth ((r:ℝ)+1) n) t) {coeff} y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      ({est}r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z => -Z z+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let G := fun n => gaussianLogStatistic (localPolynomialWeights r n {q} (optimalLocalBandwidth ((r:ℝ)+1) n) t) {coeff}
  let T := fun n => {est}r n (optimalLocalBandwidth ((r:ℝ)+1) n) t
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hab' : (0:ℝ)≤{top} := by { 'norm_num' if q==1 else 'have := (hf.1 ht).1; linarith' }
  obtain ⟨V,hV,hvar⟩ := {var}
  have hG : ∀ᶠ n in atTop,MemLp (G n) 2 (P n) := hvar.mono (fun _ hn => hn.1)
  have hT : ∀ᶠ n in atTop,MemLp (T n) 2 (P n) := by
    filter_upwards [hG,hlog.eventually_gt_atTop 0] with n hn hl
    exact boundedInverse_memLp_two (P n) (G n) hn ({cal} (Real.log n) gaussianLogSquareMean) 0 {top}
      (2*Real.log n) (by positivity) hab' ({hc}) ({hdecr})
  have hm (n : ℕ) : AEMeasurable (fun x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*(T n x-f t)) (P n) := by
    by_cases hn : 1<n
    · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hi := (boundedInverse_lipschitz ({cal} (Real.log n) gaussianLogSquareMean) 0 {top} (2*Real.log n)
        (by positivity) hab' ({hc}) ({hdecr})).continuous.measurable
      have hg : Measurable (G n) := by dsimp [G]; unfold gaussianLogStatistic; fun_prop
      exact (((hi.comp hg).sub measurable_const).const_mul _).aemeasurable
    · have hn' : n≤1 := by omega
      have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
      simp only [hl,mul_zero,zero_mul]
      exact aemeasurable_const
  have hmean : Tendsto (fun n => ((∫ x,G n x ∂P n)-{cal} (Real.log n) gaussianLogSquareMean (f t))/(Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
'''
 if q==1:
  s+='''    have he := hurstHolder_stride_first_log_mean_leading_optimal a b M r 1 ha hb hab hM (by norm_num) f hf hF hfc t ht
    simp only [Nat.cast_one,Real.log_one,mul_zero,add_zero] at he
    convert he using 1 <;> first | rfl | (funext n; dsimp [G,P,ρ,strideFirstGridLogExpectation,calibrationOne]; congr 1; ring)
'''
 else:
  s+='''    convert hurstHolder_second_log_mean_leading_optimal a b M r hr ha hb hab hM f hf hF hfc t ht using 1 <;> first
      | rfl
      | (funext n; dsimp [G,P,ρ,secondGridLogExpectation,calibrationTwo,q2LogCorrection]; congr 1; ring)
'''
 s+=f'''  have hrem := {lin}
  have hρ : ∀ᶠ n in atTop,0<ρ n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact pow_pos (optimalLocalBandwidth_pos ((r:ℝ)+1) n hn) _
  have he := estimator_distribution_of_balanced_linearization P P' G T (f t)
    (fun n => {cal} (Real.log n) gaussianLogSquareMean (f t)) (fun n => Real.log n) ρ
    (fun (n : ℕ) => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) Z (-2*R)
    hG hT hm (hlog.eventually_gt_atTop 0) hρ
    ((eventually_gt_atTop 1).mono (fun n hn => optimalLocalBandwidth_fluctuation_balance r n hn)) hCLT hmean hrem
  convert he using 1 <;> first | rfl | (funext z; dsimp [R]; ring)
'''
s+='\nend Hurst\n'
Path('.scratch/ActualOptimalCLT.lean').write_text(s)
