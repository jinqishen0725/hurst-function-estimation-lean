import Hurst.OptimalEstimatorDistribution
import Hurst.ActualConditionalCLT
import Hurst.FirstEstimatorLinearization
import Hurst.SecondEstimatorLinearization
import Hurst.OptimalNormalization

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem hurstHolder_q1_CLT_of_log_CLT (a b M : ℝ) (r : ℕ) 
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) 
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (hCLT : TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridDifferenceCoefficients n) x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridDifferenceCoefficients n) y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z => -Z z+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let G := fun n => gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridDifferenceCoefficients n)
  let T := fun n => q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hab' : (0:ℝ)≤1 := by norm_num
  obtain ⟨V,hV,hvar⟩ := hurstHolder_stride_first_optimal_log_variance a b M r 1 ha hb hab hM (by norm_num) f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hG : ∀ᶠ n in atTop,MemLp (G n) 2 (P n) := hvar.mono (fun _ hn => hn.1)
  have hT : ∀ᶠ n in atTop,MemLp (T n) 2 (P n) := by
    filter_upwards [hG,hlog.eventually_gt_atTop 0] with n hn hl
    exact boundedInverse_memLp_two (P n) (G n) hn (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1
      (2*Real.log n) (by positivity) hab' ((calibrationOne_continuous _ _).continuousOn) (calibrationOne_strongDecrease _ _ _ _)
  have hm (n : ℕ) : AEMeasurable (fun x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*(T n x-f t)) (P n) := by
    by_cases hn : 1<n
    · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n)
        (by positivity) hab' ((calibrationOne_continuous _ _).continuousOn) (calibrationOne_strongDecrease _ _ _ _)).continuous.measurable
      have hg : Measurable (G n) := by dsimp [G]; unfold gaussianLogStatistic; fun_prop
      exact (((hi.comp hg).sub measurable_const).const_mul _).aemeasurable
    · have hn' : n≤1 := by omega
      have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
      simp only [hl,mul_zero,zero_mul]
      exact aemeasurable_const
  have hmean : Tendsto (fun n => ((∫ x,G n x ∂P n)-calibrationOne (Real.log n) gaussianLogSquareMean (f t))/(Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
    have he := hurstHolder_stride_first_log_mean_leading_optimal a b M r 1 ha hb hab hM (by norm_num) f hf hF hfc t ht
    simp only [Nat.cast_one,Real.log_one,mul_zero,add_zero] at he
    have hid (n : ℕ) : gridStrideFirstCoefficients n 1=gridDifferenceCoefficients n := rfl
    simp_rw [strideFirstGridLogExpectation,hid] at he
    convert he using 1 <;> first | rfl | (funext n; dsimp [G,P,ρ,calibrationOne]; congr 1; ring)
  have hrem := hurstHolder_q1_L1_linearization a b M r ha hb hab hM f hf hF hfc t ht
  have hρ : ∀ᶠ n in atTop,0<ρ n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact pow_pos (optimalLocalBandwidth_pos ((r:ℝ)+1) n hn) _
  have he := estimator_distribution_of_balanced_linearization P P' G T (f t)
    (fun n => calibrationOne (Real.log n) gaussianLogSquareMean (f t)) (fun n => Real.log n) ρ
    (fun (n : ℕ) => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) Z (-2*R)
    hG hT hm (hlog.eventually_gt_atTop 0) hρ
    ((eventually_gt_atTop 1).mono (fun n hn => optimalLocalBandwidth_fluctuation_balance r n hn)) hCLT hmean hrem
  convert he using 1 <;> first | rfl | (funext z; dsimp [R]; ring)

theorem hurstHolder_q2_CLT_of_log_CLT (a b M : ℝ) (r : ℕ) (u : ℝ) (hr : 1≤r) (hu : u<1)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (hCLT : TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n) x-
        (∫ y,gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n) y
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun (n : ℕ) x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop
      (fun z => -Z z+2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let G := fun n => gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n)
  let T := fun n => q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hab' : (0:ℝ)≤u := by have := (hf.1 ht).1; linarith
  obtain ⟨V,hV,hvar⟩ := hurstHolder_second_optimal_log_variance a b M r hr ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hG : ∀ᶠ n in atTop,MemLp (G n) 2 (P n) := hvar.mono (fun _ hn => hn.1)
  have hT : ∀ᶠ n in atTop,MemLp (T n) 2 (P n) := by
    filter_upwards [hG,hlog.eventually_gt_atTop 0] with n hn hl
    exact boundedInverse_memLp_two (P n) (G n) hn (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u
      (2*Real.log n) (by positivity) hab' (calibrationTwo_continuousOn _ _ u hu) (calibrationTwo_strongDecrease _ _ u hu)
  have hm (n : ℕ) : AEMeasurable (fun x => 2*Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*(T n x-f t)) (P n) := by
    by_cases hn : 1<n
    · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hi := (boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (2*Real.log n)
        (by positivity) hab' (calibrationTwo_continuousOn _ _ u hu) (calibrationTwo_strongDecrease _ _ u hu)).continuous.measurable
      have hg : Measurable (G n) := by dsimp [G]; unfold gaussianLogStatistic; fun_prop
      exact (((hi.comp hg).sub measurable_const).const_mul _).aemeasurable
    · have hn' : n≤1 := by omega
      have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
      simp only [hl,mul_zero,zero_mul]
      exact aemeasurable_const
  have hmean : Tendsto (fun n => ((∫ x,G n x ∂P n)-calibrationTwo (Real.log n) gaussianLogSquareMean (f t))/(Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
    convert hurstHolder_second_log_mean_leading_optimal a b M r hr ha hb hab hM f hf hF hfc t ht using 1 <;> first
      | rfl
      | (funext n; dsimp [G,P,ρ,secondGridLogExpectation,calibrationTwo,q2LogCorrection]; congr 1; ring)
  have hrem := hurstHolder_q2_L1_linearization a b M u r hr ha hb hab hM hu f hf hF hfc t ht htu
  have hρ : ∀ᶠ n in atTop,0<ρ n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact pow_pos (optimalLocalBandwidth_pos ((r:ℝ)+1) n hn) _
  have he := estimator_distribution_of_balanced_linearization P P' G T (f t)
    (fun n => calibrationTwo (Real.log n) gaussianLogSquareMean (f t)) (fun n => Real.log n) ρ
    (fun (n : ℕ) => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) Z (-2*R)
    hG hT hm (hlog.eventually_gt_atTop 0) hρ
    ((eventually_gt_atTop 1).mono (fun n hn => optimalLocalBandwidth_fluctuation_balance r n hn)) hCLT hmean hrem
  convert he using 1 <;> first | rfl | (funext z; dsimp [R]; ring)

end Hurst
