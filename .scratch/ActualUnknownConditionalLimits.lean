import Hurst.OracleScaleDistribution
import Hurst.FirstUnknownConditionalBias
import Hurst.SecondUnknownConditionalBias

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_unknown_distribution_of_inputs (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : Ω' → ℝ) (A : ℕ → ℝ) (hA : ∀ᶠ n in atTop,0≤A n)
    (hscale : Tendsto (fun n : ℕ => A n*(∫ x,|q1LogScaleEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0))
    (hknown : TendstoInDistribution (fun n x => 2*A n*Real.log n*(q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun n x => 2*A n*Real.log n*(q1UnknownLocalEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨V,hV,hvar⟩ := hurstHolder_stride_first_optimal_log_variance a b M r 1 ha hb hab hM (by norm_num) f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hS := hurstHolder_q1_scale_memLp_eventually ((r:ℝ)+1) a b M hp ha (by linarith) hab hM f hf hF r
    (scaleAverageResolution ((r:ℝ)+1)) (optimalLocalBandwidth ((r:ℝ)+1))
  let X := fun n => gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridDifferenceCoefficients n)
  let S := fun n => q1LogScaleEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n)
  have hmeas (n : ℕ) : AEMeasurable (fun x => 2*A n*Real.log n*(boundedInverse (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (X n x-S n x)-f t)) (P n) := by
    by_cases hn : 1<n
    · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n)
        (by positivity) (by norm_num)
        ((calibrationOne_continuous _ _).continuousOn)
        (calibrationOne_strongDecrease _ _ _ _)).continuous.measurable
      have hx : Measurable (X n) := by dsimp [X]; unfold gaussianLogStatistic; fun_prop
      have hs : Measurable (S n) := q1LogScaleEstimator_measurable _ _ _ _
      exact (((hi.comp (hx.sub hs)).sub measurable_const).const_mul _).aemeasurable
    · have hn' : n≤1 := by omega
      have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
      simp only [hl,mul_zero,zero_mul]
      exact aemeasurable_const
  have he := boundedInverse_scale_distribution_transfer P P' Z X S
    (fun n => calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 0
    (fun n => Real.log n) A (fun _ => f t) (hvar.mono (fun n hn => hn.1)) hS
    (hlog.eventually_gt_atTop 0) hA (by norm_num)
    (fun n => (calibrationOne_continuous _ _).continuousOn)
    (fun n => calibrationOne_strongDecrease _ _ _ _)
    hmeas (by simpa only [sub_zero] using hscale)
    (by simp only [sub_zero]; convert hknown using 1 <;> rfl)
  exact he

theorem hurstHolder_q2_unknown_distribution_of_inputs (a b M u : ℝ) (r : ℕ) (hr : 1≤r)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hu : u<1) (hbu : b<u)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : Ω' → ℝ) (A : ℕ → ℝ) (hA : ∀ᶠ n in atTop,0≤A n)
    (hscale : Tendsto (fun n : ℕ => A n*(∫ x,|q2LogScaleEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))) atTop (𝓝 0))
    (hknown : TendstoInDistribution (fun n x => 2*A n*Real.log n*(q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun n x => 2*A n*Real.log n*(q2UnknownLocalEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t)) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp2 : (2:ℝ)≤(r:ℝ)+1 := by exact_mod_cast (show 2≤r+1 by omega)
  obtain ⟨V,hV,hvar⟩ := hurstHolder_second_optimal_log_variance a b M r hr ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hS := hurstHolder_q2_scale_memLp_eventually ((r:ℝ)+1) a b M (a/2) u hp2 ha hb hab hM
    (by linarith) hu (by linarith) f hf hF r
    (scaleAverageResolution ((r:ℝ)+1)) (optimalLocalBandwidth ((r:ℝ)+1))
  let X := fun n => gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n)
  let S := fun n => q2LogScaleEstimator (a/2) u r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n)
  have hmeas (n : ℕ) : AEMeasurable (fun x => 2*A n*Real.log n*(boundedInverse (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (X n x-S n x)-f t)) (P n) := by
    by_cases hn : 1<n
    · have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
      have hi := (boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (2*Real.log n)
        (by positivity) (by linarith)
        (calibrationTwo_continuousOn _ _ u hu)
        (calibrationTwo_strongDecrease _ _ u hu)).continuous.measurable
      have hx : Measurable (X n) := by dsimp [X]; unfold gaussianLogStatistic; fun_prop
      have hs : Measurable (S n) := q2LogScaleEstimator_measurable _ _ _ _ _ _
      exact (((hi.comp (hx.sub hs)).sub measurable_const).const_mul _).aemeasurable
    · have hn' : n≤1 := by omega
      have hl : Real.log (n:ℝ)=0 := by interval_cases n <;> norm_num
      simp only [hl,mul_zero,zero_mul]
      exact aemeasurable_const
  have he := boundedInverse_scale_distribution_transfer P P' Z X S
    (fun n => calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u 0
    (fun n => Real.log n) A (fun _ => f t) (hvar.mono (fun n hn => hn.1)) hS
    (hlog.eventually_gt_atTop 0) hA (by linarith)
    (fun n => calibrationTwo_continuousOn _ _ u hu)
    (fun n => calibrationTwo_strongDecrease _ _ u hu)
    hmeas (by simpa only [sub_zero] using hscale)
    (by simp only [sub_zero]; convert hknown using 1 <;> rfl)
  exact he

end Hurst
