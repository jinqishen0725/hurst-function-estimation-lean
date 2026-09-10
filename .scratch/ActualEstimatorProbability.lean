import Hurst.InverseProbabilityLimit
import Hurst.SecondEstimatorBias
import Hurst.FirstEstimatorBias

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q2_linearization_in_probability (a b M u : ℝ) (r : ℕ) (hr : 1≤r)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hu : u<1)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (htu : f t<u) (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n : ℕ => (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))).real
      {x | ε≤|q2LocalEstimator u r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t+
      (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridSecondCoefficients n) x-
          (calibrationTwo (Real.log n) gaussianLogSquareMean (f t)))/(2*Real.log n)|/(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)}) atTop (𝓝 0) := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let X := fun n => gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
    (gridSecondCoefficients n)
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨hδpos,hδzero,hN,hNk,hN₂⟩ := optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  have hρpos : ∀ᶠ n in atTop,0<ρ n := hδpos.mono (fun n hn => pow_pos hn _)
  have hρzero : Tendsto ρ atTop (𝓝 0) := by simpa only [zero_pow (by omega : r+1≠0)] using hδzero.pow (r+1)
  have hmean : Tendsto (fun n => ((∫ ω,X n ω ∂P n)-(-(2*Real.log n)*f t+q2LogCorrection (f t)+gaussianLogSquareMean))/
      (Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
    convert hurstHolder_second_log_mean_leading_optimal a b M r hr ha hb hab hM f hf hF hfc t ht using 1 <;> first
      | rfl
      | (funext n; dsimp only [P,X,ρ,secondGridLogExpectation]; congr 1; ring)
  obtain ⟨V,hV,hvar⟩ := hurstHolder_second_optimal_log_variance a b M r hr ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n) := hvar.mono (fun n hn => hn.1)
  have hpos : ∀ᶠ n : ℕ in atTop,0<Real.log n*ρ n := by
    filter_upwards [hlog.eventually_gt_atTop 0,hρpos] with n hn hrn
    exact mul_pos hn hrn
  obtain ⟨A,hA,hQ⟩ := mse_scale_bound_of_mean_variance P X hX
    (fun n => -(2*Real.log n)*f t+q2LogCorrection (f t)+gaussianLogSquareMean)
    (fun n => Real.log n) ρ (-2*R) V hV hpos hmean (hvar.mono (fun n hn => hn.2))
  obtain ⟨K,hK,hLip⟩ := q2LogCorrection_lipschitz_closed u hu
  have hH0 : 0<f t := (hf.1 ht).1
  let d := min (f t) (u-f t)/2
  have hd : 0<d := by dsimp [d]; positivity
  have hda : (0:ℝ)+d≤f t := by have := min_le_left (f t) (u-f t); dsimp [d]; linarith
  have hdb : f t+d≤u := by have := min_le_right (f t) (u-f t); dsimp [d]; linarith
  have hc : ContinuousOn q2LogCorrection (Icc (0:ℝ) u) := by
    convert calibrationTwo_continuousOn 0 0 u hu using 1 <;> first | rfl | (funext z; unfold calibrationTwo q2LogCorrection; ring)
  have hid (n : ℕ) : (fun z => -(2*Real.log n)*z+q2LogCorrection z+gaussianLogSquareMean)=
      calibrationTwo (Real.log n) gaussianLogSquareMean := by funext z; unfold calibrationTwo q2LogCorrection; ring
  have hG (n : ℕ) : StrongDecrease (fun z => -(2*Real.log n)*z+q2LogCorrection z+gaussianLogSquareMean) 0 u (2*Real.log n) := by
    rw [hid]
    exact calibrationTwo_strongDecrease _ _ u hu
  have hy := boundedInverse_linearization_in_probability P X hX q2LogCorrection 0 u gaussianLogSquareMean (f t) d K A
    (fun n => Real.log n) ρ hd hK hA hda hdb hc (fun z hz => hLip z hz (f t) ⟨hH0.le,htu.le⟩)
    hG hlog hρpos hρzero hQ ε hε
  simp_rw [hid] at hy
  have hval (n : ℕ) : -(2*Real.log n)*f t+q2LogCorrection (f t)+gaussianLogSquareMean=
      calibrationTwo (Real.log n) gaussianLogSquareMean (f t) := congrFun (hid n) (f t)
  simp_rw [hval] at hy
  exact hy


theorem hurstHolder_q1_linearization_in_probability (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n : ℕ => (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))).real
      {x | ε≤|q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t+
      (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridDifferenceCoefficients n) x-
          (calibrationOne (Real.log n) gaussianLogSquareMean (f t)))/(2*Real.log n)|/(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)}) atTop (𝓝 0) := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let X := fun n => gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
    (gridStrideFirstCoefficients n 1)
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨hδpos,hδzero,hN,hNk,hN₂⟩ := optimalLocalBandwidth_bias_conditions r b hb
  have hρpos : ∀ᶠ n in atTop,0<ρ n := hδpos.mono (fun n hn => pow_pos hn _)
  have hρzero : Tendsto ρ atTop (𝓝 0) := by simpa only [zero_pow (by omega : r+1≠0)] using hδzero.pow (r+1)
  have hmean : Tendsto (fun n => ((∫ ω,X n ω ∂P n)-(-(2*Real.log n)*f t+0+gaussianLogSquareMean))/
      (Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
    have he := hurstHolder_stride_first_log_mean_leading_optimal a b M r 1 ha hb hab hM (by norm_num) f hf hF hfc t ht
    simp only [Nat.cast_one,Real.log_one,mul_zero,add_zero] at he
    convert he using 1 <;> first | rfl | (funext n; dsimp only [P,X,ρ,strideFirstGridLogExpectation]; congr 1; ring)
  obtain ⟨V,hV,hvar⟩ := hurstHolder_stride_first_optimal_log_variance a b M r 1 ha hb hab hM (by norm_num) f hf hF t ⟨ht.1.le,ht.2.le⟩
  have hX : ∀ᶠ n in atTop,MemLp (X n) 2 (P n) := hvar.mono (fun n hn => hn.1)
  have hpos : ∀ᶠ n : ℕ in atTop,0<Real.log n*ρ n := by
    filter_upwards [hlog.eventually_gt_atTop 0,hρpos] with n hn hrn
    exact mul_pos hn hrn
  obtain ⟨A,hA,hQ⟩ := mse_scale_bound_of_mean_variance P X hX
    (fun n => -(2*Real.log n)*f t+0+gaussianLogSquareMean)
    (fun n => Real.log n) ρ (-2*R) V hV hpos hmean (hvar.mono (fun n hn => hn.2))
  have hH0 : 0<f t := (hf.1 ht).1
  have hH1 : f t<1 := (hf.1 ht).2
  let d := min (f t) (1-f t)/2
  have hd : 0<d := by dsimp [d]; positivity
  have hda : (0:ℝ)+d≤f t := by have := min_le_left (f t) (1-f t); dsimp [d]; linarith
  have hdb : f t+d≤1 := by have := min_le_right (f t) (1-f t); dsimp [d]; linarith
  have hid (n : ℕ) : (fun z => -(2*Real.log n)*z+0+gaussianLogSquareMean)=
      calibrationOne (Real.log n) gaussianLogSquareMean := by funext z; unfold calibrationOne; ring
  have hG (n : ℕ) : StrongDecrease (fun z => -(2*Real.log n)*z+0+gaussianLogSquareMean) 0 1 (2*Real.log n) := by
    rw [hid]
    exact calibrationOne_strongDecrease _ _ _ _
  have hy := boundedInverse_linearization_in_probability P X hX (fun _ => 0) 0 1 gaussianLogSquareMean (f t) d 0 A
    (fun n => Real.log n) ρ hd (by norm_num) hA hda hdb continuous_const.continuousOn
    (by intro z hz; simp) hG hlog hρpos hρzero hQ ε hε
  simp_rw [hid] at hy
  have hval (n : ℕ) : -(2*Real.log n)*f t+0+gaussianLogSquareMean=
      calibrationOne (Real.log n) gaussianLogSquareMean (f t) := congrFun (hid n) (f t)
  simp_rw [hval] at hy
  exact hy


end Hurst
