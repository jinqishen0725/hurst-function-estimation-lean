import Hurst.InverseL1Limit
import Hurst.OptimalLogVariance
import Hurst.HolderGridMSE

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_L1_linearization (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (hfc : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n : ℕ => (∫ x,|q1LocalEstimator r n (optimalLocalBandwidth ((r:ℝ)+1) n) t x-f t+
      (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t)
        (gridDifferenceCoefficients n) x-
          (calibrationOne (Real.log n) gaussianLogSquareMean (f t)))/(2*Real.log n)|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/
        (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) atTop (𝓝 0) := by
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
  have hy := boundedInverse_L1_remainder_tendsto P X hX (fun _ => 0) 0 1 gaussianLogSquareMean (f t) d 0 A
    (fun n => Real.log n) ρ hd (by norm_num) hA hda hdb continuous_const.continuousOn
    (by intro z hz; simp) hG hlog hρpos hρzero hQ
  simp_rw [hid] at hy
  have hval (n : ℕ) : -(2*Real.log n)*f t+0+gaussianLogSquareMean=
      calibrationOne (Real.log n) gaussianLogSquareMean (f t) := congrFun (hid n) (f t)
  simp_rw [hval] at hy
  exact hy

end Hurst
