import Hurst.ActualShortMainline
import Hurst.DistributionShift
import Hurst.KnownScaleDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem hurstHolder_q1_conditional_raw_optimal_CLT (a b M : ℝ) (r : ℕ) 
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
    TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridStrideFirstCoefficients n 1) (σ⁻¹ • x)-
        calibrationOne (Real.log n) gaussianLogSquareMean (f t))) atTop
      (fun z : ℝ => Real.sqrt V*z-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let G := fun n => gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridStrideFirstCoefficients n 1)
  let A := fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  obtain ⟨hδ,hδ0,hN,_,_⟩ := optimalLocalBandwidth_bias_conditions r b hb
  have hCLT := hurstHolder_stride_first_CLT_of_polynomial_limits
    ((r:ℝ)+1) a b M r (by linarith [Nat.cast_nonneg (α:=ℝ) r]) ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
    (optimalLocalBandwidth ((r:ℝ)+1)) hδ hδ0 hN V Vk hV hpoly
  have hmean : Tendsto (fun n : ℕ => ((∫ x,G n x ∂P n)-calibrationOne (Real.log n) gaussianLogSquareMean (f t))/(Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
    have he := hurstHolder_stride_first_log_mean_leading_optimal a b M r 1 ha hb hab hM (by norm_num) f hf hF hfc t ht
    simp only [Nat.cast_one,Real.log_one,mul_zero,add_zero] at he
    convert he using 1 <;> first | rfl | (funext n; dsimp [G,P,ρ,calibrationOne,strideFirstGridLogExpectation]; congr 1; ring)
  have hb' : Tendsto (fun n : ℕ => A n*((∫ x,G n x ∂P n)-calibrationOne (Real.log n) gaussianLogSquareMean (f t))) atTop (𝓝 (-2*R)) := by
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
  have hunit : TendstoInDistribution (fun (n : ℕ) x => A n*(G n x-calibrationOne (Real.log n) gaussianLogSquareMean (f t))) atTop
      (fun z : ℝ => Real.sqrt V*z-2*R) P (gaussianReal 0 1) := by
    convert hshift using 1 <;> first | rfl | (funext n x; dsimp [G,P,A]; ring) | (funext z; ring)
  exact featureGaussian_known_scale_distribution (gaussianReal 0 1)
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)) _
    (fun n => by dsimp [G,A]; unfold gaussianLogStatistic; fun_prop) _ σ hσ hunit

theorem hurstHolder_q2_conditional_raw_optimal_CLT (a b M : ℝ) (r : ℕ) (u : ℝ) (hr : 1≤r) (hu : u<1) (hbu : b<u)
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
 :
    TendstoInDistribution (fun (n : ℕ) x => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
      (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n) (σ⁻¹ • x)-
        calibrationTwo (Real.log n) gaussianLogSquareMean (f t))) atTop
      (fun z : ℝ => Real.sqrt V*z-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let G := fun n => gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth ((r:ℝ)+1) n) t) (gridSecondCoefficients n)
  let A := fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  let R := (iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)
  obtain ⟨hδ,hδ0,hN,_,_⟩ := optimalLocalBandwidth_bias_conditions r 0 (by norm_num)
  have hCLT := hurstHolder_grid_second_CLT_of_polynomial_limits
    ((r:ℝ)+1) a b M r (by exact_mod_cast (show 2≤r+1 by omega)) ha hb hab hM f hf hF t ⟨ht.1.le,ht.2.le⟩
    (optimalLocalBandwidth ((r:ℝ)+1)) hδ hδ0 hN V Vk hV hpoly
  have hmean : Tendsto (fun n : ℕ => ((∫ x,G n x ∂P n)-calibrationTwo (Real.log n) gaussianLogSquareMean (f t))/(Real.log n*ρ n)) atTop (𝓝 (-2*R)) := by
    convert hurstHolder_second_log_mean_leading_optimal a b M r hr ha hb hab hM f hf hF hfc t ht using 1 <;> first | rfl | (funext n; dsimp [G,P,ρ,calibrationTwo,q2LogCorrection,secondGridLogExpectation]; congr 1; ring)
  have hb' : Tendsto (fun n : ℕ => A n*((∫ x,G n x ∂P n)-calibrationTwo (Real.log n) gaussianLogSquareMean (f t))) atTop (𝓝 (-2*R)) := by
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
  have hunit : TendstoInDistribution (fun (n : ℕ) x => A n*(G n x-calibrationTwo (Real.log n) gaussianLogSquareMean (f t))) atTop
      (fun z : ℝ => Real.sqrt V*z-2*R) P (gaussianReal 0 1) := by
    convert hshift using 1 <;> first | rfl | (funext n x; dsimp [G,P,A]; ring) | (funext z; ring)
  exact featureGaussian_known_scale_distribution (gaussianReal 0 1)
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)) _
    (fun n => by dsimp [G,A]; unfold gaussianLogStatistic; fun_prop) _ σ hσ hunit

end Hurst
