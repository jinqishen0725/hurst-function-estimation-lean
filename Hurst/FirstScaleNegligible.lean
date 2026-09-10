import Hurst.ScaledMomentLimit
import Hurst.FirstScaleSharperRisk
import Hurst.OptimalMeanLeading

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_scale_L1_negligible (a b M : ℝ) (r : ℕ)
    (ha : 0<a) (hb : b<3/4) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b)) :
    Tendsto (fun n : ℕ => (∫ x,|q1LogScaleEstimator r n (scaleAverageResolution ((r:ℝ)+1) n)
      (optimalLocalBandwidth ((r:ℝ)+1) n) x|
      ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop (𝓝 0) := by
  let P := fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let S := fun n => q1LogScaleEstimator r n (scaleAverageResolution ((r:ℝ)+1) n) (optimalLocalBandwidth ((r:ℝ)+1) n)
  let ρ := fun n => (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)
  have hp : (1:ℝ)≤(r:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hceil : Nat.ceil ((r:ℝ)+1)-1=r := by
    rw [Nat.ceil_add_one (Nat.cast_nonneg r),Nat.ceil_natCast]
    omega
  obtain ⟨C,hC,N,hN,hR⟩ := hurstHolder_q1_scale_risk_log_squared_over_n ((r:ℝ)+1) a b M hp ha hb hab hM
  have hbound : ∀ᶠ n in atTop,MemLp (S n) 2 (P n) ∧
      (∫ x,(S n x)^2 ∂P n)/(Real.log n)^2≤C/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [hceil] using hR f hf hF n hn
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hρ : ∀ᶠ n in atTop,0<ρ n :=
    (optimalLocalBandwidth_bias_conditions r 0 (by norm_num)).1.mono (fun n hn => pow_pos hn _)
  have hD : ∀ᶠ n : ℕ in atTop,0<Real.log n*ρ n := by
    filter_upwards [hlog.eventually_gt_atTop 0,hρ] with n hn hr
    exact mul_pos hn hr
  apply scaled_L1_of_second_moment_tendsto P S (fun n => Real.log n*ρ n)
    (hbound.mono (fun n hn => hn.1)) hD
  have hg := optimalLocalBandwidth_power_growth ((r:ℝ)+1) 1 (2*(r+1)) (by
    apply (div_lt_iff₀ (by positivity : 0<2*((r:ℝ)+1)+1)).mpr
    push_cast
    linarith)
  have hng : Tendsto (fun n : ℕ => (n:ℝ)*(ρ n)^2) atTop atTop := by
    simpa only [Real.rpow_one,show 2*(r+1)=(r+1)*2 by omega,pow_mul] using hg
  have hz : Tendsto (fun n : ℕ => C/((n:ℝ)*(ρ n)^2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hng).const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (integral_nonneg (fun x => sq_nonneg _)) (sq_nonneg _))) ?_ hz
  filter_upwards [hbound] with n hn
  have he := div_le_div_of_nonneg_right hn.2 (sq_nonneg (ρ n))
  convert he using 1 <;> first | rfl | simp only [mul_pow,div_div]

end Hurst
