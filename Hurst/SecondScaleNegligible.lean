import Hurst.SecondScaleFineRates
import Hurst.ScaleBandwidth

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

set_option maxHeartbeats 1200000

/-- The actual q=2 log-scale estimator is negligible at the optimal local
bandwidth.  This is the scale input previously assumed by the conditional
unknown-scale mainline. -/
theorem hurstHolder_q2_scale_L1_negligible (a b M : ℝ) (r : ℕ) (u : ℝ)
    (hr : 1≤r) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (hu : u<1) (hbu : b<u) (f : ℝ → ℝ)
    (hf : f∈hurstHolderClass ((r:ℝ)+1) M)
    (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b)) :
    Tendsto (fun n : ℕ =>
      (∫ x,|q2LogScaleEstimator (a/2) u r n
          (scaleAverageResolution ((r:ℝ)+1) n)
          (optimalLocalBandwidth ((r:ℝ)+1) n) x|
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))/
      (Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))) atTop (𝓝 0) := by
  have hp : (2:ℝ)≤(r:ℝ)+1 := by exact_mod_cast (show 2≤r+1 by omega)
  obtain ⟨N₀,hN₀,C₁,hC₁,C₂,hC₂,C₃,hC₃,C₄,hC₄,C₅,hC₅,hfinite⟩ :=
    hurstHolder_q2_logScale_fine_L1 ((r:ℝ)+1) a b M u hp ha hb hab hM hu hbu
  have hupper := optimal_q2_fine_bound_scaled_tendsto r C₁ C₂ C₃ C₄ C₅ hC₁ hC₄
  have hp1 : (1:ℝ)≤(r:ℝ)+1 := by linarith
  have hscaled : Tendsto (fun n : ℕ =>
      Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*
        (∫ x,|q2LogScaleEstimator (a/2) u r n
            (scaleAverageResolution ((r:ℝ)+1) n)
            (optimalLocalBandwidth ((r:ℝ)+1) n) x|
          ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hupper
    · filter_upwards [] with n
      exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (fun _ => abs_nonneg _))
    · filter_upwards [hfinite,optimalLocalBandwidth_eventual_design ((r:ℝ)+1) N₀ hp1]
        with n hn hdesign
      let δ := optimalLocalBandwidth ((r:ℝ)+1) n
      let m := scaleAverageResolution ((r:ℝ)+1) n
      obtain ⟨hm,hmd⟩ := scaleAverageResolution_design ((r:ℝ)+1) n hdesign.2.1
      have hbound := hn f hf hF m hm δ hdesign.2.1 hdesign.2.2.1
        hdesign.2.2.2.1 hmd hdesign.2.2.2.2.2
      have hrceil : Nat.ceil ((r:ℝ)+1)-1=r := by
        rw [show (r:ℝ)+1=((r+1:ℕ):ℝ) by norm_num,Nat.ceil_natCast]
        omega
      rw [hrceil] at hbound
      exact mul_le_mul_of_nonneg_left hbound.2 (Real.sqrt_nonneg _)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hbal := optimalLocalBandwidth_fluctuation_balance r n hn
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hd := optimalLocalBandwidth_pos ((r:ℝ)+1) n hn
  have hc : Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)=
      1/(Real.log n*(optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)) := by
    apply (eq_div_iff (mul_pos hl (pow_pos hd _)).ne').mpr
    nlinarith [hbal]
  rw [hc]
  ring

end Hurst
