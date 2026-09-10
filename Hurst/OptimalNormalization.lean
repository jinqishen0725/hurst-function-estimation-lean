import Hurst.BiasVarianceScale

noncomputable section
namespace Hurst

theorem optimalLocalBandwidth_fluctuation_balance (r n : ℕ) (hn : 1<n) :
    Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1)=1 := by
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hlog := Real.log_pos hnR
  have hδ := optimalLocalBandwidth_pos ((r:ℝ)+1) n hn
  have he := optimalLocalBandwidth_raw_variance_balance r n hn
  have hnd : (0:ℝ)<(n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n := by positivity
  have hs := Real.sq_sqrt hnd.le
  have hbal : (n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n*
      ((Real.log n)^2*((optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))^2)=1 := by
    rw [← he]
    field_simp
  have hsq : (Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1))^2=1 := by
    rw [mul_pow,mul_pow,hs]
    nlinarith [hbal]
  have hpos : 0≤Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)*Real.log n*
      (optimalLocalBandwidth ((r:ℝ)+1) n)^(r+1) := by positivity
  nlinarith

end Hurst
