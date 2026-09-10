import Hurst.OptimalBandwidth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem optimalLocalBandwidth_power_decomposition (p : ℝ) (k n : ℕ) (hn : 1<n) :
    (optimalLocalBandwidth p n)^k = (n:ℝ)^(-(k:ℝ)/(2*p+1)) *
      (Real.log n)^(-2*(k:ℝ)/(2*p+1)) := by
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hlog := Real.log_pos hnR
  unfold optimalLocalBandwidth
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity),Real.mul_rpow (by positivity) (sq_nonneg _),
    ← Real.rpow_natCast (Real.log (n:ℝ)) 2,← Real.rpow_mul hlog.le]
  congr 1 <;> congr 1 <;> push_cast <;> ring

theorem optimalLocalBandwidth_power_growth (p s : ℝ) (k : ℕ) (hs : (k:ℝ)/(2*p+1)<s) :
    Tendsto (fun n : ℕ => (n:ℝ)^s*(optimalLocalBandwidth p n)^k) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ => (Real.log n)^(2*(k:ℝ)/(2*p+1))/(n:ℝ)^(s-(k:ℝ)/(2*p+1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using! (isLittleO_log_rpow_rpow_atTop
      (2*(k:ℝ)/(2*p+1)) (by linarith : 0<s-(k:ℝ)/(2*p+1))).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)^s*(optimalLocalBandwidth p n)^k)⁻¹) atTop (𝓝 0) := by
    apply hbase.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hlog : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    rw [optimalLocalBandwidth_power_decomposition p k n (by omega),← mul_assoc,← Real.rpow_add hnR]
    rw [show s + -(k:ℝ)/(2*p+1)=s-(k:ℝ)/(2*p+1) by ring,
      show -2*(k:ℝ)/(2*p+1)=-(2*(k:ℝ)/(2*p+1)) by ring,Real.rpow_neg hlog.le]
    simp only [mul_inv_rev,inv_inv,div_eq_mul_inv]
  have hp : ∀ᶠ n : ℕ in atTop,((n:ℝ)^s*(optimalLocalBandwidth p n)^k)⁻¹∈Ioi (0:ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hd := optimalLocalBandwidth_pos p n (by omega)
    exact inv_pos.mpr (mul_pos (Real.rpow_pos_of_pos hnR _) (pow_pos hd _))
  have hi' : Tendsto (fun n : ℕ => ((n:ℝ)^s*(optimalLocalBandwidth p n)^k)⁻¹) atTop (𝓝[>] (0:ℝ)) :=
    by convert hi.inf (tendsto_principal.mpr hp) using 1 <;> first | rfl | (simp only [inf_idem])
  convert tendsto_inv_nhdsGT_zero.comp hi' using 1 <;> first | rfl | (funext n; simp only [Function.comp_apply,inv_inv])

theorem optimalLocalBandwidth_tendsto_zero (p : ℝ) (hp : 1≤p) :
    Tendsto (optimalLocalBandwidth p) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n:ℝ)^(-1/(2*p+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using! (tendsto_rpow_neg_atTop
      (by positivity : 0<1/(2*p+1))).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hpow
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact (optimalLocalBandwidth_pos p n (by omega)).le
  · filter_upwards [eventually_ge_atTop 1,(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with n hn hln
    exact optimalLocalBandwidth_upper p hp n (by omega) hln

end Hurst
