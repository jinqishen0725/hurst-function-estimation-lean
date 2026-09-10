import Hurst.GridErrorLimit

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem mesh_log_ratio_tendsto :
    Tendsto (fun n : ℕ => (1+Real.log (2*(n:ℝ)))/Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlog
  have hh := (tendsto_const_nhds (x := (1:ℝ))).add (hi.const_mul (1+Real.log 2))
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1,hlog.eventually_gt_atTop 0] with n hn hln
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hnR.ne']
  field_simp
  <;> ring

theorem gridCovarianceError_scaled_tendsto (b C : ℝ) (k : ℕ) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hN₁ : Tendsto (fun n : ℕ => (n:ℝ)*(δ n)^k) atTop atTop)
    (hN₂ : Tendsto (fun n : ℕ => (n:ℝ)^(2-2*b)*(δ n)^k) atTop atTop) :
    Tendsto (fun n : ℕ => gridCovarianceError b C n/(Real.log n*(δ n)^k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n:ℝ)*(δ n)^k)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN₁
  have h2 : Tendsto (fun n : ℕ => ((n:ℝ)^(2-2*b)*(δ n)^k)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN₂
  have hh := (mesh_log_ratio_tendsto.mul (h1.add h2)).const_mul C
  simp only [add_zero,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1,hδpos] with n hn hδn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp : (n:ℝ)^(2*b-2)=((n:ℝ)^(2-2*b))⁻¹ := by
    rw [show 2*b-2=-(2-2*b) by ring,Real.rpow_neg hnR.le]
  simp only [gridCovarianceError,hp,Real.rpow_neg_one,mul_inv_rev,div_eq_mul_inv]
  ring

end Hurst
