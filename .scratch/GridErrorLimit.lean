import Hurst.GridCorrelationDecay
import Hurst.PackingAsymptotics

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem mesh_log_rpow_tendsto (r : ℝ) (hr : r < 0) :
    Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ r) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_neg] using! (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp tendsto_natCast_atTop_atTop
  have hl := nat_log_power_div_rpow_tendsto (-r) (neg_pos.mpr hr) 1
  have h := (hp.const_mul (1 + Real.log 2)).add hl
  simp only [pow_one, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne', Real.rpow_neg hn0.le]
  simp only [div_eq_mul_inv, inv_inv]
  ring

theorem gridCovarianceError_tendsto (b C : ℝ) (hb : b < 1) :
    Tendsto (gridCovarianceError b C) atTop (𝓝 0) := by
  have h := ((mesh_log_rpow_tendsto (-1) (by norm_num)).add
    (mesh_log_rpow_tendsto (2 * b - 2) (by linarith))).const_mul C
  simp only [add_zero, mul_zero] at h
  convert! h using 1
  funext n
  unfold gridCovarianceError
  ring

theorem gridCovarianceError_square_row_tendsto (b C : ℝ) (hb : b < 3 / 4) :
    Tendsto (fun n : ℕ => (n : ℝ) * (gridCovarianceError b C n) ^ 2) atTop (𝓝 0) := by
  have h := (((mesh_log_rpow_tendsto (-1 / 2) (by norm_num)).add
    (mesh_log_rpow_tendsto (2 * b - 3 / 2) (by linarith))).const_mul C).pow 2
  simp only [add_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : (n : ℝ) ^ (1 / 2 : ℝ) * gridCovarianceError b C n =
      C * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (-1 / 2 : ℝ) +
        (1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (2 * b - 3 / 2)) := by
    unfold gridCovarianceError
    have he1 : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-1 : ℝ) = (n : ℝ) ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add hn0]; norm_num
    have he2 : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (2 * b - 2) = (n : ℝ) ^ (2 * b - 3 / 2) := by rw [← Real.rpow_add hn0]; congr 1; ring
    calc
      _ = C * ((1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-1 : ℝ)) +
          (1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (2 * b - 2))) := by ring
      _ = _ := by rw [he1, he2]
  rw [← hs, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  norm_num

end Hurst
