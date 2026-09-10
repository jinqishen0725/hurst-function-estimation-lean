import Hurst.MeshPowerGeneral

noncomputable section
open Set
namespace Hurst

/-- Parameter movement of order one mesh step changes powers by a fixed factor. -/
theorem mesh_parameter_power_bound (n : ℕ) (hn : 0 < n) (d B : ℝ)
    (hB : 0 ≤ B) (hd : |d| ≤ B / n) : (n : ℝ) ^ d ≤ Real.exp B := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply rpow_le_exp_of_log_bound (n : ℝ) d B hn0
  rw [abs_of_nonneg (Real.log_nonneg hn1)]
  calc
    |d| * Real.log n ≤ (B / n) * Real.log n := mul_le_mul_of_nonneg_right hd (Real.log_nonneg hn1)
    _ ≤ (B / n) * n := mul_le_mul_of_nonneg_left (Real.log_le_self hn0.le) (div_nonneg hB hn0.le)
    _ = B := div_mul_cancel₀ B hn0.ne'

theorem normalized_mesh_envelope_bound (n : ℕ) (hn : 0 < n) (h k l b B : ℝ)
    (hh0 : 0 < h) (hk0 : 0 < k) (hl0 : 0 < l) (hhb : h ≤ b) (hkb : k ≤ b)
    (hB : 0 ≤ B) (hkl : |k - l| ≤ B / n) :
    (n : ℝ) ^ (h + k - 2) * meshPowerEnvelope n (h + min k l) ≤
      2 * Real.exp B * ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 0 < min k l := lt_min hk0 hl0
  have he2 : (2 : ℝ) ^ (1 - (h + min k l)) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := Real.rpow_one 2
  have hdiff : |k - min k l| ≤ B / n := by
    rcases le_total k l with he | he
    · rw [min_eq_left he, sub_self, abs_zero]
      positivity
    · rwa [min_eq_right he]
  have he := mesh_parameter_power_bound n hn (k - min k l) B hB hdiff
  have hid : (n : ℝ) ^ (h + k - 2) * (2 * (n : ℝ)) ^ (1 - (h + min k l)) =
      (2 : ℝ) ^ (1 - (h + min k l)) * (n : ℝ) ^ (k - min k l) * (n : ℝ) ^ (-1 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le]
    calc
      _ = (2 : ℝ) ^ (1 - (h + min k l)) * ((n : ℝ) ^ (h + k - 2) * (n : ℝ) ^ (1 - (h + min k l))) := by ring
      _ = (2 : ℝ) ^ (1 - (h + min k l)) * (n : ℝ) ^ (k - min k l + -1) := by
        rw [← Real.rpow_add hn0]
        congr 2
        ring
      _ = _ := by rw [Real.rpow_add hn0]; ring
  have hf := Real.rpow_le_rpow_of_exponent_le hn1 (show h + k - 2 ≤ 2 * b - 2 by linarith)
  have hprod := mul_le_mul he2 he (Real.rpow_nonneg hn0.le _) (by norm_num : (0 : ℝ) ≤ 2)
  have hlast := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hn0.le (-1))
  have hexp : 1 ≤ Real.exp B := Real.one_le_exp_iff.mpr hB
  unfold meshPowerEnvelope
  rw [mul_add, mul_one, hid]
  have hpow := Real.rpow_nonneg hn0.le (2 * b - 2)
  nlinarith [mul_nonneg (show 0 ≤ 2 * Real.exp B - 1 by linarith) hpow]

end Hurst
