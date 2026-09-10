import Hurst.FirstScaleLongL1
import Hurst.GridErrorLimit

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

set_option maxHeartbeats 1200000

theorem mesh_log_power_rpow_tendsto (r : ℝ) (hr : r < 0) (k : ℕ) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) ^ k * (n : ℝ) ^ r)
      atTop (𝓝 0) := by
  let c : ℝ := 2 + Real.log 2
  have hc : 0 ≤ c := by
    dsimp [c]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have ht0 := (nat_log_power_div_rpow_tendsto (-r) (by linarith) k).const_mul (c ^ k)
  have ht : Tendsto (fun n : ℕ =>
      c ^ k * ((Real.log n) ^ k * (n : ℝ) ^ r)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht0.congr' (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [Real.rpow_neg hnR.le]
      field_simp)
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_nonneg (pow_nonneg (by
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      linarith) k) (Real.rpow_nonneg (by positivity) r)
  · have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop 1] with n hn hlog1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog2 : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
    have hbase : 1 + Real.log (2 * (n : ℝ)) ≤ c * Real.log n := by
      rw [hlog2]
      dsimp [c]
      have hlog2pos : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      nlinarith [mul_nonneg hlog2pos (sub_nonneg.mpr hlog1)]
    have hp := pow_le_pow_left₀ (by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        linarith)
      linarith) hbase k
    have hm := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hnR.le r)
    calc
      _ ≤ (c * Real.log n) ^ k * (n : ℝ) ^ r := hm
      _ = c ^ k * ((Real.log n) ^ k * (n : ℝ) ^ r) := by rw [mul_pow]; ring

theorem gridCovarianceError_mesh_log_sq_tendsto
    (b C : ℝ) (hb : b < 1) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) ^ 2 * gridCovarianceError b C n)
      atTop (𝓝 0) := by
  have h1 := mesh_log_power_rpow_tendsto (-1) (by norm_num) 3
  have h2 := mesh_log_power_rpow_tendsto (2 * b - 2) (by linarith) 3
  have h := (h1.add h2).const_mul C
  simp only [add_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [] with n
  unfold gridCovarianceError
  ring

theorem gridCovarianceError_sq_mesh_log_four_tendsto
    (b C : ℝ) (hb : b < 1) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) ^ 4 * (gridCovarianceError b C n) ^ 2)
      atTop (𝓝 0) := by
  have h := (gridCovarianceError_mesh_log_sq_tendsto b C hb).pow 2
  simpa only [zero_pow (by norm_num : 2 ≠ 0)] using h.congr' (by
    filter_upwards [] with n
    ring)

theorem ceil_sqrt_div_mesh_log_four_tendsto :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) ^ 4 *
        ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) : ℝ) / n))
      atTop (𝓝 0) := by
  have hhalf := mesh_log_power_rpow_tendsto (-1 / 2) (by norm_num) 4
  have hone := mesh_log_power_rpow_tendsto (-1) (by norm_num) 4
  have htop := hhalf.add hone
  simp only [add_zero] at htop
  apply squeeze_zero' _ _ htop
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_nonneg (pow_nonneg (by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      linarith) 4) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hnR.le (1 / 2 : ℝ))
    have hdiv : (Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) : ℝ) / n ≤
        (n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ) := by
      have hc : (Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) : ℝ) ≤
          (n : ℝ) ^ (1 / 2 : ℝ) + 1 := hceil.le
      apply (div_le_iff₀ hnR).mpr
      calc
        (Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) : ℝ) ≤
            (n : ℝ) ^ (1 / 2 : ℝ) + 1 := hc
        _ = ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)) * n := by
          have h1 : (n : ℝ) ^ (-1 / 2 : ℝ) * n = (n : ℝ) ^ (1 / 2 : ℝ) := by
            calc
              (n : ℝ) ^ (-1 / 2 : ℝ) * n =
                  (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = (n : ℝ) ^ ((-1 / 2 : ℝ) + 1) := by rw [Real.rpow_add hnR]
              _ = (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num
          have h2 : (n : ℝ) ^ (-1 : ℝ) * n = 1 := by
            rw [Real.rpow_neg_one, inv_mul_cancel₀ hnR.ne']
          rw [add_mul, h1, h2]
    have hL4 : 0 ≤ (1 + Real.log (2 * (n : ℝ))) ^ 4 := by positivity
    have hm := mul_le_mul_of_nonneg_left hdiv hL4
    calc
      _ ≤ (1 + Real.log (2 * (n : ℝ))) ^ 4 *
          ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)) := hm
      _ = _ := by ring

theorem stride_power_sq_mesh_log_four_tendsto
    (b : ℝ) (hb : b < 1) (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) ^ 4 *
        ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2)
      atTop (𝓝 0) := by
  have hbase := mesh_log_power_rpow_tendsto (2 * b - 2) (by linarith) 4
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := hbase.const_mul (((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.div_rpow (Real.rpow_nonneg hnR.le _) hdR.le]
  have hpow : (((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * b - 2)) ^ 2 =
      (n : ℝ) ^ (2 * b - 2) := by
    have hinner : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * b - 2) =
        (n : ℝ) ^ ((1 / 2 : ℝ) * (2 * b - 2)) :=
      (Real.rpow_mul hnR.le (1 / 2 : ℝ) (2 * b - 2)).symm
    calc
      (((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * b - 2)) ^ 2 =
          ((n : ℝ) ^ ((1 / 2 : ℝ) * (2 * b - 2))) ^ 2 :=
            congrArg (fun x : ℝ => x ^ 2) hinner
      _ = (n : ℝ) ^ (((1 / 2 : ℝ) * (2 * b - 2)) * 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
            norm_num only [Nat.cast_ofNat]
      _ = (n : ℝ) ^ (2 * b - 2) := by congr 1 <;> ring
  calc
    ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 *
        ((1 + Real.log (2 * (n : ℝ))) ^ 4 * (n : ℝ) ^ (2 * b - 2)) =
      (1 + Real.log (2 * (n : ℝ))) ^ 4 *
        (((n : ℝ) ^ (2 * b - 2)) /
          ((d : ℝ) ^ (2 * b - 2)) ^ 2) := by
            rw [inv_pow]
            field_simp
    _ = (1 + Real.log (2 * (n : ℝ))) ^ 4 *
        ((((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * b - 2) /
          (d : ℝ) ^ (2 * b - 2)) ^ 2) := by
            rw [div_pow]
            congr 2
            exact hpow.symm

theorem firstStrideLongRowBound_mesh_log_four_div_tendsto
    (b C A : ℝ) (d : ℕ) (hb : b < 1) (hd : 0 < d) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) ^ 4 *
        (firstStrideLongRowBound b C A d n / (n : ℝ)))
      atTop (𝓝 0) := by
  let L := fun n : ℕ => 1 + Real.log (2 * (n : ℝ))
  have hc := ceil_sqrt_div_mesh_log_four_tendsto
  have hi := mesh_log_power_rpow_tendsto (-1) (by norm_num) 4
  have hp := stride_power_sq_mesh_log_four_tendsto b hb d hd
  have he := gridCovarianceError_sq_mesh_log_four_tendsto b C hb
  have h := ((((hc.const_mul 2).add
    (hi.const_mul (4 * (d : ℝ) + 1))).add hp).const_mul
      (2 * (4 * A) ^ 2)).add (he.const_mul 32)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold firstStrideLongRowBound
  push_cast
  rw [Real.rpow_neg_one]
  field_simp
  ring

end Hurst
