import Hurst.HurstPacking
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

def packingResolution (p : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (1 / (2 * p + 1)))

def lowerBoundRate (p : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (-p / (2 * p + 1))

theorem nat_log_power_div_rpow_tendsto (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ k / (n : ℝ) ^ r) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast, Function.comp_apply] using! h.comp tendsto_natCast_atTop_atTop

theorem packingResolution_bounds (p : ℝ) (hp : 1 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < packingResolution p n ∧
      (n : ℝ) ^ (1 / (2 * p + 1)) ≤ (packingResolution p n : ℝ) ∧
      (packingResolution p n : ℝ) ≤ 2 * (((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (1 / (2 * p + 1))) ∧
      (n : ℝ) * Real.log (2 * (n : ℝ)) ^ 2 * (packingResolution p n : ℝ) ^ (-2 * p - 1) ≤ 4 ∧
      (2 : ℝ) ^ (-p) * lowerBoundRate p n ≤ (packingResolution p n : ℝ) ^ (-p) := by
  have hden : 0 < 2 * p + 1 := by linarith
  have hα : 0 < 1 / (2 * p + 1) := by positivity
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlog, eventually_ge_atTop 2] with n hL hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by positivity
  have hx : 0 < (n : ℝ) * Real.log (n : ℝ) ^ 2 := by positivity
  have hx1 : 1 ≤ (n : ℝ) * Real.log (n : ℝ) ^ 2 := by nlinarith
  have hb : 1 ≤ ((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (1 / (2 * p + 1)) :=
    Real.one_le_rpow hx1 hα.le
  have hmlo := Nat.le_ceil (((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (1 / (2 * p + 1)))
  have hmhi := Nat.ceil_lt_add_one (Real.rpow_nonneg hx.le (1 / (2 * p + 1)))
  have hmone : (1 : ℝ) ≤ packingResolution p n := hb.trans hmlo
  have hm : 0 < packingResolution p n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hmone)
  have hmR : (0 : ℝ) < packingResolution p n := by exact_mod_cast hm
  have hupper : (packingResolution p n : ℝ) ≤ 2 * (((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (1 / (2 * p + 1))) := by
    dsimp [packingResolution]
    linarith
  refine ⟨by omega, hm, ?_, hupper, ?_, ?_⟩
  · apply le_trans _ hmlo
    apply Real.rpow_le_rpow hnpos.le _ hα.le
    have hs : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hs hnpos.le
  · have he := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx _) hmlo
      (show -2 * p - 1 ≤ 0 by linarith)
    have heq : (((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (1 / (2 * p + 1))) ^ (-2 * p - 1) =
        ((n : ℝ) * Real.log (n : ℝ) ^ 2)⁻¹ := by
      rw [← Real.rpow_mul hx.le]
      have hc : 1 / (2 * p + 1) * (-2 * p - 1) = -1 := by field_simp; ring
      rw [hc, Real.rpow_neg_one]
    rw [heq] at he
    have hlog2 := log_two_mul_le_twice_log n hn
    have hlog2pos : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    have hsquare : Real.log (2 * (n : ℝ)) ^ 2 ≤ 4 * Real.log (n : ℝ) ^ 2 := by nlinarith
    calc
      _ ≤ (n : ℝ) * Real.log (2 * (n : ℝ)) ^ 2 * ((n : ℝ) * Real.log (n : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ (n : ℝ) * (4 * Real.log (n : ℝ) ^ 2) * ((n : ℝ) * Real.log (n : ℝ) ^ 2)⁻¹ := by gcongr
      _ = 4 := by field_simp
  · have he := Real.rpow_le_rpow_of_nonpos hmR hupper (by linarith : -p ≤ 0)
    have heq : (2 * (((n : ℝ) * Real.log (n : ℝ) ^ 2) ^ (1 / (2 * p + 1)))) ^ (-p) =
        (2 : ℝ) ^ (-p) * lowerBoundRate p n := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
      unfold lowerBoundRate
      congr 2
      ring
    rwa [heq] at he

theorem packingResolution_tendsto (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => (packingResolution p n : ℝ)) atTop atTop := by
  have hα : 0 < 1 / (2 * p + 1) := by positivity
  exact tendsto_atTop_mono' atTop ((packingResolution_bounds p hp).mono fun n hn => hn.2.2.1)
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)

theorem packingResolution_amplitude_log_tendsto (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => (packingResolution p n : ℝ) ^ (-p) * Real.log (2 * (n : ℝ))) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hα : 0 < 1 / (2 * p + 1) := by positivity
  have ht := (nat_log_power_div_rpow_tendsto ((1 / (2 * p + 1)) * p) (by positivity) 1).const_mul 2
  simp only [mul_zero, pow_one] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg (by linarith))
  · filter_upwards [packingResolution_bounds p hp, eventually_ge_atTop 2] with n hn hn2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
    have he := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnR _) hn.2.2.1 (by linarith : -p ≤ 0)
    have heq : ((n : ℝ) ^ (1 / (2 * p + 1))) ^ (-p) = ((n : ℝ) ^ ((1 / (2 * p + 1)) * p))⁻¹ := by
      rw [← Real.rpow_mul hnR.le, ← Real.rpow_neg hnR.le]
      congr 1
      ring
    rw [heq] at he
    have hl : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * n by omega))
    calc
      _ ≤ ((n : ℝ) ^ ((1 / (2 * p + 1)) * p))⁻¹ * (2 * Real.log (n : ℝ)) :=
        mul_le_mul he (log_two_mul_le_twice_log n hn2) hl (by positivity)
      _ = _ := by ring

theorem packingResolution_derivative_entropy_tendsto (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => (packingResolution p n : ℝ) ^ (1 - 2 * p) * Real.log (2 * (n : ℝ)) ^ 2)
      atTop (𝓝 0) := by
  have hα : 0 < 1 / (2 * p + 1) := by positivity
  have ht := (nat_log_power_div_rpow_tendsto (1 / (2 * p + 1)) hα 2).const_mul 4
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ ht
  filter_upwards [packingResolution_bounds p hp, eventually_ge_atTop 2] with n hn hn2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by positivity
  have hmone : (1 : ℝ) ≤ packingResolution p n := by exact_mod_cast hn.2.1
  have he1 := Real.rpow_le_rpow_of_exponent_le hmone (show 1 - 2 * p ≤ -1 by linarith)
  have he2 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnpos _) hn.2.2.1 (by norm_num : (-1 : ℝ) ≤ 0)
  rw [Real.rpow_neg_one] at he1 he2
  have heq : ((n : ℝ) ^ (1 / (2 * p + 1))) ^ (-1 : ℝ) = ((n : ℝ) ^ (1 / (2 * p + 1)))⁻¹ := Real.rpow_neg_one _
  rw [heq] at he2
  have hl : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hlog2 := log_two_mul_le_twice_log n hn2
  have hsq : Real.log (2 * (n : ℝ)) ^ 2 ≤ 4 * Real.log (n : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ ((n : ℝ) ^ (1 / (2 * p + 1)))⁻¹ * (4 * Real.log (n : ℝ) ^ 2) :=
      mul_le_mul (he1.trans he2) hsq (by positivity) (by positivity)
    _ = _ := by ring

end Hurst
