import Hurst.MixedPower

noncomputable section
open Set
namespace Hurst

def meshPowerEnvelope (n : ℕ) (p : ℝ) : ℝ := 1 + (2 * (n : ℝ)) ^ (1 - p)

theorem meshPowerEnvelope_nonneg (n : ℕ) (p : ℝ) : 0 ≤ meshPowerEnvelope n p := by
  unfold meshPowerEnvelope
  positivity

theorem mesh_positive_power_control_general (n : ℕ) (hn : 0 < n) (p x : ℝ)
    (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1) :
    |Real.log x| ≤ Real.log (2 * (n : ℝ)) ∧ x ^ (p - 1) ≤ meshPowerEnvelope n p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hx.1
  have hlog : |Real.log x| ≤ Real.log (2 * (n : ℝ)) := by
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx.2)]
    have he := Real.log_le_log (by positivity : 0 < 1 / (2 * (n : ℝ))) hx.1
    simp only [one_div, Real.log_inv] at he
    linarith
  refine ⟨hlog, ?_⟩
  by_cases hp : 1 ≤ p
  · have he : x ^ (p - 1) ≤ 1 := Real.rpow_le_one hx0.le hx.2 (by linarith)
    exact he.trans (by unfold meshPowerEnvelope; linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * n by positivity) (1 - p)])
  · have he := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 / (2 * (n : ℝ))) hx.1 (by linarith : p - 1 ≤ 0)
    have hid : (1 / (2 * (n : ℝ))) ^ (p - 1) = (2 * (n : ℝ)) ^ (1 - p) := by
      rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
      congr 1
      ring
    rw [hid] at he
    exact he.trans (by unfold meshPowerEnvelope; linarith)

/-- Uniform spatial derivatives away from zero on the observation half-mesh. -/
theorem mesh_power_derivative_bounds_general (n : ℕ) (hn : 0 < n) (p x : ℝ)
    (hp0 : 0 < p) (hp2 : p ≤ 2)
    (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1) :
    ‖p * x ^ (p - 1)‖ ≤ 2 * meshPowerEnvelope n p ∧
      ‖x ^ (p - 1) * (1 + p * Real.log x)‖ ≤ meshPowerEnvelope n p * (1 + 2 * Real.log (2 * (n : ℝ))) := by
  have hE := meshPowerEnvelope_nonneg n p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hE := meshPowerEnvelope_nonneg n p
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 < x := (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hx.1
  obtain ⟨hl, hpow⟩ := mesh_positive_power_control_general n hn p x hx
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
  constructor
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp0, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact mul_le_mul hp2 hpow (Real.rpow_nonneg hx0.le _) (by norm_num)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have he : |1 + p * Real.log x| ≤ 1 + 2 * Real.log (2 * (n : ℝ)) := by
      have ht := abs_add_le (1 : ℝ) (p * Real.log x)
      rw [abs_one, abs_mul, abs_of_pos hp0] at ht
      have hm := mul_le_mul hp2 hl (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    exact mul_le_mul hpow he (abs_nonneg _) (meshPowerEnvelope_nonneg n p)

/-- A zero endpoint is handled by its value, not by taking a spatial derivative there. -/
theorem mesh_power_zero_bounds_general (n : ℕ) (hn : 0 < n) (p x : ℝ)
    (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1) :
    |x ^ p| ≤ meshPowerEnvelope n p * x ∧
      |x ^ p * Real.log x| ≤ meshPowerEnvelope n p * Real.log (2 * (n : ℝ)) * x := by
  have hE := meshPowerEnvelope_nonneg n p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hx.1
  obtain ⟨hl, hpow⟩ := mesh_positive_power_control_general n hn p x hx
  have he : x ^ p = x ^ (p - 1) * x := by
    calc
      _ = x ^ (p - 1 + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
  have hb : |x ^ p| ≤ meshPowerEnvelope n p * x := by
    rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _), he]
    exact mul_le_mul_of_nonneg_right hpow hx0.le
  refine ⟨hb, ?_⟩
  rw [abs_mul]
  have hm := mul_le_mul hb hl (abs_nonneg _) (by positivity)
  exact hm.trans_eq (by ring)

theorem mesh_power_pair_bounds_positive_general (n : ℕ) (hn : 0 < n) (p x y : ℝ)
    (hp0 : 0 < p) (hp2 : p ≤ 2)
    (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1) (hy : y ∈ Icc (1 / (2 * (n : ℝ))) 1) :
    |x ^ p - y ^ p| ≤ (2 * meshPowerEnvelope n p) * |x - y| ∧
      |x ^ p * Real.log x - y ^ p * Real.log y| ≤
        (meshPowerEnvelope n p * (1 + 2 * Real.log (2 * (n : ℝ)))) * |x - y| := by
  have hE := meshPowerEnvelope_nonneg n p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ u ∈ Icc (1 / (2 * (n : ℝ))) 1, 0 < u :=
    fun u hu => (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hu.1
  constructor
  · have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (Real.hasDerivAt_rpow_const (p := p) (Or.inl (hpos u hu).ne')).hasDerivWithinAt)
      (fun u hu => (mesh_power_derivative_bounds_general n hn p u hp0 hp2 hu).1)
      (convex_Icc (1 / (2 * (n : ℝ))) 1) hy hx
    simpa only [Real.norm_eq_abs] using hm
  · have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (positive_power_log_hasDerivAt p u (hpos u hu)).hasDerivWithinAt)
      (fun u hu => (mesh_power_derivative_bounds_general n hn p u hp0 hp2 hu).2)
      (convex_Icc (1 / (2 * (n : ℝ))) 1) hy hx
    simpa only [Real.norm_eq_abs] using hm

/-- The spatial estimate includes coincident grid locations and the unobserved origin. -/
theorem mesh_power_pair_bounds_general (n : ℕ) (hn : 0 < n) (p x y : ℝ)
    (hp0 : 0 < p) (hp2 : p ≤ 2)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxs : meshSeparatedFromZero n x) (hys : meshSeparatedFromZero n y) :
    |x ^ p - y ^ p| ≤ (2 * meshPowerEnvelope n p) * |x - y| ∧
      |x ^ p * Real.log x - y ^ p * Real.log y| ≤
        (meshPowerEnvelope n p * (1 + 2 * Real.log (2 * (n : ℝ)))) * |x - y| := by
  have hE := meshPowerEnvelope_nonneg n p
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
  have hzero : ∀ z ∈ Icc (1 / (2 * (n : ℝ))) 1,
      |z ^ p| ≤ (2 * meshPowerEnvelope n p) * |z| ∧
      |z ^ p * Real.log z| ≤ (meshPowerEnvelope n p * (1 + 2 * Real.log (2 * (n : ℝ)))) * |z| := by
    intro z hz
    have hE := meshPowerEnvelope_nonneg n p
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hz0 : 0 ≤ z := (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ))).trans hz.1
    obtain ⟨h1, h2⟩ := mesh_power_zero_bounds_general n hn p z hz
    rw [abs_of_nonneg hz0]
    constructor
    · have he : 0 ≤ meshPowerEnvelope n p * z := by positivity
      nlinarith
    · have hc : meshPowerEnvelope n p * Real.log (2 * (n : ℝ)) ≤ meshPowerEnvelope n p * (1 + 2 * Real.log (2 * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (meshPowerEnvelope_nonneg n p)
        linarith
      exact h2.trans (mul_le_mul_of_nonneg_right hc hz0)
  rcases hxs with rfl | hxs
  · rcases hys with rfl | hys
    · simp
    · simpa only [Real.zero_rpow hp0.ne', zero_mul, zero_sub, abs_neg] using hzero y ⟨hys, hy.2⟩
  · rcases hys with rfl | hys
    · simpa only [Real.zero_rpow hp0.ne', zero_mul, sub_zero] using hzero x ⟨hxs, hx.2⟩
    · exact mesh_power_pair_bounds_positive_general n hn p x y hp0 hp2 ⟨hxs, hx.2⟩ ⟨hys, hy.2⟩

end Hurst
