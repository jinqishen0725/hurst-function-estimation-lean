import Hurst.FrozenEstimates

noncomputable section
open Set
namespace Hurst

def meshSeparatedFromZero (n : ℕ) (x : ℝ) : Prop := x = 0 ∨ 1 / (2 * (n : ℝ)) ≤ x

theorem mesh_positive_power_control (n : ℕ) (hn : 0 < n) (p a x : ℝ)
    (ha : 0 ≤ a) (hp : |p - 1| ≤ 2 * a) (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1)
    (hsmall : a * Real.log (2 * (n : ℝ)) ≤ 1) :
    |Real.log x| ≤ Real.log (2 * (n : ℝ)) ∧ x ^ (p - 1) ≤ Real.exp 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hx.1
  have hlog : |Real.log x| ≤ Real.log (2 * (n : ℝ)) := by
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx.2)]
    have he := Real.log_le_log (by positivity : 0 < 1 / (2 * (n : ℝ))) hx.1
    simp only [one_div, Real.log_inv] at he
    linarith
  refine ⟨hlog, ?_⟩
  have he := mul_le_mul hp hlog (abs_nonneg _) (show 0 ≤ 2 * a by positivity)
  exact rpow_le_exp_of_log_bound x (p - 1) 2 hx0 (by nlinarith)

theorem positive_power_log_hasDerivAt (p x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => y ^ p * Real.log y) (x ^ (p - 1) * (1 + p * Real.log x)) x := by
  have hd := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).mul (Real.hasDerivAt_log hx.ne')
  have he : x ^ p = x ^ (p - 1) * x := by
    calc
      _ = x ^ (p - 1 + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]
  convert! hd using 1
  rw [he]
  field_simp
  ring

/-- Uniform spatial derivatives away from zero on the observation half-mesh. -/
theorem mesh_power_derivative_bounds (n : ℕ) (hn : 0 < n) (p a x : ℝ)
    (ha : 0 ≤ a) (hp0 : 0 < p) (hp2 : p ≤ 2) (hp : |p - 1| ≤ 2 * a)
    (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1) (hsmall : a * Real.log (2 * (n : ℝ)) ≤ 1) :
    ‖p * x ^ (p - 1)‖ ≤ 2 * Real.exp 2 ∧
      ‖x ^ (p - 1) * (1 + p * Real.log x)‖ ≤ Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 < x := (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hx.1
  obtain ⟨hl, hpow⟩ := mesh_positive_power_control n hn p a x ha hp hx hsmall
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
    exact mul_le_mul hpow he (abs_nonneg _) (Real.exp_pos _).le

/-- A zero endpoint is handled by its value, not by taking a spatial derivative there. -/
theorem mesh_power_zero_bounds (n : ℕ) (hn : 0 < n) (p a x : ℝ)
    (ha : 0 ≤ a) (hp : |p - 1| ≤ 2 * a) (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1)
    (hsmall : a * Real.log (2 * (n : ℝ)) ≤ 1) :
    |x ^ p| ≤ Real.exp 2 * x ∧
      |x ^ p * Real.log x| ≤ Real.exp 2 * Real.log (2 * (n : ℝ)) * x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hx.1
  obtain ⟨hl, hpow⟩ := mesh_positive_power_control n hn p a x ha hp hx hsmall
  have he : x ^ p = x ^ (p - 1) * x := by
    calc
      _ = x ^ (p - 1 + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
  have hb : |x ^ p| ≤ Real.exp 2 * x := by
    rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _), he]
    exact mul_le_mul_of_nonneg_right hpow hx0.le
  refine ⟨hb, ?_⟩
  rw [abs_mul]
  have hm := mul_le_mul hb hl (abs_nonneg _) (by positivity)
  exact hm.trans_eq (by ring)

theorem mesh_power_pair_bounds_positive (n : ℕ) (hn : 0 < n) (p a x y : ℝ)
    (ha : 0 ≤ a) (hp0 : 0 < p) (hp2 : p ≤ 2) (hp : |p - 1| ≤ 2 * a)
    (hx : x ∈ Icc (1 / (2 * (n : ℝ))) 1) (hy : y ∈ Icc (1 / (2 * (n : ℝ))) 1)
    (hsmall : a * Real.log (2 * (n : ℝ)) ≤ 1) :
    |x ^ p - y ^ p| ≤ (2 * Real.exp 2) * |x - y| ∧
      |x ^ p * Real.log x - y ^ p * Real.log y| ≤
        (Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ)))) * |x - y| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ u ∈ Icc (1 / (2 * (n : ℝ))) 1, 0 < u :=
    fun u hu => (by positivity : 0 < 1 / (2 * (n : ℝ))).trans_le hu.1
  constructor
  · have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (Real.hasDerivAt_rpow_const (p := p) (Or.inl (hpos u hu).ne')).hasDerivWithinAt)
      (fun u hu => (mesh_power_derivative_bounds n hn p a u ha hp0 hp2 hp hu hsmall).1)
      (convex_Icc (1 / (2 * (n : ℝ))) 1) hy hx
    simpa only [Real.norm_eq_abs] using hm
  · have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (positive_power_log_hasDerivAt p u (hpos u hu)).hasDerivWithinAt)
      (fun u hu => (mesh_power_derivative_bounds n hn p a u ha hp0 hp2 hp hu hsmall).2)
      (convex_Icc (1 / (2 * (n : ℝ))) 1) hy hx
    simpa only [Real.norm_eq_abs] using hm

/-- The spatial estimate includes coincident grid locations and the unobserved origin. -/
theorem mesh_power_pair_bounds (n : ℕ) (hn : 0 < n) (p a x y : ℝ)
    (ha : 0 ≤ a) (hp0 : 0 < p) (hp2 : p ≤ 2) (hp : |p - 1| ≤ 2 * a)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxs : meshSeparatedFromZero n x) (hys : meshSeparatedFromZero n y)
    (hsmall : a * Real.log (2 * (n : ℝ)) ≤ 1) :
    |x ^ p - y ^ p| ≤ (2 * Real.exp 2) * |x - y| ∧
      |x ^ p * Real.log x - y ^ p * Real.log y| ≤
        (Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ)))) * |x - y| := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
  have hzero : ∀ z ∈ Icc (1 / (2 * (n : ℝ))) 1,
      |z ^ p| ≤ (2 * Real.exp 2) * |z| ∧
      |z ^ p * Real.log z| ≤ (Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ)))) * |z| := by
    intro z hz
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hz0 : 0 ≤ z := (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ))).trans hz.1
    obtain ⟨h1, h2⟩ := mesh_power_zero_bounds n hn p a z ha hp hz hsmall
    rw [abs_of_nonneg hz0]
    constructor
    · have he : 0 ≤ Real.exp 2 * z := by positivity
      nlinarith
    · have hc : Real.exp 2 * Real.log (2 * (n : ℝ)) ≤ Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith
      exact h2.trans (mul_le_mul_of_nonneg_right hc hz0)
  rcases hxs with rfl | hxs
  · rcases hys with rfl | hys
    · simp
    · simpa only [Real.zero_rpow hp0.ne', zero_mul, zero_sub, abs_neg] using hzero y ⟨hys, hy.2⟩
  · rcases hys with rfl | hys
    · simpa only [Real.zero_rpow hp0.ne', zero_mul, sub_zero] using hzero x ⟨hxs, hx.2⟩
    · exact mesh_power_pair_bounds_positive n hn p a x y ha hp0 hp2 hp ⟨hxs, hx.2⟩ ⟨hys, hy.2⟩ hsmall

def halfMeshPoint (n : ℕ) (x : ℝ) : Prop := ∃ k : ℕ, x = (k : ℝ) / (2 * n)

theorem halfMeshPoint_grid (n i : ℕ) : halfMeshPoint n (grid n i) := by
  refine ⟨2 * i + 1, ?_⟩
  simp only [grid, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem halfMeshPoint_midpointLeft (n : ℕ) (i : Fin n) : halfMeshPoint n (midpointLeft n i) := by
  unfold midpointLeft
  split_ifs
  · exact ⟨0, by simp⟩
  · exact halfMeshPoint_grid n (previousGridIndex i).val

theorem halfMeshPoint_separated (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : halfMeshPoint n x) :
    meshSeparatedFromZero n x := by
  obtain ⟨k, rfl⟩ := hx
  by_cases hk : k = 0
  · left
    simp [hk]
  · right
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    exact div_le_div_of_nonneg_right hkR (by positivity)

theorem halfMeshPoint_abs_sub (n : ℕ) (x y : ℝ) (hx : halfMeshPoint n x) (hy : halfMeshPoint n y) :
    halfMeshPoint n |x - y| := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  have hn : 0 ≤ 2 * (n : ℝ) := by positivity
  rw [← sub_div, abs_div, abs_of_nonneg hn]
  rcases le_total k l with hkl | hlk
  · refine ⟨l - k, ?_⟩
    rw [Nat.cast_sub hkl, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hkl))]
  · refine ⟨k - l, ?_⟩
    rw [Nat.cast_sub hlk, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlk))]

end Hurst
