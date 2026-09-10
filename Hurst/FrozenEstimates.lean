import Hurst.MidpointWhitening

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem exp_sub_one_le_exp_mul (x M : ℝ) (hM : 0 ≤ M) (hx : |x| ≤ M) :
    |Real.exp x - 1| ≤ Real.exp M * |x| := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => show ‖Real.exp u‖ ≤ Real.exp M from by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hu.2)
    (convex_Icc (-M) M) (show (0 : ℝ) ∈ Icc (-M) M from ⟨by linarith, hM⟩)
    (show x ∈ Icc (-M) M from abs_le.mp hx)
  simpa only [Real.exp_zero, sub_zero, Real.norm_eq_abs] using hmvt

theorem rpow_sub_one_bound (x p M : ℝ) (hx : 0 < x) (hM : 0 ≤ M)
    (hp : |p * Real.log x| ≤ M) :
    |x ^ p - 1| ≤ Real.exp M * (|p| * |Real.log x|) := by
  rw [Real.rpow_def_of_pos hx]
  simpa only [mul_comm, abs_mul] using exp_sub_one_le_exp_mul (p * Real.log x) M hM hp

theorem frozenIncrementFeature_diagonal_bound (h : Ioo (0 : ℝ) 1) (s ℓ a L : ℝ)
    (hl : 0 < ℓ) (ha : 0 ≤ a) (_hL : 0 ≤ L) (hh : |(h : ℝ) - 1 / 2| ≤ a)
    (hlog : |Real.log ℓ| ≤ L) (hsmall : a * L ≤ 1) :
    |‖frozenIncrementFeature h s ℓ‖ ^ 2 - 1| ≤ (2 * Real.exp 2) * a * L := by
  have he : 2 * (h : ℝ) - 1 = 2 * ((h : ℝ) - 1 / 2) := by ring
  have hp : |2 * (h : ℝ) - 1| ≤ 2 * a := by
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have hprod : |2 * (h : ℝ) - 1| * |Real.log ℓ| ≤ (2 * a) * L :=
    mul_le_mul hp hlog (abs_nonneg _) (by positivity)
  rw [frozenIncrementFeature_norm_sq h s ℓ hl]
  have hbd := rpow_sub_one_bound ℓ (2 * (h : ℝ) - 1) 2 hl (by norm_num)
    (by rw [abs_mul]; nlinarith)
  have hm := mul_le_mul_of_nonneg_left hprod (Real.exp_pos 2).le
  calc
    _ ≤ Real.exp 2 * (|2 * (h : ℝ) - 1| * |Real.log ℓ|) := hbd
    _ ≤ Real.exp 2 * ((2 * a) * L) := hm
    _ = _ := by ring

theorem midpointStep_log_bound (n : ℕ) (i : Fin n) :
    |Real.log (midpointStep n i)| ≤ Real.log (2 * (n : ℝ)) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  have hn0 : (0 : ℝ) < n := by linarith
  have h2n : (1 : ℝ) ≤ 2 * n := by linarith
  unfold midpointStep
  split_ifs
  · simp only [one_div, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg h2n)]
    exact le_rfl
  · simp only [one_div, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg hn)]
    exact Real.log_le_log hn0 (by linarith)

theorem midpointFrozen_diagonal_bound (n : ℕ) (i : Fin n) (h : Ioo (0 : ℝ) 1) (a : ℝ)
    (ha : 0 ≤ a) (hh : |(h : ℝ) - 1 / 2| ≤ a) (hsmall : a * Real.log (2 * (n : ℝ)) ≤ 1) :
    |‖frozenIncrementFeature h (midpointLeft n i) (midpointStep n i)‖ ^ 2 - 1| ≤
      (2 * Real.exp 2) * a * Real.log (2 * (n : ℝ)) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  exact frozenIncrementFeature_diagonal_bound h _ _ a _ (midpointStep_pos n i) ha
    (Real.log_nonneg (by linarith)) hh (midpointStep_log_bound n i) hsmall

/-- A mean-value bound retaining the exponent factor, used for separated increment covariances. -/
theorem rpow_difference_bound_of_lower (p δ x y : ℝ) (hp : p ≤ 1) (hd : 0 < δ)
    (hx : δ ≤ x) (hy : δ ≤ y) :
    |x ^ p - y ^ p| ≤ (|p| * δ ^ (p - 1)) * |x - y| := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hd.trans_le hu)))).hasDerivWithinAt)
    (fun u hu => show ‖p * u ^ (p - 1)‖ ≤ |p| * δ ^ (p - 1) from by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hd.trans_le hu).le _)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg p)
      exact Real.rpow_le_rpow_of_nonpos hd hu (by linarith))
    (convex_Ici δ) hy hx
  simpa only [Real.norm_eq_abs] using hmvt

/-- The separated-interval power remainder retains the essential p-1 cancellation. -/
theorem rpow_rectangle_bound (p a b c d : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) :
    |(d - a) ^ p - (d - b) ^ p - ((c - a) ^ p - (c - b) ^ p)| ≤
      (p * |p - 1| * (c - b) ^ (p - 2) * (b - a)) * (d - c) := by
  have hderiv : ∀ u ∈ Icc c d, HasDerivAt (fun u => (u - a) ^ p - (u - b) ^ p)
      (p * ((u - a) ^ (p - 1) - (u - b) ^ (p - 1))) u := by
    intro u hu
    have hua : u - a ≠ 0 := ne_of_gt (by linarith [hu.1] : 0 < u - a)
    have hub : u - b ≠ 0 := ne_of_gt (by linarith [hu.1] : 0 < u - b)
    have h1 := ((hasDerivAt_id u).sub_const a).rpow_const (p := p) (Or.inl hua)
    have h2 := ((hasDerivAt_id u).sub_const b).rpow_const (p := p) (Or.inl hub)
    convert! h1.sub h2 using 1
    simp only [id_eq, one_mul]
    ring
  have hbound : ∀ u ∈ Icc c d,
      ‖p * ((u - a) ^ (p - 1) - (u - b) ^ (p - 1))‖ ≤
        p * |p - 1| * (c - b) ^ (p - 2) * (b - a) := by
    intro u hu
    have hi := rpow_difference_bound_of_lower (p - 1) (c - b) (u - a) (u - b)
      (by linarith) (by linarith) (by linarith [hu.1]) (by linarith [hu.1])
    rw [show p - 1 - 1 = p - 2 by ring,
      show u - a - (u - b) = b - a by ring, abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    have hm := mul_le_mul_of_nonneg_left hi hp
    calc
      _ ≤ p * ((|p - 1| * (c - b) ^ (p - 2)) * (b - a)) := hm
      _ = _ := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hderiv u hu).hasDerivWithinAt) hbound (convex_Icc c d)
    (left_mem_Icc.mpr hcd) (right_mem_Icc.mpr hcd)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcd)] using hmvt

def harmonizableCovCoeff (h k : ℝ) : ℝ :=
  harmonizableD ((h + k) / 2) ^ 2 / (2 * harmonizableD h * harmonizableD k)

theorem harmonizableCovCoeff_nonneg (h k : Ioo (0 : ℝ) 1) :
    0 ≤ harmonizableCovCoeff h k := by
  unfold harmonizableCovCoeff
  apply div_nonneg (sq_nonneg _)
  exact mul_nonneg (mul_nonneg (by norm_num) (harmonizableD_pos h h.property.1 h.property.2).le)
    (harmonizableD_pos k k.property.1 k.property.2).le

theorem frozenIncrementFeature_inner_rectangle (h k : Ioo (0 : ℝ) 1) (s ℓ t m : ℝ)
    (hl : 0 < ℓ) (hm : 0 < m) (hst : s + ℓ ≤ t) :
    ⟪frozenIncrementFeature h s ℓ, frozenIncrementFeature k t m⟫ =
      (harmonizableCovCoeff h k * (Real.sqrt ℓ)⁻¹ * (Real.sqrt m)⁻¹) *
      ((t + m - s) ^ ((h : ℝ) + k) - (t + m - (s + ℓ)) ^ ((h : ℝ) + k) -
        ((t - s) ^ ((h : ℝ) + k) - (t - (s + ℓ)) ^ ((h : ℝ) + k))) := by
  have e1 : |s + ℓ - (t + m)| = t + m - (s + ℓ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have e2 : |s - (t + m)| = t + m - s := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have e3 : |s + ℓ - t| = t - (s + ℓ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have e4 : |s - t| = t - s := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  simp only [frozenIncrementFeature, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, harmonizableFeature_inner_formula, e1, e2, e3, e4,
    harmonizableCovCoeff]
  ring

/-- An actual nonadjacent frozen covariance bound with its vanishing Brownian factor. -/
theorem frozenIncrementFeature_inner_bound_separated (h k : Ioo (0 : ℝ) 1) (s ℓ t m : ℝ)
    (hl : 0 < ℓ) (hm : 0 < m) (hst : s + ℓ < t) :
    |⟪frozenIncrementFeature h s ℓ, frozenIncrementFeature k t m⟫| ≤
      (harmonizableCovCoeff h k * (Real.sqrt ℓ)⁻¹ * (Real.sqrt m)⁻¹) *
      ((((h : ℝ) + k) * |(h : ℝ) + k - 1| *
        (t - (s + ℓ)) ^ ((h : ℝ) + k - 2) * ℓ) * m) := by
  have hr := rpow_rectangle_bound ((h : ℝ) + k) s (s + ℓ) t (t + m)
    (by linarith [h.property.1, k.property.1]) (by linarith [h.property.2, k.property.2])
    (by linarith) hst (by linarith)
  simp only [add_sub_cancel_left] at hr
  rw [frozenIncrementFeature_inner_rectangle h k s ℓ t m hl hm hst.le, abs_mul,
    abs_of_nonneg (mul_nonneg (mul_nonneg (harmonizableCovCoeff_nonneg h k)
      (inv_nonneg.mpr (Real.sqrt_nonneg ℓ))) (inv_nonneg.mpr (Real.sqrt_nonneg m)))]
  exact mul_le_mul_of_nonneg_left hr (mul_nonneg (mul_nonneg (harmonizableCovCoeff_nonneg h k)
      (inv_nonneg.mpr (Real.sqrt_nonneg ℓ))) (inv_nonneg.mpr (Real.sqrt_nonneg m)))

/-- Adjacent intervals are controlled in the exponent parameter, without a singular spatial derivative. -/
theorem adjacent_power_shape_bound (r s a b : ℝ) (hr : 0 < r) (hs : 0 < s)
    (ha : a ≤ 1) (hb : 1 ≤ b) :
    ∃ C ≥ 0, ∀ p ∈ Icc a b, |(r + s) ^ p - r ^ p - s ^ p| ≤ C * |p - 1| := by
  let f := fun p : ℝ => (r + s) ^ p - r ^ p - s ^ p
  let df := fun p : ℝ => Real.log (r + s) * (r + s) ^ p - Real.log r * r ^ p - Real.log s * s ^ p
  have hrs : 0 < r + s := by linarith
  have hd : ∀ p, HasDerivAt f (df p) p := by
    intro p
    have h1 := (hasDerivAt_id p).const_rpow hrs
    have h2 := (hasDerivAt_id p).const_rpow hr
    have h3 := (hasDerivAt_id p).const_rpow hs
    convert! (h1.sub h2).sub h3 using 1
    simp only [df, id_eq, mul_one]
  have hc : Continuous df := by
    exact (((Real.continuous_const_rpow hrs.ne').const_mul (Real.log (r + s))).sub
      ((Real.continuous_const_rpow hr.ne').const_mul (Real.log r))).sub
      ((Real.continuous_const_rpow hs.ne').const_mul (Real.log s))
  obtain ⟨u, hu, hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (ha.trans hb)) hc.norm.continuousOn
  have hf1 : f 1 = 0 := by simp only [f, Real.rpow_one]; ring
  refine ⟨‖df u‖, norm_nonneg _, ?_⟩
  intro p hp
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hd v).hasDerivWithinAt) (fun v hv => hm hv) (convex_Icc a b)
    (show (1 : ℝ) ∈ Icc a b from ⟨ha, hb⟩) hp
  simpa only [hf1, sub_zero, Real.norm_eq_abs, f] using hmvt

/-- The covariance prefactor is uniformly bounded over the same compact Hurst range. -/
theorem harmonizableCovCoeff_uniform_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      harmonizableCovCoeff h k ≤ C := by
  obtain ⟨c, hc, hcmin⟩ := harmonizableD_uniform_pos a b ha hb hab
  have hcont := harmonizableD_continuousOn.mono
    (show Icc a b ⊆ Ioo (0 : ℝ) 1 from fun h hh => ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩)
  obtain ⟨u, hu, humax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hcont
  refine ⟨harmonizableD u ^ 2 / (2 * c ^ 2), by positivity, ?_⟩
  intro h k hh hk
  have hm : ((h : ℝ) + k) / 2 ∈ Icc a b := by constructor <;> linarith [hh.1, hh.2, hk.1, hk.2]
  have hmid0 := harmonizableD_pos (((h : ℝ) + k) / 2) (ha.trans_le hm.1) (hm.2.trans_lt hb)
  have hsq := pow_le_pow_left₀ hmid0.le (humax hm) 2
  have hden : 2 * c ^ 2 ≤ 2 * harmonizableD h * harmonizableD k := by
    have hm := mul_le_mul (hcmin h hh) (hcmin k hk) hc.le (harmonizableD_pos h h.property.1 h.property.2).le
    nlinarith
  unfold harmonizableCovCoeff
  exact div_le_div₀ (sq_nonneg _) hsq (by positivity) hden

theorem hurst_sum_deviation (h k a : ℝ) (hh : |h - 1 / 2| ≤ a) (hk : |k - 1 / 2| ≤ a) :
    |h + k - 1| ≤ 2 * a := by
  have ht := abs_add_le (h - 1 / 2) (k - 1 / 2)
  rw [show h - 1 / 2 + (k - 1 / 2) = h + k - 1 by ring] at ht
  linarith

theorem rpow_le_exp_of_log_bound (x p M : ℝ) (hx : 0 < x) (hp : |p| * |Real.log x| ≤ M) :
    x ^ p ≤ Real.exp M := by
  rw [Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by simpa only [abs_mul, mul_comm] using hp))

theorem rpow_near_one_div_bound (x p a L : ℝ) (hx : 0 < x) (ha : 0 ≤ a)
    (hp : |p - 1| ≤ 2 * a) (hlog : |Real.log x| ≤ L) (hsmall : a * L ≤ 1) :
    x ^ (p - 2) ≤ Real.exp 2 / x := by
  have hprod := mul_le_mul hp hlog (abs_nonneg (Real.log x)) (show 0 ≤ 2 * a by positivity)
  have he := rpow_le_exp_of_log_bound x (p - 1) 2 hx (by nlinarith)
  rw [le_div_iff₀ hx]
  have hid : x ^ (p - 2) * x = x ^ (p - 1) := by
    calc
      _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ (p - 2 + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by congr 1; ring
  rwa [hid]

/-- A bound uniform near one-half, retaining inverse distance decay. -/
theorem frozenIncrementFeature_separated_uniform_bound (h k : Ioo (0 : ℝ) 1)
    (s ℓ t m a L C : ℝ) (hl : 0 < ℓ) (hm : 0 < m) (hst : s + ℓ < t)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hc : harmonizableCovCoeff h k ≤ C)
    (hh : |(h : ℝ) - 1 / 2| ≤ a) (hk : |(k : ℝ) - 1 / 2| ≤ a)
    (hlog : |Real.log (t - (s + ℓ))| ≤ L) (hsmall : a * L ≤ 1) :
    |⟪frozenIncrementFeature h s ℓ, frozenIncrementFeature k t m⟫| ≤
      (4 * C * Real.exp 2) * a * (Real.sqrt ℓ * Real.sqrt m / (t - (s + ℓ))) := by
  have hd : 0 < t - (s + ℓ) := by linarith
  have hp := hurst_sum_deviation h k a hh hk
  have hpow := rpow_near_one_div_bound (t - (s + ℓ)) ((h : ℝ) + k) a L hd ha hp hlog hsmall
  have hα : 0 ≤ (h : ℝ) + k := by linarith [h.property.1, k.property.1]
  have hα2 : (h : ℝ) + k ≤ 2 := by linarith [h.property.2, k.property.2]
  have hbound := frozenIncrementFeature_inner_bound_separated h k s ℓ t m hl hm hst
  have hm1 := mul_le_mul hα2 hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hm2 := mul_le_mul hm1 hpow (Real.rpow_nonneg hd.le _) (by positivity : 0 ≤ 2 * (2 * a))
  have hm3 := mul_le_mul hc hm2
    (mul_nonneg (mul_nonneg hα (abs_nonneg _)) (Real.rpow_nonneg hd.le _)) hC
  have hscale : 0 ≤ (Real.sqrt ℓ)⁻¹ * (Real.sqrt m)⁻¹ * ℓ * m := by positivity
  have hm4 := mul_le_mul_of_nonneg_right hm3 hscale
  have hsl : (Real.sqrt ℓ)⁻¹ * ℓ = Real.sqrt ℓ := by
    field_simp
    exact (Real.sq_sqrt hl.le).symm
  have hsm : (Real.sqrt m)⁻¹ * m = Real.sqrt m := by
    field_simp
    exact (Real.sq_sqrt hm.le).symm
  calc
    _ ≤ _ := hbound
    _ = (harmonizableCovCoeff h k * (((h : ℝ) + k) * |(h : ℝ) + k - 1| *
        (t - (s + ℓ)) ^ ((h : ℝ) + k - 2))) *
        ((Real.sqrt ℓ)⁻¹ * (Real.sqrt m)⁻¹ * ℓ * m) := by ring
    _ ≤ (C * (2 * (2 * a) * (Real.exp 2 / (t - (s + ℓ))))) *
        ((Real.sqrt ℓ)⁻¹ * (Real.sqrt m)⁻¹ * ℓ * m) := hm4
    _ = _ := by
      have he : (Real.sqrt ℓ)⁻¹ * (Real.sqrt m)⁻¹ * ℓ * m = Real.sqrt ℓ * Real.sqrt m := by
        calc
          _ = ((Real.sqrt ℓ)⁻¹ * ℓ) * ((Real.sqrt m)⁻¹ * m) := by ring
          _ = _ := by rw [hsl, hsm]
      rw [he]
      ring

/-- The first midpoint interval is half-length; the others have the ordinary mesh length. -/
theorem midpointStep_ge_half (n : ℕ) (i : Fin n) :
    1 / (2 * (n : ℝ)) ≤ midpointStep n i := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  unfold midpointStep
  split_ifs
  · exact le_rfl
  · exact div_le_div_of_nonneg_left (by norm_num) hn (by linarith)

theorem midpoint_gap_formula (n : ℕ) (i j : Fin n) (hij : i < j) :
    midpointLeft n j - (midpointLeft n i + midpointStep n i) =
      ((j.val : ℝ) - i.val - 1) / n := by
  have hj : j.val ≠ 0 := by have hh : i.val < j.val := hij; omega
  have hjc : ((j.val - 1 : ℕ) : ℝ) = (j.val : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j.val), Nat.cast_one]
  rw [← midpoint_grid_eq_left_add_step]
  simp only [midpointLeft, if_neg hj, grid, previousGridIndex, hjc]
  ring

theorem midpoint_gap_log_bound (n : ℕ) (i j : Fin n) (hij : i.val + 1 < j.val) :
    |Real.log (midpointLeft n j - (midpointLeft n i + midpointStep n i))| ≤
      Real.log (2 * (n : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi : (i.val : ℝ) + 2 ≤ j.val := by exact_mod_cast (show i.val + 2 ≤ j.val by omega)
  have hj : (j.val : ℝ) < n := by exact_mod_cast j.isLt
  rw [midpoint_gap_formula n i j (by exact show i.val < j.val by omega)]
  have hlow : 1 / (2 * (n : ℝ)) ≤ ((j.val : ℝ) - i.val - 1) / n := by
    apply (div_le_div_iff₀ (by positivity) hn).mpr
    nlinarith
  have hpos : 0 < ((j.val : ℝ) - i.val - 1) / n := div_pos (by linarith) hn
  have hup : ((j.val : ℝ) - i.val - 1) / n ≤ 1 := by
    apply (div_le_iff₀ hn).mpr
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    linarith
  rw [abs_of_nonpos (Real.log_nonpos hpos.le hup)]
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (2 * (n : ℝ))) hlow
  simp only [one_div, Real.log_inv] at hlog
  linarith

theorem midpoint_sqrt_gap_ratio_bound (n : ℕ) (i j : Fin n) (hij : i.val + 1 < j.val) :
    Real.sqrt (midpointStep n i) * Real.sqrt (midpointStep n j) /
      (midpointLeft n j - (midpointLeft n i + midpointStep n i)) ≤
        2 / ((j.val : ℝ) - i.val) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi : (i.val : ℝ) + 2 ≤ j.val := by exact_mod_cast (show i.val + 2 ≤ j.val by omega)
  have hd : 0 < (j.val : ℝ) - i.val := by linarith
  have hprod : Real.sqrt (midpointStep n i) * Real.sqrt (midpointStep n j) ≤ 1 / n := by
    calc
      _ ≤ Real.sqrt (1 / (n : ℝ)) * Real.sqrt (1 / (n : ℝ)) :=
        mul_le_mul (Real.sqrt_le_sqrt (midpointStep_le n i))
          (Real.sqrt_le_sqrt (midpointStep_le n j)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 1 / n := by rw [← sq, Real.sq_sqrt (by positivity)]
  rw [midpoint_gap_formula n i j (by exact show i.val < j.val by omega)]
  have hgap : ((j.val : ℝ) - i.val) / (2 * n) ≤ ((j.val : ℝ) - i.val - 1) / n := by
    apply (div_le_div_iff₀ (by positivity) hn).mpr
    nlinarith
  calc
    _ ≤ (1 / (n : ℝ)) / (((j.val : ℝ) - i.val) / (2 * n)) :=
      div_le_div₀ (by positivity) hprod (by positivity) hgap
    _ = _ := by field_simp

theorem midpointFrozen_separated_uniform_bound (lo hi : ℝ) (hlo : 0 < lo) (hhi : hi < 1)
    (hlohi : lo ≤ hi) :
    ∃ K ≥ 0, ∀ n : ℕ, ∀ i j : Fin n, ∀ h k : Ioo (0 : ℝ) 1, ∀ a : ℝ,
      i.val + 1 < j.val → (h : ℝ) ∈ Icc lo hi → (k : ℝ) ∈ Icc lo hi →
      0 ≤ a → |(h : ℝ) - 1 / 2| ≤ a → |(k : ℝ) - 1 / 2| ≤ a →
      a * Real.log (2 * (n : ℝ)) ≤ 1 →
      |⟪frozenIncrementFeature h (midpointLeft n i) (midpointStep n i),
        frozenIncrementFeature k (midpointLeft n j) (midpointStep n j)⟫| ≤
        K * a / ((j.val : ℝ) - i.val) := by
  obtain ⟨C, hC, hc⟩ := harmonizableCovCoeff_uniform_bound lo hi hlo hhi hlohi
  refine ⟨8 * C * Real.exp 2, by positivity, ?_⟩
  intro n i j h k a hij hh hk ha hha hka hsmall
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hiR : (i.val : ℝ) + 2 ≤ j.val := by exact_mod_cast (show i.val + 2 ≤ j.val by omega)
  have hgap : midpointLeft n i + midpointStep n i < midpointLeft n j := by
    have he := midpoint_gap_formula n i j (by exact show i.val < j.val by omega)
    have hd : 0 < ((j.val : ℝ) - i.val - 1) / n := div_pos (by linarith) hn
    linarith
  have hb := frozenIncrementFeature_separated_uniform_bound h k _ _ _ _ a
    (Real.log (2 * (n : ℝ))) C (midpointStep_pos n i) (midpointStep_pos n j) hgap ha hC
    (hc h k hh hk) hha hka (midpoint_gap_log_bound n i j hij) hsmall
  have hm := mul_le_mul_of_nonneg_left (midpoint_sqrt_gap_ratio_bound n i j hij)
    (show 0 ≤ (4 * C * Real.exp 2) * a by positivity)
  exact hb.trans (hm.trans_eq (by ring))

theorem frozenIncrementFeature_adjacent_scaled_inner (h k : Ioo (0 : ℝ) 1)
    (t r s τ : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < τ) :
    ⟪frozenIncrementFeature h t (r * τ), frozenIncrementFeature k (t + r * τ) (s * τ)⟫ =
      (harmonizableCovCoeff h k / (Real.sqrt r * Real.sqrt s)) * τ ^ ((h : ℝ) + k - 1) *
        ((r + s) ^ ((h : ℝ) + k) - r ^ ((h : ℝ) + k) - s ^ ((h : ℝ) + k)) := by
  have hp : (h : ℝ) + k ≠ 0 := ne_of_gt (by linarith [h.property.1, k.property.1])
  rw [frozenIncrementFeature_inner_rectangle h k t (r * τ) (t + r * τ) (s * τ)
    (mul_pos hr ht) (mul_pos hs ht) le_rfl]
  rw [show t + r * τ + s * τ - t = (r + s) * τ by ring,
    show t + r * τ + s * τ - (t + r * τ) = s * τ by ring,
    show t + r * τ - t = r * τ by ring, sub_self, Real.zero_rpow hp]
  rw [Real.mul_rpow (by linarith : 0 ≤ r + s) ht.le, Real.mul_rpow hs.le ht.le,
    Real.mul_rpow hr.le ht.le, Real.sqrt_mul hr.le, Real.sqrt_mul hs.le,
    Real.rpow_sub ht, Real.rpow_one]
  have hτ := Real.sq_sqrt ht.le
  have hτ0 := (Real.sqrt_pos.mpr ht).ne'
  have hr0 := (Real.sqrt_pos.mpr hr).ne'
  have hs0 := (Real.sqrt_pos.mpr hs).ne'
  field_simp
  rw [hτ]
  ring

theorem frozenIncrementFeature_adjacent_scaled_uniform (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    ∃ K ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, ∀ t τ a L : ℝ,
      (h : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) → (k : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      0 < τ → 0 ≤ a → |(h : ℝ) - 1 / 2| ≤ a → |(k : ℝ) - 1 / 2| ≤ a →
      |Real.log τ| ≤ L → a * L ≤ 1 →
      |⟪frozenIncrementFeature h t (r * τ), frozenIncrementFeature k (t + r * τ) (s * τ)⟫| ≤ K * a := by
  obtain ⟨C, hC, hc⟩ := harmonizableCovCoeff_uniform_bound (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨D, hD, hd⟩ := adjacent_power_shape_bound r s (1 / 2) (3 / 2) hr hs (by norm_num) (by norm_num)
  refine ⟨2 * (C / (Real.sqrt r * Real.sqrt s)) * Real.exp 2 * D, by positivity, ?_⟩
  intro h k t τ a L hh hk hτ ha hha hka hlog hsmall
  have hp := hurst_sum_deviation h k a hha hka
  have hprod := mul_le_mul hp hlog (abs_nonneg _) (show 0 ≤ 2 * a by positivity)
  have hpow := rpow_le_exp_of_log_bound τ ((h : ℝ) + k - 1) 2 hτ (by nlinarith)
  have hshape := hd ((h : ℝ) + k) (by constructor <;> linarith [hh.1, hh.2, hk.1, hk.2])
  have hshape' := hshape.trans (mul_le_mul_of_nonneg_left hp hD)
  have hcoef := div_le_div_of_nonneg_right (hc h k hh hk)
    (mul_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg s))
  have hcoef0 : 0 ≤ harmonizableCovCoeff h k / (Real.sqrt r * Real.sqrt s) :=
    div_nonneg (harmonizableCovCoeff_nonneg h k) (by positivity)
  rw [frozenIncrementFeature_adjacent_scaled_inner h k t r s τ hr hs hτ, abs_mul, abs_mul,
    abs_of_nonneg hcoef0, abs_of_nonneg (Real.rpow_nonneg hτ.le _)]
  have hm := mul_le_mul hcoef hpow (Real.rpow_nonneg hτ.le _) (by positivity)
  have hm' := mul_le_mul hm hshape' (abs_nonneg _) (by positivity)
  exact hm'.trans_eq (by ring)

theorem midpointFrozen_adjacent_uniform_bound :
    ∃ K ≥ 0, ∀ n : ℕ, ∀ i j : Fin n, ∀ h k : Ioo (0 : ℝ) 1, ∀ a : ℝ,
      j.val = i.val + 1 → (h : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      (k : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      0 ≤ a → |(h : ℝ) - 1 / 2| ≤ a → |(k : ℝ) - 1 / 2| ≤ a →
      a * Real.log (2 * (n : ℝ)) ≤ 1 →
      |⟪frozenIncrementFeature h (midpointLeft n i) (midpointStep n i),
        frozenIncrementFeature k (midpointLeft n j) (midpointStep n j)⟫| ≤ K * a := by
  obtain ⟨K₁, hK₁, h₁⟩ := frozenIncrementFeature_adjacent_scaled_uniform 1 1 (by norm_num) (by norm_num)
  obtain ⟨K₂, hK₂, h₂⟩ := frozenIncrementFeature_adjacent_scaled_uniform (1 / 2) 1 (by norm_num) (by norm_num)
  refine ⟨max K₁ K₂, hK₁.trans (le_max_left _ _), ?_⟩
  intro n i j h k a hij hh hk ha hha hka hsmall
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hj0 : j.val ≠ 0 := by omega
  have hjstep : midpointStep n j = 1 / n := by simp [midpointStep, hj0]
  have hlog : |Real.log (1 / (n : ℝ))| ≤ Real.log (2 * n) := by
    rw [one_div, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg hn1)]
    exact Real.log_le_log hn (by linarith)
  have hleft : midpointLeft n j = midpointLeft n i + midpointStep n i := by
    have he := midpoint_gap_formula n i j (by exact show i.val < j.val by omega)
    have hc : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij
    rw [hc] at he
    have hz : ((i.val : ℝ) + 1 - i.val - 1) / n = 0 := by ring
    rw [hz] at he
    exact sub_eq_zero.mp he
  rw [hleft, hjstep]
  by_cases hi0 : i.val = 0
  · have hist : midpointStep n i = (1 / 2 : ℝ) * (1 / n) := by
      simp only [midpointStep, if_pos hi0]
      ring
    rw [hist]
    have he := h₂ h k (midpointLeft n i) (1 / n) a (Real.log (2 * n))
      hh hk (by positivity) ha hha hka hlog hsmall
    simp only [one_mul] at he
    exact he.trans (mul_le_mul_of_nonneg_right (le_max_right K₁ K₂) ha)
  · have hist : midpointStep n i = 1 / n := by simp [midpointStep, hi0]
    rw [hist]
    have he := h₁ h k (midpointLeft n i) (1 / n) a (Real.log (2 * n))
      hh hk (by positivity) ha hha hka hlog hsmall
    simp only [one_mul] at he
    exact he.trans (mul_le_mul_of_nonneg_right (le_max_left K₁ K₂) ha)

/-- All distinct midpoint intervals, including the first half-step and adjacent pairs. -/
theorem midpointFrozen_offdiagonal_uniform_bound :
    ∃ K ≥ 0, ∀ n : ℕ, ∀ i j : Fin n, ∀ h k : Ioo (0 : ℝ) 1, ∀ a : ℝ,
      i ≠ j → (h : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      (k : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      0 ≤ a → |(h : ℝ) - 1 / 2| ≤ a → |(k : ℝ) - 1 / 2| ≤ a →
      a * Real.log (2 * (n : ℝ)) ≤ 1 →
      |⟪frozenIncrementFeature h (midpointLeft n i) (midpointStep n i),
        frozenIncrementFeature k (midpointLeft n j) (midpointStep n j)⟫| ≤
        K * a / |(j.val : ℝ) - i.val| := by
  obtain ⟨K₁, hK₁, h₁⟩ := midpointFrozen_adjacent_uniform_bound
  obtain ⟨K₂, hK₂, h₂⟩ := midpointFrozen_separated_uniform_bound (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max K₁ K₂, hK₁.trans (le_max_left _ _), ?_⟩
  have hforward : ∀ n : ℕ, ∀ i j : Fin n, ∀ h k : Ioo (0 : ℝ) 1, ∀ a : ℝ,
      i < j → (h : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      (k : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      0 ≤ a → |(h : ℝ) - 1 / 2| ≤ a → |(k : ℝ) - 1 / 2| ≤ a →
      a * Real.log (2 * (n : ℝ)) ≤ 1 →
      |⟪frozenIncrementFeature h (midpointLeft n i) (midpointStep n i),
        frozenIncrementFeature k (midpointLeft n j) (midpointStep n j)⟫| ≤
        max K₁ K₂ * a / |(j.val : ℝ) - i.val| := by
    intro n i j h k a hij hh hk ha hha hka hsmall
    have hijN : i.val < j.val := hij
    have hd : (0 : ℝ) < j.val - i.val := sub_pos.mpr (by exact_mod_cast hijN)
    rw [abs_of_pos hd]
    by_cases hadj : j.val = i.val + 1
    · have hc : (j.val : ℝ) - i.val = 1 := by
        have he : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hadj
        linarith
      rw [hc, div_one]
      exact (h₁ n i j h k a hadj hh hk ha hha hka hsmall).trans
        (mul_le_mul_of_nonneg_right (le_max_left K₁ K₂) ha)
    · exact (h₂ n i j h k a (by omega) hh hk ha hha hka hsmall).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right K₁ K₂) ha) hd.le)
  intro n i j h k a hij hh hk ha hha hka hsmall
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hforward n i j h k a hlt hh hk ha hha hka hsmall
  · rw [real_inner_comm, abs_sub_comm (j.val : ℝ) i.val]
    exact hforward n j i k h a hgt hk hh ha hka hha hsmall

end Hurst
