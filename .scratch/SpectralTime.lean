import Hurst.SpectralSecondOrder

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem rawHarmonizable_time_shift (h t l x : ℝ) :
    rawHarmonizable h (t + l) x - rawHarmonizable h t x =
      Complex.exp (Complex.I * (t * x : ℝ)) * rawHarmonizable h l x := by
  unfold rawHarmonizable
  rw [add_mul, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem rawHarmonizable_time_shift_norm (h t l x : ℝ) :
    ‖rawHarmonizable h (t + l) x - rawHarmonizable h t x‖ = ‖rawHarmonizable h l x‖ := by
  rw [rawHarmonizable_time_shift, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

theorem rawHarmonizableSlope_time_shift_norm (h t l x : ℝ) :
    ‖rawHarmonizableSlope h (t + l) x - rawHarmonizableSlope h t x‖ = ‖rawHarmonizableSlope h l x‖ := by
  simp only [rawHarmonizableSlope, ← smul_sub, norm_smul, rawHarmonizable_time_shift_norm]

theorem rawHarmonizable_time_scale (h l x : ℝ) (hl : 0 < l) :
    rawHarmonizable h l x = l ^ (h + 1 / 2) • rawHarmonizable h 1 (l * x) := by
  unfold rawHarmonizable
  rw [one_mul, abs_mul, abs_of_pos hl, Real.mul_rpow hl.le (abs_nonneg x)]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  have hp : ((l ^ (h + 1 / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hl _).ne'
  rw [← mul_div_assoc, mul_div_mul_left _ _ hp]

theorem rawHarmonizableSlope_time_scale (h l x : ℝ) (hl : 0 < l) (hx : x ≠ 0) :
    rawHarmonizableSlope h l x = l ^ (h + 1 / 2) •
      (rawHarmonizableSlope h 1 (l * x) + Real.log l • rawHarmonizable h 1 (l * x)) := by
  unfold rawHarmonizableSlope
  rw [rawHarmonizable_time_scale h l x hl, abs_mul, abs_of_pos hl, Real.log_mul hl.ne' (abs_ne_zero.mpr hx)]
  module

theorem lp_two_norm_sq_integral (v : Lp ℂ 2 (volume : Measure ℝ)) (f : ℝ → ℂ)
    (hv : v =ᵐ[volume] f) : ‖v‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem rawHarmonizableSlopeFeature_time_shift_norm (h : Ioo (0 : ℝ) 1) (t l : ℝ) :
    ‖rawHarmonizableSlopeFeature h (t + l) - rawHarmonizableSlopeFeature h t‖ =
      ‖rawHarmonizableSlopeFeature h l‖ := by
  have he : rawHarmonizableSlopeFeature h (t + l) - rawHarmonizableSlopeFeature h t =ᵐ[volume]
      fun x => rawHarmonizableSlope h (t + l) x - rawHarmonizableSlope h t x := by
    filter_upwards [Lp.coeFn_sub (rawHarmonizableSlopeFeature h (t + l)) (rawHarmonizableSlopeFeature h t),
      rawHarmonizableSlopeFeature_ae h (t + l), rawHarmonizableSlopeFeature_ae h t] with x hx hy hz
    rw [hx, Pi.sub_apply, hy, hz]
  have hs := lp_two_norm_sq_integral _ _ he
  simp_rw [rawHarmonizableSlope_time_shift_norm] at hs
  rw [← lp_two_norm_sq_integral _ _ (rawHarmonizableSlopeFeature_ae h l)] at hs
  nlinarith [norm_nonneg (rawHarmonizableSlopeFeature h (t + l) - rawHarmonizableSlopeFeature h t),
    norm_nonneg (rawHarmonizableSlopeFeature h l)]

/-- Exact scaling of the parameter slope, including the logarithmic correction. -/
theorem rawHarmonizableSlopeFeature_time_scale_norm (h : Ioo (0 : ℝ) 1) (l : ℝ) (hl : 0 < l) :
    ‖rawHarmonizableSlopeFeature h l‖ = l ^ (h : ℝ) *
      ‖rawHarmonizableSlopeFeature h 1 + Real.log l • rawHarmonizableFeature h 1‖ := by
  let v := rawHarmonizableSlopeFeature h 1 + Real.log l • rawHarmonizableFeature h 1
  let g := fun x => rawHarmonizableSlope h 1 x + Real.log l • rawHarmonizable h 1 x
  have hv : v =ᵐ[volume] g := by
    filter_upwards [Lp.coeFn_add (rawHarmonizableSlopeFeature h 1) (Real.log l • rawHarmonizableFeature h 1),
      Lp.coeFn_smul (Real.log l) (rawHarmonizableFeature h 1),
      rawHarmonizableSlopeFeature_ae h 1, rawHarmonizableFeature_ae h 1] with x hx hy hz hw
    change (rawHarmonizableSlopeFeature h 1 + Real.log l • rawHarmonizableFeature h 1) x = _
    rw [hx, Pi.add_apply, hy, Pi.smul_apply, hz, hw]
  have hs : ‖rawHarmonizableSlopeFeature h l‖ ^ 2 =
      (l ^ (h : ℝ)) ^ 2 * ‖v‖ ^ 2 := by
    rw [lp_two_norm_sq_integral _ _ (rawHarmonizableSlopeFeature_ae h l), lp_two_norm_sq_integral v g hv]
    calc
      _ = ∫ x, (l ^ ((h : ℝ) + 1 / 2)) ^ 2 * ‖g (l * x)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
        rw [rawHarmonizableSlope_time_scale h l x hl hx, norm_smul, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hl _), mul_pow]
      _ = (l ^ ((h : ℝ) + 1 / 2)) ^ 2 * (|l⁻¹| * ∫ x, ‖g x‖ ^ 2) := by
        rw [integral_const_mul]
        rw [Measure.integral_comp_mul_left (fun x => ‖g x‖ ^ 2) l, smul_eq_mul]
      _ = _ := by
        rw [abs_of_pos (inv_pos.mpr hl), ← mul_assoc]
        congr 1
        rw [← Real.rpow_natCast (l ^ ((h : ℝ) + 1 / 2)) 2,
          ← Real.rpow_mul hl.le, ← div_eq_mul_inv, ← Real.rpow_sub_one hl.ne',
          ← Real.rpow_natCast (l ^ (h : ℝ)) 2, ← Real.rpow_mul hl.le]
        congr 1
        ring
  have hp := Real.rpow_pos_of_pos hl (h : ℝ)
  change ‖rawHarmonizableSlopeFeature h l‖ = l ^ (h : ℝ) * ‖v‖
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hp.le (norm_nonneg v))).mp
  simpa only [mul_pow] using hs

theorem rawHarmonizableSlopeFeature_time_increment_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → ∀ t l : ℝ, 0 < l →
      ‖rawHarmonizableSlopeFeature h (t + l) - rawHarmonizableSlopeFeature h t‖ ≤
        C * l ^ (h : ℝ) * (1 + |Real.log l|) := by
  obtain ⟨U, hU, L, hL, hu, hLip⟩ := rawHarmonizableFeature_uniform_control a b ha hb
  obtain ⟨D, hD, hd⟩ := rawHarmonizableSlopeFeature_uniform_bound a b ha hb
  refine ⟨D + U, by positivity, ?_⟩
  intro h hh t l hl
  rw [rawHarmonizableSlopeFeature_time_shift_norm, rawHarmonizableSlopeFeature_time_scale_norm h l hl]
  have he := (norm_add_le (rawHarmonizableSlopeFeature h 1) (Real.log l • rawHarmonizableFeature h 1)).trans
    (add_le_add (hd h hh 1 (by norm_num)) (show ‖Real.log l • rawHarmonizableFeature h 1‖ ≤ |Real.log l| * U by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hu h hh 1 (by norm_num)) (abs_nonneg _)))
  have he' : ‖rawHarmonizableSlopeFeature h 1 + Real.log l • rawHarmonizableFeature h 1‖ ≤
      (D + U) * (1 + |Real.log l|) := by
    nlinarith [mul_nonneg hD (abs_nonneg (Real.log l))]
  exact (mul_le_mul_of_nonneg_left he' (Real.rpow_nonneg hl.le _)).trans_eq (by ring)

end Hurst
