import Hurst.Harmonizable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Topology.Order.Compact

/-! Parameter regularity and uniform bounds for the actual spectral integrals. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal RealInnerProductSpace
namespace Hurst

/-- All logarithmic weights created by parameter differentiation are integrable. -/
theorem rawHarmonizable_log_weight_integrable (h t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (k : ℕ) : Integrable (fun x => (Real.log |x|) ^ k * ‖rawHarmonizable h t x‖ ^ 2) volume := by
  have hm : AEStronglyMeasurable
      (fun x => (Real.log |x|) ^ k * ‖rawHarmonizable h t x‖ ^ 2) volume := by
    apply Measurable.aestronglyMeasurable
    exact ((Real.measurable_log.comp measurable_abs).pow_const k).mul
      ((rawHarmonizable_measurable h t).norm.pow_const 2)
  have hnear : (fun x => ‖rawHarmonizable h t x‖ ^ 2) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (1 - 2 * h)) := by
    apply IsBigO.of_bound (t ^ 2)
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [Real.norm_eq_abs, abs_sq, abs_of_nonneg (Real.rpow_nonneg hx.le _)] using
      rawHarmonizable_norm_sq_near h t x hx
  have hfar : (fun x => ‖rawHarmonizable h t x‖ ^ 2) =O[atTop]
      (fun x : ℝ => x ^ (-1 - 2 * h)) := by
    apply IsBigO.of_bound 4
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa only [Real.norm_eq_abs, abs_sq, abs_of_nonneg (Real.rpow_nonneg hx.le _)] using
      rawHarmonizable_norm_sq_far h t x hx
  have hlnear : (fun x : ℝ => (Real.log |x|) ^ k) =O[𝓝[>] 0]
      (fun x => x ^ (h - 1)) := by
    apply IsBigO.of_norm_left
    simpa only [Real.rpow_natCast, norm_pow, Real.norm_eq_abs, Real.log_abs] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ) (by linarith : h - 1 < 0)).isBigO
  have hlfar : (fun x : ℝ => (Real.log |x|) ^ k) =O[atTop]
      (fun x => x ^ h) := by
    simpa only [Real.rpow_natCast, Real.log_abs] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) hh).isBigO
  have hpos : IntegrableOn
      (fun x => (Real.log |x|) ^ k * ‖rawHarmonizable h t x‖ ^ 2) (Ioi 0) := by
    rw [integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin]
    refine ⟨?_, ?_, ?_⟩
    · have hb : (fun x => (Real.log |x|) ^ k * ‖rawHarmonizable h t x‖ ^ 2) =O[atTop]
          (fun x : ℝ => x ^ (-1 - h)) := by
        apply (hlfar.mul hfar).congr' (EventuallyEq.refl _ _) ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_add hx]
        congr 1
        ring
      apply hb.integrableAtFilter hm.stronglyMeasurableAtFilter
      exact ⟨Ioi 1, Ioi_mem_atTop 1,
        integrableOn_Ioi_rpow_of_lt (by linarith : -1 - h < -1) (by norm_num)⟩
    · have hb : (fun x => (Real.log |x|) ^ k * ‖rawHarmonizable h t x‖ ^ 2) =O[𝓝[>] 0]
          (fun x : ℝ => x ^ (-h)) := by
        apply (hlnear.mul hnear).congr' (EventuallyEq.refl _ _) ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [← Real.rpow_add hx]
        congr 1
        ring
      apply hb.integrableAtFilter hm.stronglyMeasurableAtFilter
      exact ⟨Ioo 0 1, Ioo_mem_nhdsGT (by norm_num),
        (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr
          (by linarith : -1 < -h)⟩
    · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hc : ContinuousAt (rawHarmonizable h t) x := by
        unfold rawHarmonizable
        apply ContinuousAt.div (by fun_prop)
          (Complex.continuous_ofReal.continuousAt.comp
            (continuous_abs.continuousAt.rpow_const (Or.inl (abs_ne_zero.mpr hx0))))
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr hx0) _))
      exact (((Real.continuousAt_log (abs_ne_zero.mpr hx0)).comp continuous_abs.continuousAt).pow k
        |>.mul (hc.norm.pow 2)).continuousWithinAt
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, rawHarmonizable_norm_sq_even, abs_neg, neg_preimage,
    neg_Iio, neg_zero] using hpos

theorem spectralCosineDensity_log_weight_integrable (h t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (k : ℕ) : Integrable (fun x => (Real.log |x|) ^ k * spectralCosineDensity h t x) volume := by
  apply ((rawHarmonizable_log_weight_integrable h t hh hh1 k).const_mul (1 / 2 : ℝ)).congr
  filter_upwards [] with x
  rw [rawHarmonizable_norm_sq_density]
  ring

/-- A single integrable pair of endpoint densities controls the whole parameter interval. -/
theorem spectralCosineDensity_le_endpoints (a b h t x : ℝ) (ha : a ≤ h) (hb : h ≤ b) :
    spectralCosineDensity h t x ≤ spectralCosineDensity a t x + spectralCosineDensity b t x := by
  by_cases hx : x = 0
  · subst x
    simp [spectralCosineDensity]
  have hx0 : 0 < |x| := abs_pos.mpr hx
  have hn : 0 ≤ 1 - Real.cos (t * x) := sub_nonneg.mpr (Real.cos_le_one _)
  rcases le_total |x| 1 with hx1 | hx1
  · have hr := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith : 2 * h + 1 ≤ 2 * b + 1)
    have hd : spectralCosineDensity h t x ≤ spectralCosineDensity b t x :=
      div_le_div_of_nonneg_left hn (Real.rpow_pos_of_pos hx0 _) hr
    exact hd.trans (le_add_of_nonneg_left (spectralCosineDensity_nonneg a t x))
  · have hr := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : 2 * a + 1 ≤ 2 * h + 1)
    have hd : spectralCosineDensity h t x ≤ spectralCosineDensity a t x :=
      div_le_div_of_nonneg_left hn (Real.rpow_pos_of_pos hx0 _) hr
    exact hd.trans (le_add_of_nonneg_right (spectralCosineDensity_nonneg b t x))

theorem spectralCosineDensity_hasDerivAt (h t x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun u => spectralCosineDensity u t x)
      (-2 * Real.log |x| * spectralCosineDensity h t x) h := by
  have hp := ((hasDerivAt_id h).const_mul 2 |>.add_const 1).const_rpow (abs_pos.mpr hx)
  simp only [id_eq, mul_one] at hp
  have hp0 : |x| ^ (2 * h + 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr hx) _)
  convert! (hasDerivAt_const h (1 - Real.cos (t * x))).div hp hp0 using 1
  unfold spectralCosineDensity
  field_simp
  ring

/-- Differentiation under the full real spectral integral with a proved dominating function. -/
theorem spectralCosineDensity_integral_hasDerivAt (h t : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (fun u => ∫ x, spectralCosineDensity u t x)
      (∫ x, -2 * Real.log |x| * spectralCosineDensity h t x) h := by
  let a := h / 2
  let b := (h + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have han : a < h := by dsimp [a]; linarith
  have hbn : h < b := by dsimp [b]; linarith
  let bound := fun x => 2 * (|Real.log |x| * spectralCosineDensity a t x| +
    |Real.log |x| * spectralCosineDensity b t x|)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Icc a b)
    (F' := fun u x => -2 * Real.log |x| * spectralCosineDensity u t x)
    (bound := bound) (Icc_mem_nhds han hbn) ?_
    (spectralCosineDensity_integrable h t hh hh1) ?_ ?_ ?_ ?_).2
  · filter_upwards [] with u
    apply Measurable.aestronglyMeasurable
    unfold spectralCosineDensity
    fun_prop
  · unfold spectralCosineDensity
    fun_prop
  · filter_upwards [] with x
    intro u hu
    have hd := spectralCosineDensity_le_endpoints a b u t x hu.1 hu.2
    have hn := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (abs_nonneg (Real.log |x|)))
    simpa only [bound, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (spectralCosineDensity_nonneg u t x),
      abs_of_nonneg (spectralCosineDensity_nonneg a t x),
      abs_of_nonneg (spectralCosineDensity_nonneg b t x), mul_add, mul_assoc] using hn
  · have hia := (spectralCosineDensity_log_weight_integrable a t ha ha1 1).abs
    have hib := (spectralCosineDensity_log_weight_integrable b t hb hb1 1).abs
    simpa only [bound, pow_one, Pi.add_apply] using! (hia.add hib).const_mul 2
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    intro u hu
    exact spectralCosineDensity_hasDerivAt u t x hx

theorem harmonizableD_differentiableAt (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    DifferentiableAt ℝ harmonizableD h := by
  exact (spectralCosineDensity_integral_hasDerivAt h 1 hh hh1).differentiableAt.sqrt
    (ne_of_gt (spectralCosineDensity_integral_pos h hh hh1))

theorem harmonizableD_continuousOn : ContinuousOn harmonizableD (Ioo 0 1) := by
  intro h hh
  exact (harmonizableD_differentiableAt h hh.1 hh.2).continuousAt.continuousWithinAt

theorem harmonizableD_uniform_pos (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ c > 0, ∀ h ∈ Icc a b, c ≤ harmonizableD h := by
  have hc : ContinuousOn harmonizableD (Icc a b) :=
    harmonizableD_continuousOn.mono (fun h hh => ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩)
  obtain ⟨h, hh, hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  exact ⟨harmonizableD h, harmonizableD_pos h (ha.trans_le hh.1) (hh.2.trans_lt hb), hm⟩

theorem spectralLogMoment_continuousOn (t : ℝ) (k : ℕ) :
    ContinuousOn (fun h => ∫ x, (Real.log |x|) ^ k * spectralCosineDensity h t x) (Ioo 0 1) := by
  intro h hh
  let a := h / 2
  let b := (h + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hh.1]
  have ha1 : a < 1 := by dsimp [a]; linarith [hh.2]
  have hb : 0 < b := by dsimp [b]; linarith [hh.1]
  have hb1 : b < 1 := by dsimp [b]; linarith [hh.2]
  have han : a < h := by dsimp [a]; linarith [hh.1]
  have hbn : h < b := by dsimp [b]; linarith [hh.2]
  let bound := fun x => |(Real.log |x|) ^ k * spectralCosineDensity a t x| +
    |(Real.log |x|) ^ k * spectralCosineDensity b t x|
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := bound)
  · filter_upwards [] with u
    apply Measurable.aestronglyMeasurable
    unfold spectralCosineDensity
    fun_prop
  · filter_upwards [Icc_mem_nhds han hbn] with u hu
    filter_upwards [] with x
    have hd := spectralCosineDensity_le_endpoints a b u t x hu.1 hu.2
    have hn := mul_le_mul_of_nonneg_left hd (abs_nonneg ((Real.log |x|) ^ k))
    simpa only [bound, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (spectralCosineDensity_nonneg u t x),
      abs_of_nonneg (spectralCosineDensity_nonneg a t x),
      abs_of_nonneg (spectralCosineDensity_nonneg b t x), mul_add] using hn
  · exact ((spectralCosineDensity_log_weight_integrable a t ha ha1 k).abs).add
      ((spectralCosineDensity_log_weight_integrable b t hb hb1 k).abs)
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    exact (spectralCosineDensity_hasDerivAt h t x hx).continuousAt.const_mul _

def harmonizableDSlope (h : ℝ) : ℝ :=
  -(∫ x, Real.log |x| * spectralCosineDensity h 1 x) / harmonizableD h

theorem harmonizableD_hasDerivAt (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt harmonizableD (harmonizableDSlope h) h := by
  have hi := (spectralCosineDensity_integral_hasDerivAt h 1 hh hh1).sqrt
    (ne_of_gt (spectralCosineDensity_integral_pos h hh hh1))
  convert! hi using 1
  change -(∫ x, Real.log |x| * spectralCosineDensity h 1 x) / harmonizableD h =
    (∫ x, -2 * Real.log |x| * spectralCosineDensity h 1 x) / (2 * harmonizableD h)
  simp_rw [mul_assoc (-2 : ℝ)]
  rw [integral_const_mul]
  ring

theorem harmonizableDSlope_continuousOn : ContinuousOn harmonizableDSlope (Ioo 0 1) := by
  have hc : ContinuousOn (fun h => ∫ x, Real.log |x| * spectralCosineDensity h 1 x) (Ioo 0 1) := by
    simpa only [pow_one] using spectralLogMoment_continuousOn 1 1
  exact hc.neg.div harmonizableD_continuousOn (fun h hh => (harmonizableD_pos h hh.1 hh.2).ne')

/-- A proved uniform parameter Lipschitz bound for the normalizer. -/
theorem harmonizableD_uniform_lipschitz (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h ∈ Icc a b, ∀ k ∈ Icc a b,
      |harmonizableD h - harmonizableD k| ≤ C * |h - k| := by
  have hc := harmonizableDSlope_continuousOn.norm.mono
    (show Icc a b ⊆ Ioo (0 : ℝ) 1 from fun h hh => ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩)
  obtain ⟨u, hu, hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  refine ⟨‖harmonizableDSlope u‖, norm_nonneg _, ?_⟩
  intro h hh k hk
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (harmonizableD_hasDerivAt x (ha.trans_le hx.1) (hx.2.trans_lt hb)).hasDerivWithinAt)
    (fun x hx => hm hx) (convex_Icc a b) hk hh
  simpa only [Real.norm_eq_abs] using hmvt

end Hurst
