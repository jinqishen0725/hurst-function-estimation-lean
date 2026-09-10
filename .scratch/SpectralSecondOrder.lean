import Hurst.SpectralMajorant
import Mathlib.Topology.MetricSpace.Pseudo.Real

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def rawHarmonizableSlope (h t x : ℝ) : ℂ := -Real.log |x| • rawHarmonizable h t x

theorem rawHarmonizableSlope_memLp (h t : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    MemLp (rawHarmonizableSlope h t) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by exact (((Real.measurable_log.comp measurable_abs).neg).smul (rawHarmonizable_measurable h t)).aestronglyMeasurable)).mpr
  have hi := rawHarmonizable_log_weight_integrable h t hh hh1 2
  simpa only [rawHarmonizableSlope, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs] using hi

def rawHarmonizableSlopeFeature (h : Ioo (0 : ℝ) 1) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (rawHarmonizableSlope_memLp h t h.property.1 h.property.2).toLp _

theorem rawHarmonizableSlopeFeature_ae (h : Ioo (0 : ℝ) 1) (t : ℝ) :
    rawHarmonizableSlopeFeature h t =ᵐ[volume] rawHarmonizableSlope h t := MemLp.coeFn_toLp _

theorem spectralLogSquareEnvelope_memLp (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    MemLp (fun x => |Real.log (|x|)| ^ 2 * spectralEnvelope a b x) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by unfold spectralEnvelope spectralMajorant; fun_prop)).mpr
  have hi := spectralMajorant_log_weight_integrable a b ha hb 4
  have he : (fun x => (|Real.log (|x|)| ^ 2 * spectralEnvelope a b x) ^ 2) =
      (fun x => Real.log |x| ^ 4 * spectralMajorant a b x) := by
    funext x
    rw [mul_pow, sq_abs, spectralEnvelope, Real.sq_sqrt (spectralMajorant_nonneg a b x)]
    ring
  rwa [he]

/-- A quadratic parameter remainder is established pointwise before passing to L2. -/
theorem rawHarmonizable_quadratic_remainder (a b h k t x : ℝ) (ha : 0 < a) (hb : b < 1)
    (hh : h ∈ Icc a b) (hk : k ∈ Icc a b) (ht : |t| ≤ 1) (hx : x ≠ 0) :
    ‖rawHarmonizable k t x - rawHarmonizable h t x - (k - h) • rawHarmonizableSlope h t x‖ ≤
      (2 * |Real.log (|x|)| ^ 2 * spectralEnvelope a b x) * |k - h| ^ 2 := by
  have hsub : uIcc h k ⊆ Icc a b := uIcc_subset_Icc hh hk
  have hderiv : ∀ u ∈ uIcc h k,
      HasDerivAt (fun v => rawHarmonizable v t x - rawHarmonizable h t x - (v - h) • rawHarmonizableSlope h t x)
        (-Real.log |x| • (rawHarmonizable u t x - rawHarmonizable h t x)) u := by
    intro u hu
    have hd := ((rawHarmonizable_hasDerivAt u t x hx).sub_const (rawHarmonizable h t x)).sub
      (((hasDerivAt_id u).sub_const h).smul_const (rawHarmonizableSlope h t x))
    convert! hd using 1
    simp only [one_smul, rawHarmonizableSlope, smul_sub]
  have hbound : ∀ u ∈ uIcc h k,
      ‖-Real.log |x| • (rawHarmonizable u t x - rawHarmonizable h t x)‖ ≤
        (2 * |Real.log (|x|)| ^ 2 * spectralEnvelope a b x) * |k - h| := by
    intro u hu
    have hp := rawHarmonizable_parameter_bound a b u h t x ha hb (hsub hu) hh ht hx
    have hdist : |u - h| ≤ |k - h| := abs_sub_left_of_mem_uIcc hu
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    have he := mul_le_mul_of_nonneg_left hp (abs_nonneg (Real.log |x|))
    have hf := mul_le_mul_of_nonneg_left hdist
      (show 0 ≤ 2 * |Real.log (|x|)| ^ 2 * spectralEnvelope a b x by unfold spectralEnvelope; positivity)
    nlinarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hderiv u hu).hasDerivWithinAt) hbound (convex_uIcc h k) left_mem_uIcc right_mem_uIcc
  simp only [sub_self, zero_smul, sub_zero, Real.norm_eq_abs] at hm
  exact hm.trans_eq (by ring)

/-- Actual Hilbert-space quadratic remainder with one parameter/time-uniform constant. -/
theorem rawHarmonizableFeature_uniform_quadratic_remainder (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ t : ℝ, |t| ≤ 1 →
      ‖rawHarmonizableFeature k t - rawHarmonizableFeature h t -
        ((k : ℝ) - h) • rawHarmonizableSlopeFeature h t‖ ≤ C * |(k : ℝ) - h| ^ 2 := by
  let e : Lp ℝ 2 (volume : Measure ℝ) := (spectralLogSquareEnvelope_memLp a b ha hb).toLp _
  have he : e =ᵐ[volume] (fun x => |Real.log (|x|)| ^ 2 * spectralEnvelope a b x) := MemLp.coeFn_toLp _
  refine ⟨2 * ‖e‖, by positivity, ?_⟩
  intro h k hh hk t ht
  have hn : ‖rawHarmonizableFeature k t - rawHarmonizableFeature h t -
        ((k : ℝ) - h) • rawHarmonizableSlopeFeature h t‖ ≤ (2 * |(k : ℝ) - h| ^ 2) * ‖e‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul (g := e)
    filter_upwards [Lp.coeFn_sub (rawHarmonizableFeature k t - rawHarmonizableFeature h t)
        (((k : ℝ) - h) • rawHarmonizableSlopeFeature h t),
      Lp.coeFn_sub (rawHarmonizableFeature k t) (rawHarmonizableFeature h t),
      Lp.coeFn_smul ((k : ℝ) - h) (rawHarmonizableSlopeFeature h t),
      rawHarmonizableFeature_ae k t, rawHarmonizableFeature_ae h t,
      rawHarmonizableSlopeFeature_ae h t, he, volume.ae_ne (0 : ℝ)] with x hsub hsub' hsm hkx hhx hsx hex hx0
    rw [hsub, Pi.sub_apply, hsub', Pi.sub_apply, hsm, Pi.smul_apply, hkx, hhx, hsx, hex,
      Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ |Real.log (|x|)| ^ 2 * spectralEnvelope a b x by unfold spectralEnvelope; positivity)]
    have hp := rawHarmonizable_quadratic_remainder a b h k t x ha hb hh hk ht hx0
    exact hp.trans_eq (by ring)
  exact hn.trans_eq (by ring)

/-- Uniform norm of the actual parameter slope on a compact Hurst range. -/
theorem rawHarmonizableSlopeFeature_uniform_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → ∀ t : ℝ, |t| ≤ 1 →
      ‖rawHarmonizableSlopeFeature h t‖ ≤ C := by
  let e : Lp ℝ 2 (volume : Measure ℝ) := (spectralLogEnvelope_memLp a b ha hb).toLp _
  have he : e =ᵐ[volume] (fun x => |Real.log (|x|)| * spectralEnvelope a b x) := MemLp.coeFn_toLp _
  refine ⟨2 * ‖e‖, by positivity, ?_⟩
  intro h hh t ht
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := e)
  filter_upwards [rawHarmonizableSlopeFeature_ae h t, he] with x hx hex
  rw [hx, hex, rawHarmonizableSlope, norm_smul, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ |Real.log (|x|)| * spectralEnvelope a b x by unfold spectralEnvelope; positivity)]
  have hraw := rawHarmonizable_norm_uniform a b h t x ha hb hh.1 hh.2 ht
  have he := mul_le_mul_of_nonneg_left hraw (abs_nonneg (Real.log |x|))
  nlinarith

end Hurst
