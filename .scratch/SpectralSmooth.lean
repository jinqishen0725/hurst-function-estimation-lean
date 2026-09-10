import Hurst.SpectralRegularity
import Hurst.SpectralMajorant
import Hurst.CovarianceParameter
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Hurst

def spectralLogMoment (t : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  ∫ x, (Real.log |x|) ^ k * spectralCosineDensity h t x

theorem spectralLogMoment_hasDerivAt (t : ℝ) (k : ℕ) (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (spectralLogMoment t k) (-2 * spectralLogMoment t (k + 1) h) h := by
  let a := h / 2
  let b := (h + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hh.1]
  have ha1 : a < 1 := by dsimp [a]; linarith [hh.2]
  have hb : 0 < b := by dsimp [b]; linarith [hh.1]
  have hb1 : b < 1 := by dsimp [b]; linarith [hh.2]
  have han : a < h := by dsimp [a]; linarith [hh.1]
  have hbn : h < b := by dsimp [b]; linarith [hh.2]
  let bound := fun x => 2 * (|(Real.log |x|) ^ (k + 1) * spectralCosineDensity a t x| +
    |(Real.log |x|) ^ (k + 1) * spectralCosineDensity b t x|)
  have hd : HasDerivAt (spectralLogMoment t k)
      (∫ x, -2 * ((Real.log |x|) ^ (k + 1) * spectralCosineDensity h t x)) h := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Icc a b)
      (F' := fun u x => -2 * ((Real.log |x|) ^ (k + 1) * spectralCosineDensity u t x))
      (bound := bound) (Icc_mem_nhds han hbn) ?_
      (spectralCosineDensity_log_weight_integrable h t hh.1 hh.2 k) ?_ ?_ ?_ ?_).2
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
        (abs_nonneg ((Real.log |x|) ^ (k + 1))))
      simpa only [bound, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (spectralCosineDensity_nonneg u t x),
        abs_of_nonneg (spectralCosineDensity_nonneg a t x),
        abs_of_nonneg (spectralCosineDensity_nonneg b t x), mul_add, mul_assoc] using hn
    · exact (((spectralCosineDensity_log_weight_integrable a t ha ha1 (k + 1)).abs).add
        ((spectralCosineDensity_log_weight_integrable b t hb hb1 (k + 1)).abs)).const_mul 2
    · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
      intro u hu
      convert! (spectralCosineDensity_hasDerivAt u t x hx).const_mul ((Real.log |x|) ^ k) using 1
      rw [pow_succ]
      ring
  simpa only [integral_const_mul, spectralLogMoment] using hd

theorem spectralLogMoment_smooth (t : ℝ) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spectralLogMoment t k) (Ioo (0 : ℝ) 1) := by
  apply contDiffOn_infty.mpr
  intro n
  induction n generalizing k with
  | zero => exact contDiffOn_zero.mpr (spectralLogMoment_continuousOn t k)
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
    apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mpr
    refine ⟨fun h hh => (spectralLogMoment_hasDerivAt t k h hh).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    apply (contDiffOn_const.mul (ih (k + 1))).congr
    intro h hh
    exact (spectralLogMoment_hasDerivAt t k h hh).deriv

theorem harmonizableD_smooth : ContDiffOn ℝ (⊤ : ℕ∞) harmonizableD (Ioo (0 : ℝ) 1) := by
  have he : spectralLogMoment 1 0 = fun h => ∫ x, spectralCosineDensity h 1 x := by
    funext h
    simp [spectralLogMoment]
  have hs := spectralLogMoment_smooth 1 0
  rw [he] at hs
  exact hs.sqrt (fun h hh => (spectralCosineDensity_integral_pos h hh.1 hh.2).ne')

theorem harmonizableNormalizer_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) harmonizableNormalizer (Ioo (0 : ℝ) 1) := by
  exact (contDiffOn_const.mul harmonizableD_smooth).inv (fun h hh =>
    mul_ne_zero (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      (harmonizableD_pos h hh.1 hh.2).ne')

theorem smooth_uniform_iteratedDeriv_bound (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo (0 : ℝ) 1))
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) (r : ℕ) :
    ∃ C ≥ 0, ∀ h ∈ Icc a b, |iteratedDeriv r f h| ≤ C := by
  have hc0 := hf.continuousOn_iteratedDerivWithin (m := r) (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)) isOpen_Ioo.uniqueDiffOn
  have hc : ContinuousOn (iteratedDeriv r f) (Ioo (0 : ℝ) 1) := by
    apply hc0.congr
    intro h hh
    exact (iteratedDerivWithin_of_isOpen (n := r) isOpen_Ioo hh).symm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (fun h hh => ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩))
  exact ⟨max C 0, le_max_right _ _, fun h hh => (hC h hh).trans (le_max_left _ _)⟩

theorem harmonizableD_all_derivatives_uniform (a b : ℝ) (ha : 0 < a) (hb : b < 1) (r : ℕ) :
    ∃ C ≥ 0, ∀ h ∈ Icc a b, |iteratedDeriv r harmonizableD h| ≤ C :=
  smooth_uniform_iteratedDeriv_bound harmonizableD harmonizableD_smooth a b ha hb r

theorem harmonizableNormalizer_all_derivatives_uniform (a b : ℝ) (ha : 0 < a) (hb : b < 1) (r : ℕ) :
    ∃ C ≥ 0, ∀ h ∈ Icc a b, |iteratedDeriv r harmonizableNormalizer h| ≤ C :=
  smooth_uniform_iteratedDeriv_bound harmonizableNormalizer harmonizableNormalizer_smooth a b ha hb r

theorem harmonizableCovCoeff_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => harmonizableCovCoeff z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  let S := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => harmonizableD z.1) S :=
    harmonizableD_smooth.comp contDiff_fst.contDiffOn (fun z hz => hz.1)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => harmonizableD z.2) S :=
    harmonizableD_smooth.comp contDiff_snd.contDiffOn (fun z hz => hz.2)
  have hm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => harmonizableD ((z.1 + z.2) / 2)) S := by
    apply harmonizableD_smooth.comp (by fun_prop)
    intro z hz
    constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  exact (hm.pow 2).div (contDiffOn_const.mul hf |>.mul hg) (fun z hz =>
    mul_ne_zero (mul_ne_zero (by norm_num) (harmonizableD_pos z.1 hz.1.1 hz.1.2).ne')
      (harmonizableD_pos z.2 hz.2.1 hz.2.2).ne')

theorem harmonizableCovCoeff_all_derivatives_uniform (a b : ℝ) (ha : 0 < a) (hb : b < 1) (r : ℕ) :
    ∃ C ≥ 0, ∀ z ∈ Icc a b ×ˢ Icc a b,
      ‖iteratedFDeriv ℝ r (fun w : ℝ × ℝ => harmonizableCovCoeff w.1 w.2) z‖ ≤ C := by
  let U := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hc0 := harmonizableCovCoeff_smooth.continuousOn_iteratedFDerivWithin (m := r)
    (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)) hU.uniqueDiffOn
  have hc : ContinuousOn (iteratedFDeriv ℝ r (fun w : ℝ × ℝ => harmonizableCovCoeff w.1 w.2)) U := by
    apply hc0.congr
    intro z hz
    exact (iteratedFDerivWithin_of_isOpen r hU hz).symm
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.mono (fun z hz => ⟨⟨ha.trans_le hz.1.1, hz.1.2.trans_lt hb⟩,
      ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩⟩))
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩

end Hurst
