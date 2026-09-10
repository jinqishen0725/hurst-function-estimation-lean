import Hurst.SpatialRisk
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

def unitLpLoss (s : ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ t in Ioo (0 : ℝ) 1, |f t - g t| ^ s) ^ s⁻¹

theorem unitLpLoss_nonneg (s : ℝ) (f g : ℝ → ℝ) : 0 ≤ unitLpLoss s f g :=
  Real.rpow_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)) _

theorem unitLpLoss_le_squared_integral (s : ℝ) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (unitLpLoss s f g) ^ 2 ≤ ∫ t in Ioo (0 : ℝ) 1, (f t - g t) ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hfs := continuous_memLp_unit (f - g) (hf.sub hg) (ENNReal.ofReal s)
  have hf2 := continuous_memLp_unit (f - g) (hf.sub hg) 2
  have hnorm := eLpNorm_le_eLpNorm_of_exponent_le (show ENNReal.ofReal s ≤ 2 by exact_mod_cast hs2) hfs.aestronglyMeasurable
  rw [hfs.eLpNorm_eq_integral_rpow_norm (by positivity) (by simp),
    hf2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hnorm
  simp only [ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_ofNat, Real.norm_eq_abs, Pi.sub_apply,
    Real.rpow_two, sq_abs] at hnorm
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at hnorm
  have hreal : unitLpLoss s f g ≤ Real.sqrt (∫ t in Ioo (0 : ℝ) 1, (f t - g t) ^ 2) := by
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hnorm
  have hsq := pow_le_pow_left₀ (unitLpLoss_nonneg s f g) hreal 2
  rwa [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hsq

theorem unitLpLoss_measurable {Ω : Type*} [MeasurableSpace Ω]
    (s : ℝ) (F : Ω → ℝ → ℝ) (g : ℝ → ℝ)
    (hF : Measurable (fun z : Ω × ℝ => F z.1 z.2)) (hg : Measurable g) :
    Measurable (fun x => unitLpLoss s (F x) g) := by
  have hm : Measurable (fun z : Ω × ℝ => |F z.1 z.2 - g z.2| ^ s) := by fun_prop
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))
  exact hi.measurable.pow_const s⁻¹

/-- Monotonicity of probability-space Lp norms transfers integrated MSE to every 1 ≤ s ≤ 2. -/
theorem unitLpRisk_le_integrated_mse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℝ) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (F : Ω → ℝ → ℝ) (g : ℝ → ℝ)
    (hF : Measurable (fun z : Ω × ℝ => F z.1 z.2)) (hg : Continuous g)
    (hFc : ∀ x, Continuous (F x)) (hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1)
    (hgb : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) :
    (∫ x, (unitLpLoss s (F x) g) ^ 2 ∂P) ≤
      ∫ x, (∫ t in Ioo (0 : ℝ) 1, (F x t - g t) ^ 2) ∂P := by
  have hbound : ∀ x, (∫ t in Ioo (0 : ℝ) 1, (F x t - g t) ^ 2) ≤ 1 := by
    intro x
    have hi := (continuous_memLp_unit (F x - g) ((hFc x).sub hg) 2).integrable_sq
    have he := integral_mono_ae hi (integrable_const (1 : ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hx := hFb x t
      have ht' := hgb ⟨ht.1.le, ht.2.le⟩
      have ha : |F x t - g t| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, ht'.2], by linarith [hx.2, ht'.1]⟩
      have he := pow_le_pow_left₀ (abs_nonneg _) ha 2
      simpa only [sq_abs, one_pow, Pi.sub_apply] using he)
    simpa only [Pi.sub_apply, integral_const, probReal_univ, one_smul] using he
  have hmeas : Measurable (fun x => ∫ t in Ioo (0 : ℝ) 1, (F x t - g t) ^ 2) := by
    have hm : Measurable (fun z : Ω × ℝ => (F z.1 z.2 - g z.2) ^ 2) := by fun_prop
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable
  have hi : Integrable (fun x => ∫ t in Ioo (0 : ℝ) 1, (F x t - g t) ^ 2) P := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact hbound x
  have hle := fun x => unitLpLoss_le_squared_integral s hs hs2 (F x) g (hFc x) hg
  have hLoss : Integrable (fun x => (unitLpLoss s (F x) g) ^ 2) P := by
    apply Integrable.of_bound ((unitLpLoss_measurable s F g hF hg.measurable).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hle x).trans (hbound x)
  exact integral_mono hLoss hi hle

end Hurst
