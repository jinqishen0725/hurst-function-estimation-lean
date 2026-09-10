import Hurst.OptimalCombinedRawEvenMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

 theorem lower_real_moment_of_even {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ)
    (s : ℝ) (k : ℕ) (hs : 0 < s) (hk : 1 ≤ k) (hsk : s ≤ (2 * k : ℕ))
    (hmem : MemLp F (ENNReal.ofReal (2 * k : ℝ)) μ)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : (∫ x, |F x| ^ (2 * k) ∂μ) ≤ A ^ (2 * k)) :
    MemLp F (ENNReal.ofReal s) μ ∧
      (∫ x, |F x| ^ s ∂μ) ≤ A ^ s := by
  have hpq : ENNReal.ofReal s ≤ ENNReal.ofReal (2 * k : ℝ) :=
    ENNReal.ofReal_le_ofReal (by exact_mod_cast hsk)
  have hsmem := hmem.mono_exponent hpq
  refine ⟨hsmem, ?_⟩
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le hpq hmem.aestronglyMeasurable
  have hmonor := ENNReal.toReal_mono hmem.2.ne hmono
  rw [MeasureTheory.toReal_eLpNorm hsmem.aestronglyMeasurable,
    MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable] at hmonor
  have hs0 : ENNReal.ofReal s ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hs)
  have hq0 : ENNReal.ofReal (2 * k : ℝ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hqtop : ENNReal.ofReal (2 * k : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsEq := MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hs0 hstop
    hsmem.aestronglyMeasurable
  have hqEq := MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop
    hmem.aestronglyMeasurable
  have hqto : (ENNReal.ofReal (2 * k : ℝ)).toReal = (2 * k : ℕ) := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    norm_num
  rw [ENNReal.toReal_ofReal hs.le] at hsEq
  rw [hqto] at hqEq
  have hIq0 : 0 ≤ ∫ x, |F x| ^ (2 * k) ∂μ :=
    integral_nonneg (fun x => pow_nonneg (abs_nonneg (F x)) _)
  have hIs0 : 0 ≤ ∫ x, |F x| ^ s ∂μ := integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hqne : 2 * k ≠ 0 := Nat.mul_ne_zero (by norm_num) (by omega)
  have hqroot : MeasureTheory.lpNorm F (ENNReal.ofReal (2 * k : ℝ)) μ ≤ A := by
    rw [hqEq]
    calc
      (∫ x, ‖F x‖ ^ ((2 * k : ℕ) : ℝ) ∂μ) ^ ((2 * k : ℕ) : ℝ)⁻¹ =
          (∫ x, |F x| ^ (2 * k) ∂μ) ^ ((2 * k : ℕ) : ℝ)⁻¹ := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with x
            rw [Real.norm_eq_abs, Real.rpow_natCast]
      _ ≤ (A ^ (2 * k)) ^ ((2 * k : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow hIq0 hbound (by positivity)
      _ = A := Real.pow_rpow_inv_natCast hA hqne
  have hsroot : (∫ x, |F x| ^ s ∂μ) ^ s⁻¹ ≤ A := by
    rw [hsEq] at hmonor
    simpa only [Real.norm_eq_abs] using hmonor.trans hqroot
  calc
    (∫ x, |F x| ^ s ∂μ) = ((∫ x, |F x| ^ s ∂μ) ^ s⁻¹) ^ s :=
      (Real.rpow_inv_rpow hIs0 hs.ne').symm
    _ ≤ A ^ s := Real.rpow_le_rpow (Real.rpow_nonneg hIs0 _) hsroot hs.le

end Hurst
