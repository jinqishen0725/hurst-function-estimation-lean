import Hurst.FeatureTime
import Hurst.SecondCancellation

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def frozenSecondIncrement (h : Ioo (0 : ℝ) 1) (t l : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  harmonizableFeature h (t + 2 * l) - (2 : ℝ) • harmonizableFeature h (t + l) + harmonizableFeature h t

def varyingSecondIncrement (h0 h1 h2 : Ioo (0 : ℝ) 1) (t l : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  harmonizableFeature h2 (t + 2 * l) - (2 : ℝ) • harmonizableFeature h1 (t + l) + harmonizableFeature h0 t

/-- The actual second-difference perturbation has a uniform normalized logarithmic rate. -/
theorem varyingSecondIncrement_uniform_remainder (a b B D : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ C ≥ 0, ∀ h0 h1 h2 : Ioo (0 : ℝ) 1,
      (h0 : ℝ) ∈ Icc a b → (h1 : ℝ) ∈ Icc a b → (h2 : ℝ) ∈ Icc a b →
      ∀ t l : ℝ, 0 < l → l ≤ 1 → |t + l| ≤ 1 → |t + 2 * l| ≤ 1 →
      |(h1 : ℝ) - h0| ≤ B * l → |(h2 : ℝ) - h0| ≤ 2 * B * l →
      |(h2 : ℝ) - 2 * h1 + h0| ≤ D * l ^ 2 →
      ‖l ^ (-(h0 : ℝ)) • (varyingSecondIncrement h0 h1 h2 t l - frozenSecondIncrement h0 t l)‖ ≤
        C * l * (1 + |Real.log l|) := by
  obtain ⟨R, hR, hr⟩ := harmonizableFeature_uniform_quadratic_remainder a b ha hb hab
  obtain ⟨S, hS, hs⟩ := harmonizableSlopeFeature_uniform_bound a b ha hb hab
  obtain ⟨T, hT, ht'⟩ := harmonizableSlopeFeature_time_increment_bound a b ha hb hab
  refine ⟨D * S + 6 * R * B ^ 2 + 2 * B * T, by positivity, ?_⟩
  intro h0 h1 h2 hh0 hh1 hh2 t l hl hl1 ht1 ht2 hd1 hd2 hdd
  have htime : ‖harmonizableSlopeFeature h0 (t + 2 * l) - harmonizableSlopeFeature h0 (t + l)‖ ≤
      T * (l ^ (h0 : ℝ) * (1 + |Real.log l|)) := by
    have ht0 := ht' h0 hh0 (t + l) l hl
    rw [show t + l + l = t + 2 * l by ring, mul_assoc] at ht0
    exact ht0
  have hdd' : |((h2 : ℝ) - h0) - 2 * ((h1 : ℝ) - h0)| ≤ D * l ^ 2 := by
    convert! hdd using 1 <;> congr 1 <;> ring
  have hc := second_difference_parameter_rate
    (harmonizableFeature h1 (t + l)) (harmonizableFeature h2 (t + 2 * l))
    (harmonizableFeature h0 (t + l)) (harmonizableFeature h0 (t + 2 * l))
    (harmonizableSlopeFeature h0 (t + l)) (harmonizableSlopeFeature h0 (t + 2 * l))
    ((h1 : ℝ) - h0) ((h2 : ℝ) - h0) R S T B D l (l ^ (h0 : ℝ) * (1 + |Real.log l|))
    hR hS hT hB hD hl.le (by positivity)
    (hr h0 h1 hh0 hh1 (t + l) ht1) (hr h0 h2 hh0 hh2 (t + 2 * l) ht2)
    (hs h0 hh0 (t + 2 * l) ht2) htime hd1 hd2 hdd'
  have he : varyingSecondIncrement h0 h1 h2 t l - frozenSecondIncrement h0 t l =
      (harmonizableFeature h2 (t + 2 * l) - harmonizableFeature h0 (t + 2 * l)) -
      (2 : ℝ) • (harmonizableFeature h1 (t + l) - harmonizableFeature h0 (t + l)) := by
    unfold varyingSecondIncrement frozenSecondIncrement
    module
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hl _), he]
  have hscale : l ^ (-(h0 : ℝ)) * l ^ (h0 : ℝ) = 1 := by
    rw [← Real.rpow_add hl, neg_add_cancel, Real.rpow_zero]
  have hsmall : l ^ (-(h0 : ℝ)) * l ^ 2 ≤ l := by
    rw [← Real.rpow_natCast l 2, ← Real.rpow_add hl]
    calc
      _ ≤ l ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hl hl1 (by norm_num; linarith [h0.property.2])
      _ = l := Real.rpow_one l
  have hc' := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hl.le (-(h0 : ℝ)))
  have hb0 : 0 ≤ D * S + 6 * R * B ^ 2 := by positivity
  have hsmall' := mul_le_mul_of_nonneg_left hsmall hb0
  have hlog := mul_nonneg (mul_nonneg hb0 hl.le) (abs_nonneg (Real.log l))
  have heprod : l ^ (-(h0 : ℝ)) *
      ((D * S + 6 * R * B ^ 2) * l ^ 2 + 2 * B * T * l * (l ^ (h0 : ℝ) * (1 + |Real.log l|))) =
      (D * S + 6 * R * B ^ 2) * (l ^ (-(h0 : ℝ)) * l ^ 2) + 2 * B * T * l * (1 + |Real.log l|) := by
    calc
      _ = (D * S + 6 * R * B ^ 2) * (l ^ (-(h0 : ℝ)) * l ^ 2) +
          2 * B * T * l * (1 + |Real.log l|) * (l ^ (-(h0 : ℝ)) * l ^ (h0 : ℝ)) := by ring
      _ = _ := by rw [hscale, mul_one]
  rw [heprod] at hc'
  nlinarith

end Hurst
