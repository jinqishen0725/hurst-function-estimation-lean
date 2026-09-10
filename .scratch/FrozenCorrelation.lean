import Hurst.FrozenEstimates
import Hurst.VaryingIncrement

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem raw_increment_inner_rectangle (h k : Ioo (0 : ℝ) 1) (s ℓ t m : ℝ)
    (hl : 0 < ℓ) (hm : 0 < m) (hst : s + ℓ ≤ t) :
    ⟪harmonizableFeature h (s + ℓ) - harmonizableFeature h s,
      harmonizableFeature k (t + m) - harmonizableFeature k t⟫ =
      harmonizableCovCoeff h k *
      ((t + m - s) ^ ((h : ℝ) + k) - (t + m - (s + ℓ)) ^ ((h : ℝ) + k) -
        ((t - s) ^ ((h : ℝ) + k) - (t - (s + ℓ)) ^ ((h : ℝ) + k))) := by
  have e1 : |s + ℓ - (t + m)| = t + m - (s + ℓ) := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have e2 : |s - (t + m)| = t + m - s := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have e3 : |s + ℓ - t| = t - (s + ℓ) := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have e4 : |s - t| = t - s := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  simp only [inner_sub_left, inner_sub_right, harmonizableFeature_inner_formula, e1, e2, e3, e4, harmonizableCovCoeff]
  ring

theorem raw_increment_inner_bound (h k : Ioo (0 : ℝ) 1) (s ℓ t m : ℝ)
    (hl : 0 < ℓ) (hm : 0 < m) (hst : s + ℓ < t) :
    |⟪harmonizableFeature h (s + ℓ) - harmonizableFeature h s,
      harmonizableFeature k (t + m) - harmonizableFeature k t⟫| ≤
      harmonizableCovCoeff h k * ((((h : ℝ) + k) * |(h : ℝ) + k - 1| *
        (t - (s + ℓ)) ^ ((h : ℝ) + k - 2) * ℓ) * m) := by
  have hr := rpow_rectangle_bound ((h : ℝ) + k) s (s + ℓ) t (t + m)
    (by linarith [h.property.1, k.property.1]) (by linarith [h.property.2, k.property.2])
    (by linarith) hst (by linarith)
  simp only [add_sub_cancel_left] at hr
  rw [raw_increment_inner_rectangle h k s ℓ t m hl hm hst.le, abs_mul,
    abs_of_nonneg (harmonizableCovCoeff_nonneg h k)]
  exact mul_le_mul_of_nonneg_left hr (harmonizableCovCoeff_nonneg h k)

theorem normalizedFrozenIncrement_separated_bound (h k : Ioo (0 : ℝ) 1) (s t ℓ d : ℝ)
    (hl : 0 < ℓ) (hd : 0 < d) (hgap : t - (s + ℓ) = d * ℓ) :
    |⟪normalizedFrozenIncrement h s ℓ, normalizedFrozenIncrement k t ℓ⟫| ≤
      harmonizableCovCoeff h k * ((h : ℝ) + k) * |(h : ℝ) + k - 1| * d ^ ((h : ℝ) + k - 2) := by
  have hst : s + ℓ < t := by have := mul_pos hd hl; linarith
  have hr := raw_increment_inner_bound h k s ℓ t ℓ hl hl hst
  rw [hgap, Real.mul_rpow hd.le hl.le] at hr
  rw [normalizedFrozenIncrement, normalizedFrozenIncrement, real_inner_smul_left, real_inner_smul_right,
    abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hl.le _), abs_of_nonneg (Real.rpow_nonneg hl.le _)]
  calc
    _ ≤ ℓ ^ (-(h : ℝ)) * (ℓ ^ (-(k : ℝ)) *
        (harmonizableCovCoeff h k * ((((h : ℝ) + k) * |(h : ℝ) + k - 1| *
        (d ^ ((h : ℝ) + k - 2) * ℓ ^ ((h : ℝ) + k - 2)) * ℓ) * ℓ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hl.le _)) (Real.rpow_nonneg hl.le _)
    _ = _ := by
      have he : ℓ ^ (-(h : ℝ)) * ℓ ^ (-(k : ℝ)) * ℓ ^ ((h : ℝ) + k - 2) * ℓ ^ (2 : ℝ) = 1 := by
        rw [← Real.rpow_add hl, ← Real.rpow_add hl, ← Real.rpow_add hl]
        convert Real.rpow_zero ℓ using 1
        congr 1
        ring
      rw [Real.rpow_two] at he
      calc
        _ = (harmonizableCovCoeff h k * ((h : ℝ) + k) * |(h : ℝ) + k - 1| * d ^ ((h : ℝ) + k - 2)) *
            (ℓ ^ (-(h : ℝ)) * ℓ ^ (-(k : ℝ)) * ℓ ^ ((h : ℝ) + k - 2) * ℓ ^ 2) := by ring
        _ = _ := by rw [he, mul_one]

theorem normalizedFrozenIncrement_uniform_decay (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s t ℓ d : ℝ, 0 < ℓ → 1 ≤ d → t - (s + ℓ) = d * ℓ →
        |⟪normalizedFrozenIncrement h s ℓ, normalizedFrozenIncrement k t ℓ⟫| ≤ C * d ^ (2 * b - 2) := by
  obtain ⟨C, hC, hc⟩ := harmonizableCovCoeff_uniform_bound a b ha hb hab
  refine ⟨2 * C, by positivity, ?_⟩
  intro h k hh hk s t ℓ d hl hd hgap
  have hp0 : 0 ≤ (h : ℝ) + k := by linarith [h.property.1, k.property.1]
  have hp2 : (h : ℝ) + k ≤ 2 := by linarith [h.property.2, k.property.2]
  have hp1 : |(h : ℝ) + k - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hc' : harmonizableCovCoeff h k ≤ C := hc h k hh hk
  have hm := mul_le_mul hc' hp2 hp0 hC
  have hm' := mul_le_mul hm hp1 (abs_nonneg _) (by positivity : 0 ≤ C * 2)
  have hpow := Real.rpow_le_rpow_of_exponent_le hd (show (h : ℝ) + k - 2 ≤ 2 * b - 2 by linarith [hh.2, hk.2])
  apply (normalizedFrozenIncrement_separated_bound h k s t ℓ d hl (by linarith) hgap).trans
  have he := mul_le_mul hm' hpow (Real.rpow_nonneg (by linarith : 0 ≤ d) _) (by positivity : 0 ≤ C * 2 * 1)
  simpa only [mul_one, mul_comm C 2] using he

end Hurst
