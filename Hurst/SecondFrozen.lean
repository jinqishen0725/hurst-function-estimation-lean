import Hurst.PowerDifferences
import Hurst.SecondIncrement
import Hurst.FrozenCorrelation
import Hurst.StationaryDifferences

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem frozenSecondIncrement_eq (h : Ioo (0 : ℝ) 1) (t l : ℝ) :
    frozenSecondIncrement h t l = secondDifferenceFeature h t l := by
  unfold frozenSecondIncrement secondDifferenceFeature
  module

theorem frozenSecondIncrement_inner_forward (h k : Ioo (0 : ℝ) 1) (s t l : ℝ)
    (hl : 0 < l) (hst : s + 2 * l < t) :
    ⟪frozenSecondIncrement h s l, frozenSecondIncrement k t l⟫ =
      -harmonizableCovCoeff h k * powerForwardDifference 4 ((h : ℝ) + k) l (t - (s + 2 * l)) := by
  have e00 : |s - t| = t - (s + 2 * l) + 2 * l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e01 : |s - (t + l)| = t - (s + 2 * l) + 3 * l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e02 : |s - (t + 2 * l)| = t - (s + 2 * l) + 4 * l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e10 : |(s + l) - t| = t - (s + 2 * l) + l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e11 : |(s + l) - (t + l)| = t - (s + 2 * l) + 2 * l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e12 : |(s + l) - (t + 2 * l)| = t - (s + 2 * l) + 3 * l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e20 : |(s + 2 * l) - t| = t - (s + 2 * l) := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e21 : |(s + 2 * l) - (t + l)| = t - (s + 2 * l) + l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have e22 : |(s + 2 * l) - (t + 2 * l)| = t - (s + 2 * l) + 2 * l := by
    rw [abs_of_nonpos (by linarith)]
    ring
  simp only [frozenSecondIncrement, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, harmonizableFeature_inner_formula,
    e00, e01, e02, e10, e11, e12, e20, e21, e22, powerForwardDifference_four, harmonizableCovCoeff]
  ring

theorem frozenSecondIncrement_inner_bound (h k : Ioo (0 : ℝ) 1) (s t l : ℝ)
    (hl : 0 < l) (hst : s + 2 * l < t) :
    |⟪frozenSecondIncrement h s l, frozenSecondIncrement k t l⟫| ≤
      256 * harmonizableCovCoeff h k * (t - (s + 2 * l)) ^ ((h : ℝ) + k - 4) * l ^ 4 := by
  rw [frozenSecondIncrement_inner_forward h k s t l hl hst, abs_mul, abs_neg,
    abs_of_nonneg (harmonizableCovCoeff_nonneg h k)]
  have hr := powerForwardDifference_four_bound ((h : ℝ) + k) l (t - (s + 2 * l))
    (by linarith [h.property.1, k.property.1]) (by linarith [h.property.2, k.property.2]) hl.le (by linarith)
  exact (mul_le_mul_of_nonneg_left hr (harmonizableCovCoeff_nonneg h k)).trans_eq (by ring)

def normalizedFrozenSecondIncrement (h : Ioo (0 : ℝ) 1) (t l : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  l ^ (-(h : ℝ)) • frozenSecondIncrement h t l

theorem normalizedFrozenSecondIncrement_norm_sq (h : Ioo (0 : ℝ) 1) (t l : ℝ) (hl : 0 < l) :
    ‖normalizedFrozenSecondIncrement h t l‖ ^ 2 = 4 - (2 : ℝ) ^ (2 * (h : ℝ)) := by
  rw [normalizedFrozenSecondIncrement, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    frozenSecondIncrement_eq, secondDifferenceFeature_norm_sq, abs_of_pos hl]
  have he : (l ^ (-(h : ℝ))) ^ 2 * l ^ (2 * (h : ℝ)) = 1 := by
    rw [← Real.rpow_natCast (l ^ (-(h : ℝ))) 2, ← Real.rpow_mul hl.le, ← Real.rpow_add hl]
    convert Real.rpow_zero l using 1
    congr 1
    norm_num
    ring
  calc
    _ = (4 - (2 : ℝ) ^ (2 * (h : ℝ))) * ((l ^ (-(h : ℝ))) ^ 2 * l ^ (2 * (h : ℝ))) := by ring
    _ = _ := by rw [he, mul_one]

theorem normalizedFrozenSecondIncrement_norm_le (h : Ioo (0 : ℝ) 1) (t l : ℝ) (hl : 0 < l) :
    ‖normalizedFrozenSecondIncrement h t l‖ ≤ 2 := by
  have he := normalizedFrozenSecondIncrement_norm_sq h t l hl
  nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * (h : ℝ)),
    norm_nonneg (normalizedFrozenSecondIncrement h t l)]

theorem normalizedFrozenSecondIncrement_separated_bound (h k : Ioo (0 : ℝ) 1) (s t l d : ℝ)
    (hl : 0 < l) (hd : 0 < d) (hgap : t - (s + 2 * l) = d * l) :
    |⟪normalizedFrozenSecondIncrement h s l, normalizedFrozenSecondIncrement k t l⟫| ≤
      256 * harmonizableCovCoeff h k * d ^ ((h : ℝ) + k - 4) := by
  have hst : s + 2 * l < t := by have := mul_pos hd hl; linarith
  have hr := frozenSecondIncrement_inner_bound h k s t l hl hst
  rw [hgap, Real.mul_rpow hd.le hl.le] at hr
  rw [normalizedFrozenSecondIncrement, normalizedFrozenSecondIncrement, real_inner_smul_left, real_inner_smul_right,
    abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hl.le _), abs_of_nonneg (Real.rpow_nonneg hl.le _)]
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr
    (Real.rpow_nonneg hl.le (-(k : ℝ)))) (Real.rpow_nonneg hl.le (-(h : ℝ)))
  apply hm.trans_eq
  have he : l ^ (-(h : ℝ)) * l ^ (-(k : ℝ)) * l ^ ((h : ℝ) + k - 4) * l ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add hl, ← Real.rpow_add hl, ← Real.rpow_add hl]
    convert Real.rpow_zero l using 1
    congr 1
    ring
  norm_num only [Real.rpow_ofNat] at he
  calc
    _ = (256 * harmonizableCovCoeff h k * d ^ ((h : ℝ) + k - 4)) *
        (l ^ (-(h : ℝ)) * l ^ (-(k : ℝ)) * l ^ ((h : ℝ) + k - 4) * l ^ 4) := by ring
    _ = _ := by rw [he, mul_one]

theorem normalizedFrozenSecondIncrement_uniform_decay (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s t l d : ℝ, 0 < l → 1 ≤ d → t - (s + 2 * l) = d * l →
        |⟪normalizedFrozenSecondIncrement h s l, normalizedFrozenSecondIncrement k t l⟫| ≤
          C * d ^ (2 * b - 4) := by
  obtain ⟨C, hC, hc⟩ := harmonizableCovCoeff_uniform_bound a b ha hb hab
  refine ⟨256 * C, by positivity, ?_⟩
  intro h k hh hk s t l d hl hd hgap
  apply (normalizedFrozenSecondIncrement_separated_bound h k s t l d hl (by linarith) hgap).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hc h k hh hk) (by norm_num : (0 : ℝ) ≤ 256))
    (Real.rpow_le_rpow_of_exponent_le hd (by linarith [hh.2, hk.2]))
    (Real.rpow_nonneg (by linarith : 0 ≤ d) _) (by positivity)

theorem normalizedFrozenSecondIncrement_uniform_norm_floor (b : ℝ) (hb : b < 1) :
    ∃ c > 0, ∀ h : Ioo (0 : ℝ) 1, (h : ℝ) ≤ b → ∀ t l : ℝ, 0 < l →
      c ≤ ‖normalizedFrozenSecondIncrement h t l‖ := by
  have hp : (2 : ℝ) ^ (2 * b) < 4 := by
    calc
      _ < (2 : ℝ) ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 4 := by norm_num
  refine ⟨Real.sqrt (4 - (2 : ℝ) ^ (2 * b)), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro h hh t l hl
  have hs := Real.sq_sqrt (show 0 ≤ 4 - (2 : ℝ) ^ (2 * b) by linarith)
  have he := normalizedFrozenSecondIncrement_norm_sq h t l hl
  have hp' := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (show 2 * (h : ℝ) ≤ 2 * b by linarith)
  nlinarith [Real.sqrt_nonneg (4 - (2 : ℝ) ^ (2 * b)), norm_nonneg (normalizedFrozenSecondIncrement h t l)]

end Hurst
