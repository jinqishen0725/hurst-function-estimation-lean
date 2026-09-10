import Hurst.GaussianLogRisk
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- Unit-length interval indicators give an explicit orthonormal family in
real `L²(ℝ)`.  They are used only to add independent Gaussian coordinates when
an active triangular-array row is embedded into a larger exact-size row. -/
def lebesgueUnitIntervalFeature (i : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 measurableSet_Ico (by simp [Real.volume_Ico]) 1
    (s := Ico (i : ℝ) (i + 1 : ℝ))

theorem lebesgueUnitInterval_inter (i j : ℕ) (hij : i ≠ j) :
    Ico (i : ℝ) (i + 1 : ℝ) ∩ Ico (j : ℝ) (j + 1 : ℝ) = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_Ico, mem_empty_iff_false, iff_false]
  rintro ⟨⟨hi0, hi1⟩, ⟨hj0, hj1⟩⟩
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hc : (i + 1 : ℕ) ≤ j := by omega
    have hc' : (i + 1 : ℕ) ≤ (j : ℝ) := by exact_mod_cast hc
    norm_num only [Nat.cast_add, Nat.cast_one] at hc'
    linarith
  · have hc : (j + 1 : ℕ) ≤ i := by omega
    have hc' : (j + 1 : ℕ) ≤ (i : ℝ) := by exact_mod_cast hc
    norm_num only [Nat.cast_add, Nat.cast_one] at hc'
    linarith

theorem lebesgueUnitIntervalFeature_inner (i j : ℕ) :
    ⟪lebesgueUnitIntervalFeature i, lebesgueUnitIntervalFeature j⟫ =
      if i = j then 1 else 0 := by
  have hiTop : volume (Ico (i : ℝ) (i + 1 : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Ico]
    simp
  have hjTop : volume (Ico (j : ℝ) (j + 1 : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Ico]
    simp
  unfold lebesgueUnitIntervalFeature
  rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    (hμs := hiTop) (hμt := hjTop)]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    rw [inter_self, Real.volume_real_Ico_of_le (by norm_num)]
    norm_num
  · rw [if_neg hij, lebesgueUnitInterval_inter i j hij]
    simp

theorem lebesgueUnitIntervalFeature_norm (i : ℕ) :
    ‖lebesgueUnitIntervalFeature i‖ = 1 := by
  have hinner := lebesgueUnitIntervalFeature_inner i i
  simp only [if_pos] at hinner
  rw [real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (lebesgueUnitIntervalFeature i)]

theorem lebesgueUnitIntervalFeature_ne_zero (i : ℕ) :
    lebesgueUnitIntervalFeature i ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [lebesgueUnitIntervalFeature_norm]; norm_num)

end Hurst
