import Hurst.LinearScale

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

theorem firstScale_weighted_bias {ι : Type*} [Fintype ι]
    (w H m₁ m₂ : ι → ℝ) (L c e₁ e₂ : ℝ) (hL : 1 ≤ L)
    (hw : ∑ i, w i = 1)
    (h₁ : ∀ i, |m₁ i-(c-2*L*H i)| ≤ e₁)
    (h₂ : ∀ i, |m₂ i-(c-2*L*H i+2*Real.log 2*H i)| ≤ e₂) :
    |(1-L/Real.log 2)*smooth w m₁+(L/Real.log 2)*smooth w m₂-c| ≤
      (1+1/Real.log 2)*L*(∑ i, |w i|)*(e₁+e₂) := by
  have hl : 0 < Real.log 2 := by positivity
  have hL0 : 0 ≤ L := by linarith
  let a₁ := fun i => m₁ i-(c-2*L*H i)
  let a₂ := fun i => m₂ i-(c-2*L*H i+2*Real.log 2*H i)
  have he₁ := smooth_residual_bound w a₁ e₁ h₁
  have he₂ := smooth_residual_bound w a₂ e₂ h₂
  have hsum : smooth w (fun _ => c) = c := by unfold smooth; rw [← Finset.sum_mul,hw,one_mul]
  have hid : (1-L/Real.log 2)*smooth w m₁+(L/Real.log 2)*smooth w m₂-c =
      (1-L/Real.log 2)*smooth w a₁+(L/Real.log 2)*smooth w a₂ := by
    rw [← hsum]
    unfold smooth a₁ a₂
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
    <;> ring
  rw [hid]
  have hcoef : |1-L/Real.log 2| ≤ (1+1/Real.log 2)*L := by
    have hh := abs_sub 1 (L/Real.log 2)
    rw [abs_one,abs_of_nonneg (div_nonneg hL0 hl.le)] at hh
    calc
      _ ≤ 1+L/Real.log 2 := hh
      _ ≤ (1+1/Real.log 2)*L := by simp only [div_eq_mul_inv]; nlinarith
  have hcoef₂ : |L/Real.log 2| ≤ (1+1/Real.log 2)*L := by
    rw [abs_of_nonneg (div_nonneg hL0 hl.le)]
    simp only [div_eq_mul_inv]
    nlinarith
  have hcoef0 : 0 ≤ (1+1/Real.log 2)*L := by positivity
  calc
    _ ≤ |1-L/Real.log 2| * |smooth w a₁|+|L/Real.log 2| * |smooth w a₂| := by
      simpa only [abs_mul] using abs_add_le ((1-L/Real.log 2)*smooth w a₁) ((L/Real.log 2)*smooth w a₂)
    _ ≤ ((1+1/Real.log 2)*L)*((∑ i,|w i|)*e₁)+((1+1/Real.log 2)*L)*((∑ i,|w i|)*e₂) :=
      add_le_add (mul_le_mul hcoef he₁ (abs_nonneg _) hcoef0) (mul_le_mul hcoef₂ he₂ (abs_nonneg _) hcoef0)
    _ = _ := by ring

end Hurst
