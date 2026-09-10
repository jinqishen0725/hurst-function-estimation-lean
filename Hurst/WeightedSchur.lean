import Mathlib.Tactic

noncomputable section
namespace Hurst

theorem symmetric_row_quadratic_bound {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (w : ι → ℝ) (B : ℝ)
    (hA : ∀ i j, 0≤A i j) (hsym : ∀ i j,A i j=A j i)
    (hrow : ∀ i,∑ j,A i j≤B) :
    (∑ i,∑ j,|w i| *|w j| *A i j) ≤ B*∑ i,w i^2 := by
  have hp (i j : ι) : |w i| *|w j| ≤ (w i^2+w j^2)/2 := by
    nlinarith [sq_nonneg (|w i|-|w j|),sq_abs (w i),sq_abs (w j)]
  have hb : (∑ i,∑ j,|w i| *|w j| *A i j) ≤
      ∑ i,∑ j,(w i^2*A i j+w j^2*A i j)/2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    calc
      _ ≤ ((w i^2+w j^2)/2)*A i j := mul_le_mul_of_nonneg_right (hp i j) (hA i j)
      _ = _ := by ring
  have he : (∑ i,∑ j,w j^2*A i j) = ∑ i,∑ j,w i^2*A i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hm : (∑ i,∑ j,w i^2*A i j) ≤ B*∑ i,w i^2 := by
    simp only [← Finset.mul_sum]
    calc
      _ ≤ ∑ i,w i^2*B := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul,mul_comm]
  simp only [← Finset.sum_div,Finset.sum_add_distrib,he] at hb
  linarith

end Hurst
