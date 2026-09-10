import Hurst.WeightedSchur
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
open scoped RealInnerProductSpace
namespace Hurst

theorem hilbert_weighted_sum_sq_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : ι → ℝ) (A : ι → ι → ℝ) (B C : ℝ)
    (hC : 0≤C) (hA : ∀ i j,0≤A i j) (hsym : ∀ i j,A i j=A j i)
    (hrow : ∀ i,∑ j,A i j≤B) (hv : ∀ i j,|⟪v i,v j⟫|≤C*A i j) :
    ‖∑ i,w i • v i‖^2 ≤ C*B*∑ i,w i^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,conj_trivial,Finset.mul_sum]
  calc
    _ ≤ ∑ i,∑ j,C*(|w i| * |w j| * A i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [real_inner_comm (v i) (v j)]
      calc
        _ ≤ |w i*(w j*⟪v i,v j⟫)| := le_abs_self _
        _ = |w i| * |w j| * |⟪v i,v j⟫| := by rw [abs_mul,abs_mul]; ring
        _ ≤ |w i| * |w j| * (C*A i j) :=
          mul_le_mul_of_nonneg_left (hv i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = _ := by ring
    _ = C*(∑ i,∑ j,|w i| * |w j| * A i j) := by simp only [Finset.mul_sum]
    _ ≤ C*(B*∑ i,w i^2) := mul_le_mul_of_nonneg_left (symmetric_row_quadratic_bound A w B hA hsym hrow) hC
    _ = _ := by rw [← mul_assoc,Finset.mul_sum]

end Hurst
