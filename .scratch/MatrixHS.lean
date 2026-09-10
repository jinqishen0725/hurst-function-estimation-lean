import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
noncomputable section
open Matrix
open scoped RealInnerProductSpace Matrix.Norms.Frobenius
example {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) :
    |Matrix.trace (A * B)| ≤ ‖A‖ * ‖B‖ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    |∑ i, ∑ j, A i j * B j i| ≤ ∑ i, |∑ j, A i j * B j i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * B j i| := by
      gcongr with i
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, |A i j| * |B j i| := by simp only [abs_mul]
    _ ≤ Real.sqrt (∑ i, ∑ j, |A i j| ^ 2) * Real.sqrt (∑ i, ∑ j, |B j i| ^ 2) := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ.product Finset.univ : Finset (n × n))
        (fun p ↦ |A p.1 p.2|) (fun p ↦ |B p.2 p.1|)
      have hab : (∑ p ∈ (Finset.univ.product Finset.univ : Finset (n × n)),
          |A p.1 p.2| * |B p.2 p.1|) =
          ∑ i, ∑ j, |A i j| * |B j i| :=
        Finset.sum_product Finset.univ Finset.univ _
      have ha : (∑ p ∈ (Finset.univ.product Finset.univ : Finset (n × n)),
          |A p.1 p.2| ^ 2) = ∑ i, ∑ j, |A i j| ^ 2 :=
        Finset.sum_product Finset.univ Finset.univ _
      have hb : (∑ p ∈ (Finset.univ.product Finset.univ : Finset (n × n)),
          |B p.2 p.1| ^ 2) = ∑ i, ∑ j, |B j i| ^ 2 :=
        Finset.sum_product Finset.univ Finset.univ _
      rwa [hab, ha, hb] at h
    _ = ‖A‖ * ‖B‖ := by
      rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      congr 1
      · congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Real.norm_eq_abs, Real.rpow_two]
      · rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Real.norm_eq_abs, Real.rpow_two]
