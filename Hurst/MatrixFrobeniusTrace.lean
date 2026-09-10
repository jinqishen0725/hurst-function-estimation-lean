import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open Filter Matrix
open scoped Topology Matrix.Norms.Frobenius
namespace Hurst

/-- The trace pairing is bounded by the product of Frobenius norms. -/
theorem abs_matrix_trace_mul_le_frobenius
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) :
    |Matrix.trace (A * B)| ≤ ‖A‖ * ‖B‖ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    |∑ i, ∑ j, A i j * B j i| ≤ ∑ i, |∑ j, A i j * B j i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * B j i| := by
      gcongr with i
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, |A i j| * |B j i| := by simp only [abs_mul]
    _ ≤ Real.sqrt (∑ i, ∑ j, |A i j| ^ 2) *
        Real.sqrt (∑ i, ∑ j, |B j i| ^ 2) := by
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
      rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
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

/-- Frobenius convergence of fixed-size matrices implies convergence of every
fixed power trace.  This is the finite-dimensional continuity step used in
the cyclic-trace argument. -/
theorem matrix_trace_pow_tendsto_of_frobenius_sub_tendsto_zero
    {d : ℕ} {I : Type*} {l : Filter I}
    (A : I → Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ)
    (hA : Tendsto (fun i ↦ ‖A i - B‖) l (nhds 0)) (k : ℕ) :
    Tendsto (fun i ↦ Matrix.trace ((A i) ^ k)) l
      (nhds (Matrix.trace (B ^ k))) := by
  have hAB : Tendsto A l (nhds B) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hA
  have hpow : Tendsto (fun i ↦ (A i) ^ k) l (nhds (B ^ k)) := hAB.pow k
  exact ((Matrix.traceLinearMap (Fin d) ℝ ℝ).continuous_of_finiteDimensional
    |>.tendsto (B ^ k)).comp hpow

end Hurst
