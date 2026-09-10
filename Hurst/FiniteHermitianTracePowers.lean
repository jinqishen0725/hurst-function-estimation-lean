import Hurst.FiniteGaussianSpectral

noncomputable section

open Matrix

namespace Hurst

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every finite trace power of a real symmetric matrix is the corresponding
power sum of its eigenvalues. -/
theorem hermitian_trace_pow_eq_sum_eigenvalues_pow
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  let U := hA.eigenvectorUnitary
  let D : Matrix ι ι ℝ := diagonal hA.eigenvalues
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hspec : A = C D := by
    simpa [U, D, C, RCLike.ofReal_real_eq_id] using hA.spectral_theorem
  calc
    (A ^ k).trace = ((C D) ^ k).trace := by rw [hspec]
    _ = (C (D ^ k)).trace := by rw [map_pow]
    _ = ((U : Matrix ι ι ℝ) * (D ^ k) *
          star (U : Matrix ι ι ℝ)).trace := rfl
    _ = (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) * (D ^ k)).trace :=
      Matrix.trace_mul_cycle (U : Matrix ι ι ℝ) (D ^ k)
        (star (U : Matrix ι ι ℝ))
    _ = (D ^ k).trace := by
      rw [Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i, hA.eigenvalues i ^ k := by
      change (diagonal hA.eigenvalues ^ k).trace = _
      rw [Matrix.diagonal_pow]
      simp [Matrix.trace]

/-- One-step cyclic coordinate expansion of a trace power.  Iterating this
identity expands the trace into the usual sum over closed index cycles. -/
theorem matrix_trace_pow_succ_cyclic_coordinates
    (A : Matrix ι ι ℝ) (k : ℕ) :
    (A ^ (k + 1)).trace = ∑ i, ∑ j, (A ^ k) i j * A j i := by
  rw [pow_succ]
  rfl

/-- The cyclic coordinate expansion specialized to a real symmetric matrix. -/
theorem hermitian_trace_pow_succ_coordinates
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ (k + 1)).trace = ∑ i, ∑ j, (A ^ k) i j * A i j := by
  rw [matrix_trace_pow_succ_cyclic_coordinates A k]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hs : A j i = A i j := by
    simpa using hA.apply i j
  rw [hs]

end Hurst
