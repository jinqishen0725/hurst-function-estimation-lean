import Hurst.GaussianKLMulti
import Hurst.Rates

/-! Connect the actual Gaussian divergence with the previously proved spectral estimate.
The paper-specific bounds on the eigenvalues remain separate obligations. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal
namespace Hurst

theorem klDiv_multivariateGaussian_unit_spectral {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
      (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) =
      ENNReal.ofReal (spectralKL Finset.univ (fun i => hA.1.eigenvalues i - 1)) := by
  rw [klDiv_multivariateGaussian_zero A 1 hA Matrix.PosDef.one,
    Matrix.det_one, Real.log_one, inv_one, one_mul]
  congr 1
  rw [hA.1.det_eq_prod_eigenvalues, hA.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  unfold spectralKL
  simp only [add_sub_cancel, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Proposition 8.1's spectral step now bounds actual KL, not a stand-alone expression. -/
theorem klDiv_multivariateGaussian_unit_bound {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (hev : ∀ i, |hA.1.eigenvalues i - 1| ≤ (1 / 2 : ℝ)) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
      (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) ≤
      ENNReal.ofReal (∑ i, (hA.1.eigenvalues i - 1) ^ 2) := by
  rw [klDiv_multivariateGaussian_unit_spectral A hA]
  exact ENNReal.ofReal_le_ofReal (spectralKL_bound Finset.univ _ (fun i _ => hev i)).2

/-- A global scalar estimate from log(1/x) ≤ 1/x - 1. Unlike a local Taylor bound,
this only requires positivity and imposes no upper bound on x. -/
theorem log_deviation_le_sq_div (x : ℝ) (hx : 0 < x) :
    0 ≤ x - 1 - Real.log x ∧ x - 1 - Real.log x ≤ (x - 1) ^ 2 / x := by
  have hlo := Real.log_le_sub_one_of_pos hx
  have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hinv
  have he : (x - 1) ^ 2 / x = x - 2 + x⁻¹ := by
    field_simp
    ring
  rw [he]
  constructor <;> linarith

/-- The file 20 KL estimate with only a spectral floor. This works even when the
covariance does not converge to the identity. -/
theorem klDiv_multivariateGaussian_unit_bound_of_floor {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (m : ℝ) (hm : 0 < m)
    (hev : ∀ i, m ≤ hA.1.eigenvalues i) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
      (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) ≤
      ENNReal.ofReal ((∑ i, (hA.1.eigenvalues i - 1) ^ 2) / (2 * m)) := by
  rw [klDiv_multivariateGaussian_unit_spectral A hA]
  apply ENNReal.ofReal_le_ofReal
  have hterm : ∀ i, hA.1.eigenvalues i - 1 - Real.log (hA.1.eigenvalues i) ≤
      (hA.1.eigenvalues i - 1) ^ 2 / m := by
    intro i
    exact (log_deviation_le_sq_div _ (hA.eigenvalues_pos i)).2.trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hm (hev i))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [← Finset.sum_div] at hsum
  unfold spectralKL
  simp only [add_sub_cancel]
  have he : (∑ i, (hA.1.eigenvalues i - 1) ^ 2) / (2 * m) =
      (1 / 2 : ℝ) * ((∑ i, (hA.1.eigenvalues i - 1) ^ 2) / m) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- At the quarter spectral floor in file 20, constant 2 suffices (the written
Taylor argument used the valid but looser constant 4). -/
theorem klDiv_multivariateGaussian_unit_bound_quarter {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (hev : ∀ i, (1 / 4 : ℝ) ≤ hA.1.eigenvalues i) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
      (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) ≤
      ENNReal.ofReal (2 * ∑ i, (hA.1.eigenvalues i - 1) ^ 2) := by
  convert klDiv_multivariateGaussian_unit_bound_of_floor A hA (1 / 4) (by norm_num) hev using 1 <;>
    congr 1 <;> ring

/-- The squared spectral error equals the actual sum of squared matrix entries.
This supplies the Frobenius identification used in files 09 and 20. -/
theorem eigenvalue_error_sum_eq_matrix_error {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i - 1) ^ 2) = ∑ i, ∑ j, ((A - 1) i j) ^ 2 := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) (star hA.eigenvectorUnitary)
  have ht (B : Matrix (Fin d) (Fin d) ℝ) : (e B).trace = B.trace := by
    dsimp [e]
    rw [star_star, Matrix.trace_mul_cycle,
      ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]
  have hd : e (A - 1) = Matrix.diagonal (fun i => hA.eigenvalues i - 1) := by
    rw [map_sub, map_one]
    change Unitary.conjStarAlgAut ℝ _ (star hA.eigenvectorUnitary) A - 1 = _
    rw [hA.conjStarAlgAut_star_eigenvectorUnitary]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have htrace := ht ((A - 1) * (A - 1))
  rw [map_mul, hd, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal] at htrace
  have hs : ∀ i j, (A - 1) i j = (A - 1) j i := by
    intro i j
    have hh := (hA.sub Matrix.isHermitian_one).apply j i
    simpa using hh
  calc
    (∑ i, (hA.eigenvalues i - 1) ^ 2) = ((A - 1) * (A - 1)).trace := by
      simpa only [pow_two] using htrace
    _ = ∑ i, ∑ j, ((A - 1) i j) ^ 2 := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hs i j, pow_two]

/-- File 20's KL bound now has the actual Frobenius error on its right-hand side. -/
theorem klDiv_multivariateGaussian_unit_frobenius_quarter {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (hev : ∀ i, (1 / 4 : ℝ) ≤ hA.1.eigenvalues i) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
      (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) ≤
      ENNReal.ofReal (2 * ∑ i, ∑ j, ((A - 1) i j) ^ 2) := by
  simpa only [eigenvalue_error_sum_eq_matrix_error A hA.1] using
    klDiv_multivariateGaussian_unit_bound_quarter A hA hev

end Hurst
