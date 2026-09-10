import Hurst.TruncatedVarianceFormula
import Hurst.GaussianLogRank

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- Every finite Hermite truncation of the centered Gaussian log function
retains Hermite rank at least two.  This is the polynomial-integral form used
in Bardet--Surgailis Theorem 1(ii). -/
theorem gaussianLogTruncationPolynomial_hermite_orthogonal
    (M k : ℕ) (hk : k < 2) :
    (∫ z : ℝ, (hermiteTruncationPolynomial gaussianLogLp M).eval z *
      (gaussianHermite k).eval z ∂gaussianReal 0 1) = 0 := by
  simp only [hermiteTruncationPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul]
  simp only [Finset.sum_mul]
  rw [show (fun z : ℝ => ∑ n ∈ Finset.range M,
      ⟪gaussianHermiteUnit n, gaussianLogLp⟫ *
          (Real.sqrt (n.factorial : ℝ))⁻¹ * (gaussianHermite n).eval z *
            (gaussianHermite k).eval z) =
      fun z : ℝ => ∑ n ∈ Finset.range M,
        (⟪gaussianHermiteUnit n, gaussianLogLp⟫ *
          (Real.sqrt (n.factorial : ℝ))⁻¹) *
            ((gaussianHermite n).eval z * (gaussianHermite k).eval z) by
      funext z
      apply Finset.sum_congr rfl
      intro n hn
      ring]
  calc
    (∫ z : ℝ, ∑ n ∈ Finset.range M,
        (⟪gaussianHermiteUnit n, gaussianLogLp⟫ *
          (Real.sqrt (n.factorial : ℝ))⁻¹) *
            ((gaussianHermite n).eval z * (gaussianHermite k).eval z)
      ∂gaussianReal 0 1) =
        ∑ n ∈ Finset.range M, ∫ z : ℝ,
          (⟪gaussianHermiteUnit n, gaussianLogLp⟫ *
            (Real.sqrt (n.factorial : ℝ))⁻¹) *
              ((gaussianHermite n).eval z * (gaussianHermite k).eval z)
          ∂gaussianReal 0 1 :=
      integral_finsetSum (Finset.range M) (fun n _ =>
        (standardGaussian_polynomial_memLp_two (gaussianHermite n)).integrable_mul
          (standardGaussian_polynomial_memLp_two (gaussianHermite k)) |>.const_mul _)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [integral_const_mul, standardGaussian_hermite_orthogonality]
      by_cases hnk : n = k
      · subst n
        rw [if_pos rfl, gaussianLog_hermite_rank_at_least_two k hk]
        ring
      · rw [if_neg hnk]
        ring

theorem gaussianLogTruncationPolynomial_rank_two (M : ℕ) :
    ∀ k, k < 2 →
      (∫ z : ℝ, (hermiteTruncationPolynomial gaussianLogLp M).eval z *
        (gaussianHermite k).eval z ∂gaussianReal 0 1) = 0 :=
  fun k hk => gaussianLogTruncationPolynomial_hermite_orthogonal M k hk

end Hurst
