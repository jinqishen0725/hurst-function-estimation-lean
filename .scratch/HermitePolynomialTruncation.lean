import Hurst.HermiteTruncation
import Hurst.GaussianPullback

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
open scoped RealInnerProductSpace
namespace Hurst

def hermiteTruncationPolynomial (f : GaussianL2) (M : ℕ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range M,
    (⟪gaussianHermiteUnit n,f⟫*(Real.sqrt (n.factorial:ℝ))⁻¹) • gaussianHermite n

theorem hermiteTruncation_polynomial_ae (f : GaussianL2) (M : ℕ) :
    hermiteTruncation f M =ᵐ[gaussianReal 0 1] fun x => (hermiteTruncationPolynomial f M).eval x := by
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range M)
      (fun n => ⟪gaussianHermiteUnit n,f⟫ • gaussianHermiteUnit n),
    ae_all_iff.mpr (fun n => Lp.coeFn_smul ⟪gaussianHermiteUnit n,f⟫ (gaussianHermiteUnit n)),
    ae_all_iff.mpr gaussianHermiteUnit_ae] with x hsum hsmul hpoly
  change ((∑ n ∈ Finset.range M,⟪gaussianHermiteUnit n,f⟫ • gaussianHermiteUnit n) : GaussianL2) x = _
  rw [hsum]
  simp only [hermiteTruncationPolynomial,Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [hsmul n]
  simp only [Pi.smul_apply,smul_eq_mul,hpoly n,Polynomial.eval_smul]
  ring

theorem gaussianLog_hermiteTail_polynomial_ae (M : ℕ) :
    hermiteTail gaussianLogLp M =ᵐ[gaussianReal 0 1]
      fun x => centeredGaussianLog x-(hermiteTruncationPolynomial gaussianLogLp M).eval x := by
  filter_upwards [Lp.coeFn_sub gaussianLogLp (hermiteTruncation gaussianLogLp M),
    gaussianLogLp_ae,hermiteTruncation_polynomial_ae gaussianLogLp M] with x hsub hf hp
  simpa only [hermiteTail,Pi.sub_apply,hf,hp] using hsub

end Hurst
