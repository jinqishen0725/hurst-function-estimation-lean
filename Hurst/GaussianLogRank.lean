import Hurst.GaussianLogStein

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
open scoped RealInnerProductSpace
namespace Hurst

theorem gaussianHermite_two : gaussianHermite 2=X^2-1 := by
  rw [show 2=1+1 by norm_num,gaussianHermite_succ,gaussianHermite_one,Polynomial.derivative_X,pow_two]

theorem gaussianLog_second_hermite_integral :
    (∫ x,centeredGaussianLog x*(gaussianHermite 2).eval x ∂gaussianReal 0 1)=2 := by
  have hlog := log_square_memLp_two_gaussianReal 1 one_ne_zero
  have hH := standardGaussian_polynomial_memLp_two (gaussianHermite 2)
  have hi : Integrable (fun x => Real.log (x^2)*(gaussianHermite 2).eval x) (gaussianReal 0 1) :=
    hlog.integrable_mul hH
  have he : (∫ x,2-Real.log (x^2)*(gaussianHermite 2).eval x ∂gaussianReal 0 1)=0 := by
    rw [standardGaussian_weight_integral]
    have hid : (fun x => (2-Real.log (x^2)*(gaussianHermite 2).eval x)*gaussianWeight x) =
        gaussianLogSteinDerivative := by
      funext x
      simp only [gaussianHermite_two,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one,
        gaussianLogSteinDerivative]
      ring
    rw [hid,gaussianLogSteinDerivative_integral,mul_zero]
  rw [integral_sub (integrable_const _) hi,integral_const] at he
  simp only [measureReal_univ_eq_one,one_smul] at he
  have hid : (fun x => centeredGaussianLog x*(gaussianHermite 2).eval x) =
      fun x => Real.log (x^2)*(gaussianHermite 2).eval x-gaussianLogSquareMean*(gaussianHermite 2).eval x := by
    funext x
    unfold centeredGaussianLog
    ring
  rw [hid,integral_sub hi ((hH.integrable (by norm_num)).const_mul _),integral_const_mul,
    show (∫ x,(gaussianHermite 2).eval x ∂gaussianReal 0 1)=0 from standardGaussian_hermite_mean_succ 1,
    mul_zero,sub_zero]
  linarith

theorem gaussianLog_hermite_coefficient_two : ⟪gaussianHermiteUnit 2,gaussianLogLp⟫=Real.sqrt 2 := by
  rw [gaussianLog_hermite_coefficient,gaussianLog_second_hermite_integral]
  norm_num
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have he := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  field_simp
  nlinarith

theorem gaussianLog_hermite_rank_exactly_two :
    (∀ n : ℕ,n<2 → ⟪gaussianHermiteUnit n,gaussianLogLp⟫=0) ∧
      ⟪gaussianHermiteUnit 2,gaussianLogLp⟫≠0 := by
  refine ⟨gaussianLog_hermite_rank_at_least_two,?_⟩
  rw [gaussianLog_hermite_coefficient_two]
  exact (Real.sqrt_pos.mpr (by norm_num)).ne'

end Hurst
