import Hurst.GaussianHermite

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
namespace Hurst

theorem standardGaussian_polynomial_stein (p : Polynomial ℝ) :
    (∫ x,p.derivative.eval x ∂gaussianReal 0 1) = ∫ x,x*p.eval x ∂gaussianReal 0 1 := by
  rw [standardGaussian_weight_integral,standardGaussian_weight_integral,polynomial_gaussian_stein]

theorem standardGaussian_affine_polynomial_integrable (p : Polynomial ℝ) (a b : ℝ) :
    Integrable (fun x : ℝ => p.eval (a+b*x)) (gaussianReal 0 1) := by
  convert standardGaussian_polynomial_integrable (p.comp (C a+C b*X)) using 1 <;>
    first | rfl | (funext x; simp)

theorem standardGaussian_affine_hermite_stein (n : ℕ) (a b : ℝ) :
    (∫ x,x*(gaussianHermite (n+1)).eval (a+b*x) ∂gaussianReal 0 1) =
      b*(n+1)*(∫ x,(gaussianHermite n).eval (a+b*x) ∂gaussianReal 0 1) := by
  have he := standardGaussian_polynomial_stein ((gaussianHermite (n+1)).comp (C a+C b*X))
  simp only [Polynomial.derivative_comp,gaussianHermite_derivative_succ,
    Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.derivative_add,Polynomial.derivative_C,Polynomial.derivative_mul,
    Polynomial.derivative_X,zero_mul,zero_add,mul_one] at he
  rw [← he,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem standardGaussian_conditional_hermite (n : ℕ) (ρ s x : ℝ) (h : ρ^2+s^2=1) :
    (∫ y,(gaussianHermite n).eval (ρ*x+s*y) ∂gaussianReal 0 1) =
      ρ^n*(gaussianHermite n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gaussianHermite_zero]
  | one =>
    simp only [gaussianHermite_one,Polynomial.eval_X,pow_one]
    rw [integral_add (integrable_const _) ((show Integrable (fun y : ℝ => y) (gaussianReal 0 1) from by
        simpa using standardGaussian_polynomial_integrable X).const_mul s),
      integral_const,integral_const_mul,integral_id_gaussianReal]
    simp
  | more n hn hn1 =>
    have h0 := standardGaussian_affine_polynomial_integrable (gaussianHermite n) (ρ*x) s
    have h1 := standardGaussian_affine_polynomial_integrable (gaussianHermite (n+1)) (ρ*x) s
    have hy : Integrable (fun y : ℝ => y*(gaussianHermite (n+1)).eval (ρ*x+s*y)) (gaussianReal 0 1) := by
      convert standardGaussian_polynomial_integrable
        (X*((gaussianHermite (n+1)).comp (C (ρ*x)+C s*X))) using 1 <;>
        first | rfl | (funext y; simp)
    have he : (fun y : ℝ => (gaussianHermite (n+2)).eval (ρ*x+s*y)) =
        fun y => ρ*x*(gaussianHermite (n+1)).eval (ρ*x+s*y)+
          s*(y*(gaussianHermite (n+1)).eval (ρ*x+s*y))-
            (n+1)*(gaussianHermite n).eval (ρ*x+s*y) := by
      funext y
      rw [show n+2=(n+1)+1 by omega,gaussianHermite_succ (n+1),gaussianHermite_derivative_succ]
      simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
      ring
    have hA : Integrable (fun y => ρ*x*(gaussianHermite (n+1)).eval (ρ*x+s*y)) (gaussianReal 0 1) := h1.const_mul _
    have hB : Integrable (fun y => s*(y*(gaussianHermite (n+1)).eval (ρ*x+s*y))) (gaussianReal 0 1) := hy.const_mul _
    have hC : Integrable (fun y => (n+1:ℝ)*(gaussianHermite n).eval (ρ*x+s*y)) (gaussianReal 0 1) := h0.const_mul _
    have hAB : Integrable (fun y => ρ*x*(gaussianHermite (n+1)).eval (ρ*x+s*y)+s*(y*(gaussianHermite (n+1)).eval (ρ*x+s*y))) (gaussianReal 0 1) := hA.add hB
    rw [he,integral_sub hAB hC,
      integral_add hA hB,integral_const_mul,integral_const_mul,
      integral_const_mul,standardGaussian_affine_hermite_stein,hn,hn1]
    rw [show n+2=(n+1)+1 by omega,gaussianHermite_succ (n+1),gaussianHermite_derivative_succ]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,pow_succ]
    have hs : s*s=1-ρ*ρ := by nlinarith [h]
    linear_combination (n+1)*ρ^n*(gaussianHermite n).eval x*h

end Hurst
