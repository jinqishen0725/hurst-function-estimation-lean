import Hurst.GaussianPolynomial
import Hurst.HermiteAlgebra

noncomputable section
open Set MeasureTheory Polynomial
namespace Hurst

def polynomialGaussianIntegral (p : Polynomial ℝ) : ℝ := ∫ x : ℝ, p.eval x*gaussianWeight x

theorem polynomialGaussianIntegral_add (p q : Polynomial ℝ) :
    polynomialGaussianIntegral (p+q) = polynomialGaussianIntegral p+polynomialGaussianIntegral q := by
  unfold polynomialGaussianIntegral
  simp only [Polynomial.eval_add,add_mul]
  exact integral_add (polynomial_gaussian_integrable p) (polynomial_gaussian_integrable q)

theorem polynomialGaussianIntegral_sub (p q : Polynomial ℝ) :
    polynomialGaussianIntegral (p-q) = polynomialGaussianIntegral p-polynomialGaussianIntegral q := by
  unfold polynomialGaussianIntegral
  simp only [Polynomial.eval_sub,sub_mul]
  exact integral_sub (polynomial_gaussian_integrable p) (polynomial_gaussian_integrable q)

theorem polynomialGaussianIntegral_C_mul (c : ℝ) (p : Polynomial ℝ) :
    polynomialGaussianIntegral (Polynomial.C c*p) = c*polynomialGaussianIntegral p := by
  unfold polynomialGaussianIntegral
  simp only [Polynomial.eval_mul,Polynomial.eval_C,mul_assoc]
  exact integral_const_mul _ _

theorem polynomialGaussianIntegral_X_mul (p : Polynomial ℝ) :
    polynomialGaussianIntegral (Polynomial.X*p) = polynomialGaussianIntegral p.derivative := by
  simpa only [polynomialGaussianIntegral,Polynomial.eval_mul,Polynomial.eval_X] using (polynomial_gaussian_stein p).symm

theorem polynomialGaussianIntegral_one : polynomialGaussianIntegral 1 = Real.sqrt (2*Real.pi) := by
  simpa [polynomialGaussianIntegral,gaussianWeight,div_eq_mul_inv,mul_comm] using integral_gaussian (1/2:ℝ)

theorem polynomialGaussianIntegral_zero : polynomialGaussianIntegral 0 = 0 := by simp [polynomialGaussianIntegral]

theorem polynomialGaussianIntegral_adjoint (p q : Polynomial ℝ) :
    polynomialGaussianIntegral ((Polynomial.X*p-p.derivative)*q) =
      polynomialGaussianIntegral (p*q.derivative) := by
  have he : (Polynomial.X*p-p.derivative)*q = Polynomial.X*(p*q)-(p*q).derivative+p*q.derivative := by
    rw [Polynomial.derivative_mul]
    ring
  rw [he,polynomialGaussianIntegral_add,polynomialGaussianIntegral_sub,polynomialGaussianIntegral_X_mul,sub_self,zero_add]

theorem gaussianHermite_integral_succ (n : ℕ) : polynomialGaussianIntegral (gaussianHermite (n+1)) = 0 := by
  rw [gaussianHermite_succ]
  have he := polynomialGaussianIntegral_adjoint (gaussianHermite n) 1
  simpa [polynomialGaussianIntegral_zero] using he

theorem gaussianHermite_orthogonality (n m : ℕ) :
    polynomialGaussianIntegral (gaussianHermite n*gaussianHermite m) =
      if n=m then (n.factorial:ℝ)*Real.sqrt (2*Real.pi) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [gaussianHermite_zero,polynomialGaussianIntegral_one]
    | succ m => simp [gaussianHermite_zero,gaussianHermite_integral_succ]
  | succ n ih =>
    rw [gaussianHermite_succ n,polynomialGaussianIntegral_adjoint]
    cases m with
    | zero => simp [gaussianHermite_zero,polynomialGaussianIntegral_zero]
    | succ m =>
      rw [gaussianHermite_derivative_succ]
      rw [show gaussianHermite n*(Polynomial.C (m+1:ℝ)*gaussianHermite m) =
        Polynomial.C (m+1:ℝ)*(gaussianHermite n*gaussianHermite m) by ring,
        polynomialGaussianIntegral_C_mul,ih]
      by_cases h : n=m
      · subst m
        simp [Nat.factorial_succ]
        ring
      · simp [h]

end Hurst
