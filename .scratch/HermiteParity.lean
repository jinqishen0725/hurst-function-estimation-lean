import Hurst.GaussianHermite

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
namespace Hurst

theorem gaussianHermite_eval_neg (n : ℕ) (x : ℝ) :
    (gaussianHermite n).eval (-x) = (-1:ℝ)^n*(gaussianHermite n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gaussianHermite_zero]
  | one => simp [gaussianHermite_one]
  | more n hn hn1 =>
    rw [show n+2=(n+1)+1 by omega,gaussianHermite_succ (n+1),gaussianHermite_derivative_succ]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,hn,hn1,pow_succ]
    ring

theorem standardGaussian_odd_integral (F : ℝ → ℝ) (hF : ∀ x, F (-x) = -F x) :
    (∫ x,F x ∂gaussianReal 0 1)=0 := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨by fun_prop,by simp only [gaussianReal_map_neg,neg_zero]⟩
  have he := hmp.integral_comp (Homeomorph.neg ℝ).measurableEmbedding F
  simp only [hF,integral_neg] at he
  linarith

theorem standardGaussian_even_odd_hermite (f : ℝ → ℝ) (hf : ∀ x,f (-x)=f x)
    (n : ℕ) (hn : Odd n) :
    (∫ x,f x*(gaussianHermite n).eval x ∂gaussianReal 0 1)=0 := by
  apply standardGaussian_odd_integral
  intro x
  rw [hf,gaussianHermite_eval_neg,hn.neg_one_pow]
  ring

end Hurst
