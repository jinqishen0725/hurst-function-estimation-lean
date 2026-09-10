import Hurst.GaussianLog
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Asymptotics Polynomial
open scoped Topology
namespace Hurst

def gaussianWeight (x : ℝ) : ℝ := Real.exp (-(1/2:ℝ)*x^2)

theorem polynomial_gaussian_integrable (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x*gaussianWeight x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1 <;> first | rfl | (funext x; simp [Pi.add_apply,mul_add,add_mul])
  | monomial n c =>
    have he := (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
      (show (-1:ℝ) < (n:ℝ) by have := Nat.cast_nonneg (α := ℝ) n; linarith)).const_mul c
    simpa only [Polynomial.eval_monomial,Real.rpow_natCast,mul_assoc,gaussianWeight] using he

theorem polynomial_gaussian_tendsto_atTop (p : Polynomial ℝ) :
    Tendsto (fun x : ℝ => p.eval x*gaussianWeight x) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add,add_mul,add_zero] using hp.add hq
  | monomial n c =>
    have ht : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by norm_num : -(1/2:ℝ) < 0)).mpr tendsto_id)
    have he := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0:ℝ) < 1/2) (n:ℝ)).tendsto_zero_of_tendsto ht
    simpa only [Polynomial.eval_monomial,Real.rpow_natCast,mul_assoc,gaussianWeight,mul_zero] using he.const_mul c

theorem polynomial_gaussian_tendsto_atBot (p : Polynomial ℝ) :
    Tendsto (fun x : ℝ => p.eval x*gaussianWeight x) atBot (𝓝 0) := by
  have ht := (polynomial_gaussian_tendsto_atTop (p.comp (-Polynomial.X))).comp tendsto_neg_atBot_atTop
  change Tendsto (fun x : ℝ => (p.comp (-Polynomial.X)).eval (-x)*gaussianWeight (-x)) atBot (𝓝 0) at ht
  simpa only [Function.comp_apply,Polynomial.eval_comp,Polynomial.eval_neg,Polynomial.eval_X,neg_neg,gaussianWeight,neg_sq] using ht

theorem gaussianWeight_hasDerivAt (x : ℝ) : HasDerivAt gaussianWeight (-x*gaussianWeight x) x := by
  convert ((((hasDerivAt_id x).pow 2).const_mul (-(1/2:ℝ))).exp) using 1
  · funext y
    simp [gaussianWeight,Pi.pow_apply]
  · simp [gaussianWeight,Pi.pow_apply]
    ring

theorem polynomial_gaussian_stein (p : Polynomial ℝ) :
    (∫ x : ℝ, p.derivative.eval x*gaussianWeight x) = ∫ x : ℝ, x*p.eval x*gaussianWeight x := by
  have h1 := polynomial_gaussian_integrable p.derivative
  have h2 : Integrable (fun x : ℝ => x*p.eval x*gaussianWeight x) := by
    have he := polynomial_gaussian_integrable (Polynomial.X*p)
    convert he using 1
    funext x
    simp
  have hd := integral_deriv_mul_eq_sub
    (u := fun x => p.eval x) (u' := fun x => p.derivative.eval x)
    (v := gaussianWeight) (v' := fun x => -x*gaussianWeight x)
    (fun x _ => p.hasDerivAt x) (fun x _ => gaussianWeight_hasDerivAt x)
    (by
      convert h1.sub h2 using 1
      funext x
      simp only [Pi.add_apply,Pi.mul_apply,Pi.sub_apply]
      ring)
    (polynomial_gaussian_tendsto_atBot p) (polynomial_gaussian_tendsto_atTop p)
  have hid : (fun x : ℝ => p.derivative.eval x*gaussianWeight x+p.eval x*(-x*gaussianWeight x)) =
      (fun x : ℝ => p.derivative.eval x*gaussianWeight x-x*p.eval x*gaussianWeight x) := by funext x; ring
  rw [hid,integral_sub h1 h2] at hd
  linarith

end Hurst
