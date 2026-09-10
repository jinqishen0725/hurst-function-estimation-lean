import Hurst.HermiteConditional
import Hurst.GaussianPolynomialLaw
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
namespace Hurst

def gaussianAffinePairMap (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem standardGaussian_pair_polynomial_integrable (p q : Polynomial ℝ) (a b : ℝ) :
    Integrable (fun z : ℝ × ℝ => p.eval z.1*q.eval (a*z.1+b*z.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hG : HasGaussianLaw (fun z : ℝ × ℝ => z)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := IsGaussian.hasGaussianLaw_id
  have hX := hG.fst
  have hY : HasGaussianLaw (fun z : ℝ × ℝ => a*z.1+b*z.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa [gaussianAffinePairMap] using hG.map_fun (gaussianAffinePairMap a b)
  exact (gaussianLaw_polynomial_memLp_two hX p).integrable_mul (gaussianLaw_polynomial_memLp_two hY q)

theorem standardGaussian_pair_hermite (n m : ℕ) (ρ s : ℝ) (h : ρ^2+s^2=1) :
    (∫ z : ℝ × ℝ,(gaussianHermite n).eval z.1*(gaussianHermite m).eval (ρ*z.1+s*z.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
      if n=m then (n.factorial:ℝ)*ρ^n else 0 := by
  rw [integral_prod _ (standardGaussian_pair_polynomial_integrable _ _ _ _)]
  simp only [integral_const_mul,standardGaussian_conditional_hermite m ρ s _ h]
  have he : (fun x => (gaussianHermite n).eval x*(ρ^m*(gaussianHermite m).eval x)) =
      fun x => ρ^m*((gaussianHermite n).eval x*(gaussianHermite m).eval x) := by funext x; ring
  rw [he,integral_const_mul,standardGaussian_hermite_orthogonality]
  split_ifs with hnm
  · subst m
    ring
  · ring

end Hurst
