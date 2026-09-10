import Hurst.GaussianCompleteness
import Hurst.HermiteSpan

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
namespace Hurst

def gaussianPolynomialPairing (f : ℝ → ℝ) (hf : MemLp f 2 (gaussianReal 0 1)) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x,f x*p.eval x ∂gaussianReal 0 1
  map_add' p q := by
    simp only [Polynomial.eval_add,mul_add]
    apply integral_add
    · exact hf.integrable_mul (standardGaussian_polynomial_memLp_two p)
    · exact hf.integrable_mul (standardGaussian_polynomial_memLp_two q)
  map_smul' c p := by
    simp only [Polynomial.eval_smul,smul_eq_mul,RingHom.id_apply]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring

theorem standardGaussian_L2_hermite_total {f : ℝ → ℝ}
    (hf : MemLp f 2 (gaussianReal 0 1))
    (hm : ∀ n : ℕ, (∫ x : ℝ,f x*(gaussianHermite n).eval x ∂gaussianReal 0 1)=0) :
    f =ᵐ[gaussianReal 0 1] 0 := by
  let T := gaussianPolynomialPairing f hf
  have hspan : Submodule.span ℝ (Set.range gaussianHermite) ≤ T.ker := by
    apply Submodule.span_le.mpr
    rintro p ⟨n,rfl⟩
    exact hm n
  rw [gaussianHermite_span_eq_top] at hspan
  apply standardGaussian_L2_moment_total hf
  intro n
  have he := hspan (show (X:Polynomial ℝ)^n ∈ (⊤:Submodule ℝ (Polynomial ℝ)) by trivial)
  change (∫ x,f x*(((X:Polynomial ℝ)^n).eval x) ∂gaussianReal 0 1)=0 at he
  simpa only [Polynomial.eval_pow,Polynomial.eval_X] using he

end Hurst
