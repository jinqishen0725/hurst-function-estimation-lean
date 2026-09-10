import Hurst.HermiteOrthogonality

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
namespace Hurst

theorem standardGaussian_density_weight (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2*Real.pi))⁻¹*gaussianWeight x := by
  unfold gaussianPDFReal gaussianWeight
  simp only [NNReal.coe_one,sub_zero,mul_one]
  congr 2
  ring

theorem standardGaussian_weight_integral (F : ℝ → ℝ) :
    (∫ x,F x ∂gaussianReal 0 1) = (Real.sqrt (2*Real.pi))⁻¹*(∫ x,F x*gaussianWeight x) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smul_eq_mul,standardGaussian_density_weight]
  ring

theorem standardGaussian_polynomial_integrable (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF,smul_eq_mul,standardGaussian_density_weight]
  convert (polynomial_gaussian_integrable p).const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
  congr 1
  funext x
  ring

theorem standardGaussian_polynomial_memLp_two (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => p.eval x) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq p.continuous.aestronglyMeasurable).mpr
  convert standardGaussian_polynomial_integrable (p^2) using 1 <;> first | rfl | (funext x; simp)

theorem standardGaussian_hermite_orthogonality (n m : ℕ) :
    (∫ x : ℝ,(gaussianHermite n).eval x*(gaussianHermite m).eval x ∂gaussianReal 0 1) =
      if n=m then (n.factorial:ℝ) else 0 := by
  rw [standardGaussian_weight_integral]
  have he : (∫ x : ℝ,(gaussianHermite n).eval x*(gaussianHermite m).eval x*gaussianWeight x) =
      polynomialGaussianIntegral (gaussianHermite n*gaussianHermite m) := by
    simp only [polynomialGaussianIntegral,Polynomial.eval_mul]
  rw [he,gaussianHermite_orthogonality]
  split_ifs
  · have hs : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  · ring

theorem standardGaussian_hermite_mean_succ (n : ℕ) :
    (∫ x : ℝ,(gaussianHermite (n+1)).eval x ∂gaussianReal 0 1) = 0 := by
  simpa [gaussianHermite_zero] using standardGaussian_hermite_orthogonality (n+1) 0

end Hurst
