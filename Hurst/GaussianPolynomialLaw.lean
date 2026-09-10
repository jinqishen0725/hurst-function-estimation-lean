import Hurst.GaussianHermite
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal
namespace Hurst

theorem gaussianLaw_polynomial_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P)
    (p : Polynomial ℝ) : Integrable (fun ω => p.eval (X ω)) P := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1 <;> first | rfl | (funext ω; simp)
  | monomial n c =>
    have hn := (hX.memLp (p := (n:ℝ≥0∞)) (by simp)).integrable_norm_pow'
    have hi : Integrable (fun ω => (X ω)^n) P := by
      apply hn.mono' (hX.aemeasurable.pow_const n).aestronglyMeasurable
      filter_upwards [] with ω
      simp only [norm_pow,le_refl]
    simpa only [Polynomial.eval_monomial] using hi.const_mul c

theorem gaussianLaw_polynomial_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P)
    (p : Polynomial ℝ) : MemLp (fun ω => p.eval (X ω)) 2 P := by
  apply (memLp_two_iff_integrable_sq (p.continuous.comp_aestronglyMeasurable hX.aemeasurable.aestronglyMeasurable)).mpr
  convert gaussianLaw_polynomial_integrable hX (p^2) using 1 <;>
    first | rfl | (funext ω; simp)

end Hurst
