import Hurst.GaussianHermite
import Hurst.MomentDetermination
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal
namespace Hurst

theorem standardGaussian_exp_memLp_two (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (t*x)) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (2*t) using 1 <;>
    first | rfl | (funext x; rw [← Real.exp_nat_mul]; congr 1; ring)

theorem memLp_positive_part {μ : Measure ℝ} {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p μ) : MemLp (fun x => max (f x) 0) p μ := by
  apply hf.of_le (hf.1.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  filter_upwards [] with x
  simp only [Real.norm_eq_abs,abs_of_nonneg (le_max_right (f x) 0)]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem standardGaussian_L2_moment_total {f : ℝ → ℝ}
    (hf : MemLp f 2 (gaussianReal 0 1))
    (hm : ∀ n : ℕ, (∫ x : ℝ,f x*x^n ∂gaussianReal 0 1)=0) :
    f =ᵐ[gaussianReal 0 1] 0 := by
  let μ := gaussianReal 0 1
  let u : ℝ → ℝ := fun x => max (f x) 0
  let v : ℝ → ℝ := fun x => max (-f x) 0
  have hu : MemLp u 2 μ := memLp_positive_part hf
  have hv : MemLp v 2 μ := memLp_positive_part hf.neg
  have hu0 (x : ℝ) : 0 ≤ u x := le_max_right _ _
  have hv0 (x : ℝ) : 0 ≤ v x := le_max_right _ _
  let P := μ.withDensity (fun x => ENNReal.ofReal (u x))
  let Q := μ.withDensity (fun x => ENNReal.ofReal (v x))
  haveI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal (hu.integrable (by norm_num)).2
  haveI : IsFiniteMeasure Q := isFiniteMeasure_withDensity_ofReal (hv.integrable (by norm_num)).2
  have hPI (g : ℝ → ℝ) : (∫ x,g x ∂P) = ∫ x,u x*g x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hu.1.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hu0 _),smul_eq_mul]
  have hQI (g : ℝ → ℝ) : (∫ x,g x ∂Q) = ∫ x,v x*g x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hv.1.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hv0 _),smul_eq_mul]
  have hPe (t : ℝ) : Integrable (fun x => Real.exp (t*x)) P := by
    rw [integrable_withDensity_iff_integrable_smul₀' hu.1.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hu0 _),smul_eq_mul]
    exact hu.integrable_mul (standardGaussian_exp_memLp_two t)
  have hQe (t : ℝ) : Integrable (fun x => Real.exp (t*x)) Q := by
    rw [integrable_withDensity_iff_integrable_smul₀' hv.1.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hv0 _),smul_eq_mul]
    exact hv.integrable_mul (standardGaussian_exp_memLp_two t)
  have hPQ : P=Q := by
    apply finite_measure_eq_of_exponential_moments P Q hPe hQe
    intro n
    rw [hPI,hQI]
    have hn : MemLp (fun x : ℝ => x^n) 2 μ := by
      simpa only [Polynomial.eval_pow,Polynomial.eval_X] using
        standardGaussian_polynomial_memLp_two ((X:Polynomial ℝ)^n)
    have hid : (fun x => u x*x^n-v x*x^n) = fun x => f x*x^n := by
      funext x
      dsimp [u,v]
      rw [← sub_mul,max_zero_sub_max_neg_zero_eq_self]
    have hz : (∫ x,u x*x^n ∂μ)-(∫ x,v x*x^n ∂μ)=0 := by
      have hui : Integrable (fun x => u x*x^n) μ := hu.integrable_mul hn
      have hvi : Integrable (fun x => v x*x^n) μ := hv.integrable_mul hn
      rw [← integral_sub hui hvi,hid]
      exact hm n
    exact sub_eq_zero.mp hz
  have he := (withDensity_eq_iff_of_sigmaFinite hu.1.aemeasurable.ennreal_ofReal
    hv.1.aemeasurable.ennreal_ofReal).mp hPQ
  filter_upwards [he] with x hx
  have he' := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal (hu0 _),ENNReal.toReal_ofReal (hv0 _)] at he'
  change f x=0
  dsimp [u,v] at he'
  have hzero := max_zero_sub_max_neg_zero_eq_self (f x)
  rw [he',sub_self] at hzero
  exact hzero.symm

end Hurst
