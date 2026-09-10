import Hurst.GaussianLogHermite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial Filter Asymptotics
open scoped Topology
namespace Hurst

theorem standardGaussian_integrable_weight {F : ℝ → ℝ}
    (hF : Integrable F (gaussianReal 0 1)) : Integrable (fun x => F x*gaussianWeight x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hF
  simp only [toReal_gaussianPDF,smul_eq_mul,standardGaussian_density_weight] at hF
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  convert hF.const_mul (Real.sqrt (2*Real.pi)) using 1 <;> first | rfl |
    (funext x; field_simp)

def gaussianLogSteinPrimitive (x : ℝ) : ℝ := x*Real.log (x^2)*gaussianWeight x

def gaussianLogSteinDerivative (x : ℝ) : ℝ :=
  (2+Real.log (x^2)*(1-x^2))*gaussianWeight x

theorem gaussianLogSteinPrimitive_continuous : Continuous gaussianLogSteinPrimitive := by
  have he : gaussianLogSteinPrimitive = fun x => 2*(x*Real.log x)*gaussianWeight x := by
    funext x
    simp only [gaussianLogSteinPrimitive,Real.log_pow,Nat.cast_ofNat]
    ring
  rw [he]
  exact (continuous_const.mul Real.continuous_mul_log).mul (by unfold gaussianWeight; fun_prop)

theorem gaussianLogSteinPrimitive_derivative (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt gaussianLogSteinPrimitive (gaussianLogSteinDerivative x) x := by
  have hd := ((hasDerivAt_id x).mul (((hasDerivAt_id x).pow 2).log (pow_ne_zero 2 hx))).mul
    (gaussianWeight_hasDerivAt x)
  convert hd using 1 <;> first | rfl | (funext y; rfl) |
    (simp only [gaussianLogSteinDerivative,Pi.pow_apply,Pi.mul_apply,id_eq]
     field_simp
     ring)

theorem gaussianLogSteinPrimitive_tendsto :
    Tendsto gaussianLogSteinPrimitive atTop (𝓝 0) := by
  have hl : (fun x : ℝ => Real.log x) =O[atTop] (fun x => x) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1)).isBigO
  have hh := hl.mul (isBigO_refl (fun x : ℝ => x*gaussianWeight x) atTop)
  have hz : Tendsto (fun x : ℝ => x*(x*gaussianWeight x)) atTop (𝓝 0) := by
    convert polynomial_gaussian_tendsto_atTop ((X:Polynomial ℝ)^2) using 1
    funext x
    simp only [Polynomial.eval_pow,Polynomial.eval_X]
    ring
  have ht := (hh.trans_tendsto hz).const_mul 2
  convert ht using 1
  · funext x
    simp only [gaussianLogSteinPrimitive,Real.log_pow,Nat.cast_ofNat]
    ring
  · ring

theorem gaussianLogSteinDerivative_integrable : Integrable gaussianLogSteinDerivative := by
  have hi : Integrable (fun x : ℝ => Real.log (x^2)*(1-x^2)) (gaussianReal 0 1) := by
    have hp := standardGaussian_polynomial_memLp_two (1-(X:Polynomial ℝ)^2)
    have he := (log_square_memLp_two_gaussianReal 1 one_ne_zero).integrable_mul hp
    convert he using 1 <;> first | rfl | (funext x; simp)
  have h2 := standardGaussian_integrable_weight ((integrable_const 2).add hi)
  convert h2 using 1 <;> first | rfl | (funext x; rfl)

theorem gaussianLogSteinDerivative_integral : (∫ x,gaussianLogSteinDerivative x)=0 := by
  have hz := integral_Ioi_of_hasDerivAt_of_tendsto
    (gaussianLogSteinPrimitive_continuous.continuousAt.continuousWithinAt (x := 0) (s := Ici 0))
    (fun x hx => gaussianLogSteinPrimitive_derivative x (ne_of_gt hx))
    (gaussianLogSteinDerivative_integrable.restrict) gaussianLogSteinPrimitive_tendsto
  simp only [gaussianLogSteinPrimitive,zero_mul,sub_zero] at hz
  have ha : (fun x => gaussianLogSteinDerivative |x|) = gaussianLogSteinDerivative := by
    funext x
    simp [gaussianLogSteinDerivative,gaussianWeight,sq_abs]
  rw [← ha,integral_comp_abs,hz,mul_zero]

end Hurst
