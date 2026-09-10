import Hurst.GaussianLog
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Hurst

def gaussianVarianceRatio (v x : ℝ) : ℝ :=
  (Real.sqrt v)⁻¹ * Real.exp ((1 - v⁻¹) * x ^ 2 / 2)

theorem gaussianVarianceRatio_pos (v x : ℝ) (hv : 0 < v) : 0 < gaussianVarianceRatio v x := by
  unfold gaussianVarianceRatio
  positivity

theorem gaussianVarianceRatio_even (v x : ℝ) : gaussianVarianceRatio v (-x) = gaussianVarianceRatio v x := by
  simp [gaussianVarianceRatio]

theorem gaussianVarianceRatio_density (v x : ℝ) (hv : 0 < v) :
    gaussianPDFReal 0 1 x * gaussianVarianceRatio v x = gaussianPDFReal 0 ⟨v, hv.le⟩ x := by
  unfold gaussianPDFReal gaussianVarianceRatio
  simp only [NNReal.coe_one, sub_zero, mul_one]
  change (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
    ((Real.sqrt v)⁻¹ * Real.exp ((1 - v⁻¹) * x ^ 2 / 2)) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x ^ 2) / (2 * v))
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have he : -(x ^ 2) / 2 + (1 - v⁻¹) * x ^ 2 / 2 = -(x ^ 2) / (2 * v) := by ring
  calc
    _ = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt v)⁻¹) *
      (Real.exp (-(x ^ 2) / 2) * Real.exp ((1 - v⁻¹) * x ^ 2 / 2)) := by ring
    _ = _ := by rw [← Real.exp_add, he, mul_inv_rev]; ring

theorem gaussianVarianceRatio_integral (v : ℝ) (hv : 0 < v) :
    (∫ x, gaussianVarianceRatio v x ∂gaussianReal 0 1) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, gaussianVarianceRatio_density v _ hv]
  exact integral_gaussianPDFReal_eq_one 0 (show (⟨v, hv.le⟩ : ℝ≥0) ≠ 0 by intro he; have : v = 0 := congrArg Subtype.val he; linarith)

theorem gaussianVarianceRatio_integrable (v : ℝ) (hv : 0 < v) :
    Integrable (gaussianVarianceRatio v) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simpa only [toReal_gaussianPDF, smul_eq_mul, gaussianVarianceRatio_density v _ hv] using
    integrable_gaussianPDFReal 0 ⟨v, hv.le⟩

/-- Product of variance likelihood ratios is another such ratio, times an explicit constant. -/
theorem gaussianVarianceRatio_product (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : c⁻¹ = a⁻¹ + b⁻¹ - 1) :
    gaussianVarianceRatio a x * gaussianVarianceRatio b x =
      (Real.sqrt c / (Real.sqrt a * Real.sqrt b)) * gaussianVarianceRatio c x := by
  unfold gaussianVarianceRatio
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have he : (1 - a⁻¹) * x ^ 2 / 2 + (1 - b⁻¹) * x ^ 2 / 2 = (1 - c⁻¹) * x ^ 2 / 2 := by
    rw [habc]
    ring
  calc
    _ = ((Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹) *
      (Real.exp ((1 - a⁻¹) * x ^ 2 / 2) * Real.exp ((1 - b⁻¹) * x ^ 2 / 2)) := by ring
    _ = _ := by
      rw [← Real.exp_add, he]
      field_simp

theorem gaussianVarianceRatio_overlap (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : c⁻¹ = a⁻¹ + b⁻¹ - 1) :
    (∫ x, gaussianVarianceRatio a x * gaussianVarianceRatio b x ∂gaussianReal 0 1) =
      Real.sqrt c / (Real.sqrt a * Real.sqrt b) := by
  simp_rw [gaussianVarianceRatio_product a b c _ ha hb hc habc]
  rw [integral_const_mul, gaussianVarianceRatio_integral c hc, mul_one]

theorem gaussianVarianceRatio_product_integrable (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : c⁻¹ = a⁻¹ + b⁻¹ - 1) :
    Integrable (fun x => gaussianVarianceRatio a x * gaussianVarianceRatio b x) (gaussianReal 0 1) := by
  simp_rw [gaussianVarianceRatio_product a b c _ ha hb hc habc]
  exact (gaussianVarianceRatio_integrable c hc).const_mul _

theorem gaussianVarianceRatio_overlap_closed (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < a + b - a * b) :
    (∫ x, gaussianVarianceRatio a x * gaussianVarianceRatio b x ∂gaussianReal 0 1) =
      (Real.sqrt (a + b - a * b))⁻¹ := by
  let c := a * b / (a + b - a * b)
  have hc : 0 < c := by dsimp [c]; positivity
  have he : c⁻¹ = a⁻¹ + b⁻¹ - 1 := by
    dsimp [c]
    field_simp
    ring
  rw [gaussianVarianceRatio_overlap a b c ha hb hc he]
  dsimp [c]
  rw [Real.sqrt_div (mul_nonneg ha.le hb.le), Real.sqrt_mul ha.le]
  have hsa := (Real.sqrt_pos.mpr ha).ne'
  have hsb := (Real.sqrt_pos.mpr hb).ne'
  field_simp

theorem gaussianVarianceRatio_product_integrable_closed (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < a + b - a * b) :
    Integrable (fun x => gaussianVarianceRatio a x * gaussianVarianceRatio b x) (gaussianReal 0 1) := by
  apply gaussianVarianceRatio_product_integrable a b (a * b / (a + b - a * b)) ha hb (by positivity)
  field_simp
  ring

theorem gaussianVarianceRatio_memLp_two (a : ℝ) (ha : 0 < a) (ha2 : a < 2) :
    MemLp (gaussianVarianceRatio a) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by unfold gaussianVarianceRatio; fun_prop)).mpr
  simpa only [pow_two] using gaussianVarianceRatio_product_integrable_closed a a ha ha (by nlinarith)

theorem gaussianVarianceRatio_withDensity (a : ℝ) (ha : 0 < a) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (gaussianVarianceRatio a x)) =
      gaussianReal 0 ⟨a, ha.le⟩ := by
  have hratio : Measurable (fun x => ENNReal.ofReal (gaussianVarianceRatio a x)) := by
    unfold gaussianVarianceRatio
    fun_prop
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, ← withDensity_mul _ (measurable_gaussianPDF 0 1) hratio,
    gaussianReal_of_var_ne_zero 0 (show (⟨a, ha.le⟩ : ℝ≥0) ≠ 0 by intro he; have : a = 0 := congrArg Subtype.val he; linarith)]
  apply withDensity_congr_ae
  filter_upwards [] with x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) * ENNReal.ofReal (gaussianVarianceRatio a x) =
    ENNReal.ofReal (gaussianPDFReal 0 ⟨a, ha.le⟩ x)
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianVarianceRatio_density a x ha]

end Hurst
