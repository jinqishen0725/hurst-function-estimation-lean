import Hurst.GaussianOverlap
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Hurst

def gaussianProduct2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
instance gaussianProduct2_isProbability : IsProbabilityMeasure gaussianProduct2 := by
  unfold gaussianProduct2
  infer_instance

def diagonalGaussianRatio (a b : ℝ) (z : ℝ × ℝ) : ℝ :=
  gaussianVarianceRatio a z.1 * gaussianVarianceRatio b z.2

theorem diagonalGaussianRatio_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ z, diagonalGaussianRatio a b z ∂gaussianProduct2) = 1 := by
  unfold diagonalGaussianRatio gaussianProduct2
  rw [integral_prod_mul (gaussianVarianceRatio a) (gaussianVarianceRatio b),
    gaussianVarianceRatio_integral a ha, gaussianVarianceRatio_integral b hb, mul_one]

theorem diagonalGaussianRatio_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (diagonalGaussianRatio a b) gaussianProduct2 :=
  (gaussianVarianceRatio_integrable a ha).mul_prod (gaussianVarianceRatio_integrable b hb)

theorem diagonalGaussianRatio_product_integrable (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hac : 0 < a + c - a * c) (hbd : 0 < b + d - b * d) :
    Integrable (fun z => diagonalGaussianRatio a b z * diagonalGaussianRatio c d z) gaussianProduct2 := by
  convert! (gaussianVarianceRatio_product_integrable_closed a c ha hc hac).mul_prod
    (gaussianVarianceRatio_product_integrable_closed b d hb hd hbd) using 1
  funext z
  unfold diagonalGaussianRatio
  ring

theorem diagonalGaussianRatio_overlap (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hac : 0 < a + c - a * c) (hbd : 0 < b + d - b * d) :
    (∫ z, diagonalGaussianRatio a b z * diagonalGaussianRatio c d z ∂gaussianProduct2) =
      (Real.sqrt (a + c - a * c))⁻¹ * (Real.sqrt (b + d - b * d))⁻¹ := by
  have he : (fun z => diagonalGaussianRatio a b z * diagonalGaussianRatio c d z) =
      (fun z : ℝ × ℝ => (gaussianVarianceRatio a z.1 * gaussianVarianceRatio c z.1) *
        (gaussianVarianceRatio b z.2 * gaussianVarianceRatio d z.2)) := by
    funext z
    unfold diagonalGaussianRatio
    ring
  rw [he, gaussianProduct2, integral_prod_mul
    (fun x => gaussianVarianceRatio a x * gaussianVarianceRatio c x)
    (fun x => gaussianVarianceRatio b x * gaussianVarianceRatio d x),
    gaussianVarianceRatio_overlap_closed a c ha hc hac,
    gaussianVarianceRatio_overlap_closed b d hb hd hbd]

def correlationDiagonalRatio (ρ : ℝ) : ℝ × ℝ → ℝ := diagonalGaussianRatio (1 + ρ) (1 - ρ)

theorem correlationDiagonalRatio_integral (ρ : ℝ) (hρ : |ρ| < 1) :
    (∫ z, correlationDiagonalRatio ρ z ∂gaussianProduct2) = 1 :=
  diagonalGaussianRatio_integral _ _ (by linarith [(abs_lt.mp hρ).1]) (by linarith [(abs_lt.mp hρ).2])

theorem correlationDiagonalRatio_square_integral (ρ : ℝ) (hρ : |ρ| < 1) :
    (∫ z, (correlationDiagonalRatio ρ z) ^ 2 ∂gaussianProduct2) = (1 - ρ ^ 2)⁻¹ := by
  have hs : 0 < 1 - ρ ^ 2 := by nlinarith [(abs_lt.mp hρ).1, (abs_lt.mp hρ).2]
  have ha : 0 < 1 + ρ := by linarith [(abs_lt.mp hρ).1]
  have hb : 0 < 1 - ρ := by linarith [(abs_lt.mp hρ).2]
  conv_lhs => simp only [correlationDiagonalRatio, pow_two]
  rw [diagonalGaussianRatio_overlap _ _ _ _ ha hb ha hb (by nlinarith) (by nlinarith)]
  rw [show (1 + ρ) + (1 + ρ) - (1 + ρ) * (1 + ρ) = 1 - ρ ^ 2 by ring,
    show (1 - ρ) + (1 - ρ) - (1 - ρ) * (1 - ρ) = 1 - ρ ^ 2 by ring,
    ← mul_inv_rev, ← pow_two, Real.sq_sqrt hs.le]

theorem correlationDiagonalRatio_cross_integral (ρ : ℝ) (hρ : |ρ| < 1) :
    (∫ z, correlationDiagonalRatio ρ z * correlationDiagonalRatio (-ρ) z ∂gaussianProduct2) =
      (1 + ρ ^ 2)⁻¹ := by
  have ha : 0 < 1 + ρ := by linarith [(abs_lt.mp hρ).1]
  have hb : 0 < 1 - ρ := by linarith [(abs_lt.mp hρ).2]
  simp only [correlationDiagonalRatio, ← sub_eq_add_neg, sub_neg_eq_add]
  rw [diagonalGaussianRatio_overlap _ _ _ _ ha hb hb ha (by nlinarith [sq_nonneg ρ]) (by nlinarith [sq_nonneg ρ])]
  rw [show (1 + ρ) + (1 - ρ) - (1 + ρ) * (1 - ρ) = 1 + ρ ^ 2 by ring,
    show (1 - ρ) + (1 + ρ) - (1 - ρ) * (1 + ρ) = 1 + ρ ^ 2 by ring,
    ← mul_inv_rev, ← pow_two, Real.sq_sqrt (by positivity)]

theorem correlationDiagonalRatio_memLp_two (ρ : ℝ) (hρ : |ρ| < 1) :
    MemLp (correlationDiagonalRatio ρ) 2 gaussianProduct2 := by
  have ha : 0 < 1 + ρ := by linarith [(abs_lt.mp hρ).1]
  have hb : 0 < 1 - ρ := by linarith [(abs_lt.mp hρ).2]
  have hs : 0 < 1 - ρ ^ 2 := by nlinarith [(abs_lt.mp hρ).1, (abs_lt.mp hρ).2]
  apply (memLp_two_iff_integrable_sq (by unfold correlationDiagonalRatio diagonalGaussianRatio gaussianVarianceRatio; fun_prop)).mpr
  simpa only [pow_two, correlationDiagonalRatio] using! diagonalGaussianRatio_product_integrable (1 + ρ) (1 - ρ) (1 + ρ) (1 - ρ)
    ha hb ha hb (by nlinarith) (by nlinarith)

theorem integral_square_half_sum_sub_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ((f x + g x) / 2 - 1) ^ 2 ∂μ) =
      ((∫ x, (f x) ^ 2 ∂μ) + (∫ x, (g x) ^ 2 ∂μ) + 2 * ∫ x, f x * g x ∂μ) / 4 -
        (∫ x, f x ∂μ) - (∫ x, g x ∂μ) + 1 := by
  have hf2 := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hg2 := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hf1 := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg1 := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hAB : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2) μ := hf2.add hg2
  have hA : Integrable (fun x => ((f x) ^ 2 + (g x) ^ 2 + 2 * (f x * g x)) / 4) μ :=
    (hAB.add (hfg.const_mul 2)).div_const 4
  have hB : Integrable (fun x => ((f x) ^ 2 + (g x) ^ 2 + 2 * (f x * g x)) / 4 - f x) μ := hA.sub hf1
  have hC : Integrable (fun x => ((f x) ^ 2 + (g x) ^ 2 + 2 * (f x * g x)) / 4 - f x - g x) μ := hB.sub hg1
  have he : (fun x => ((f x + g x) / 2 - 1) ^ 2) =
      (fun x => (((f x) ^ 2 + (g x) ^ 2 + 2 * (f x * g x)) / 4 - f x) - g x + 1) := by
    funext x
    ring
  rw [he, integral_add hC (integrable_const 1),
    integral_sub hB hg1, integral_sub hA hf1, integral_div,
    integral_add hAB (hfg.const_mul 2), integral_add hf2 hg2, integral_const_mul,
    integral_const]
  simp

def gaussianSymmetricRatio (ρ : ℝ) (z : ℝ × ℝ) : ℝ :=
  (correlationDiagonalRatio ρ z + correlationDiagonalRatio (-ρ) z) / 2

theorem gaussianSymmetricRatio_memLp_two (ρ : ℝ) (hρ : |ρ| < 1) :
    MemLp (gaussianSymmetricRatio ρ) 2 gaussianProduct2 := by
  have hn : |-ρ| < 1 := by simpa only [abs_neg] using hρ
  convert! ((correlationDiagonalRatio_memLp_two ρ hρ).add
    (correlationDiagonalRatio_memLp_two (-ρ) hn)).const_mul (1 / 2 : ℝ) using 1
  funext z
  unfold gaussianSymmetricRatio
  simp only [Pi.add_apply]
  ring

/-- Exact squared density error after symmetrization; the leading order is rho^4. -/
theorem gaussianSymmetricRatio_square_error (ρ : ℝ) (hρ : |ρ| < 1) :
    (∫ z, (gaussianSymmetricRatio ρ z - 1) ^ 2 ∂gaussianProduct2) =
      ρ ^ 4 / (1 - ρ ^ 4) := by
  have hn : |-ρ| < 1 := by simpa only [abs_neg] using hρ
  unfold gaussianSymmetricRatio
  rw [integral_square_half_sum_sub_one gaussianProduct2 _ _
      (correlationDiagonalRatio_memLp_two ρ hρ) (correlationDiagonalRatio_memLp_two (-ρ) hn),
    correlationDiagonalRatio_square_integral ρ hρ,
    correlationDiagonalRatio_square_integral (-ρ) hn,
    correlationDiagonalRatio_cross_integral ρ hρ,
    correlationDiagonalRatio_integral ρ hρ,
    correlationDiagonalRatio_integral (-ρ) hn, neg_sq]
  have h2 : 0 < 1 - ρ ^ 2 := by nlinarith [(abs_lt.mp hρ).1, (abs_lt.mp hρ).2]
  have h4 : 0 < 1 - ρ ^ 4 := by nlinarith [sq_nonneg (ρ ^ 2), sq_nonneg ρ]
  have hp : 0 < 1 + ρ ^ 2 := by positivity
  field_simp
  ring

theorem abs_integral_mul_le_sqrt_integrals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have h : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
    have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
    have h0 := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (h2 ▸ hf) (h2 ▸ hg)
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow] using h0
  calc
    _ ≤ ∫ x, |f x * g x| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [abs_mul, Real.norm_eq_abs]
    _ ≤ _ := h

theorem gaussianSymmetricRatio_small_error (ρ : ℝ) (hρ : |ρ| ≤ 1 / 2) :
    Real.sqrt (∫ z, (gaussianSymmetricRatio ρ z - 1) ^ 2 ∂gaussianProduct2) ≤ 2 * ρ ^ 2 := by
  have hρ1 : |ρ| < 1 := by linarith
  rw [gaussianSymmetricRatio_square_error ρ hρ1, Real.sqrt_le_left (by positivity)]
  have h2 : ρ ^ 2 ≤ 1 / 4 := by nlinarith [(abs_le.mp hρ).1, (abs_le.mp hρ).2]
  have h4 : ρ ^ 4 ≤ 1 / 16 := by nlinarith [sq_nonneg (ρ ^ 2), sq_nonneg ρ]
  apply (div_le_iff₀ (by linarith : 0 < 1 - ρ ^ 4)).mpr
  nlinarith [sq_nonneg (ρ ^ 2), mul_nonneg (show 0 ≤ ρ ^ 4 by positivity) (show 0 ≤ 3 - 4 * ρ ^ 4 by linarith)]

theorem gaussianSymmetricRatio_test_bound (ρ : ℝ) (hρ : |ρ| ≤ 1 / 2)
    (A : ℝ × ℝ → ℝ) (hA : MemLp A 2 gaussianProduct2) :
    |∫ z, A z * (gaussianSymmetricRatio ρ z - 1) ∂gaussianProduct2| ≤
      2 * ρ ^ 2 * Real.sqrt (∫ z, (A z) ^ 2 ∂gaussianProduct2) := by
  have hS := (gaussianSymmetricRatio_memLp_two ρ (by linarith : |ρ| < 1)).sub (memLp_const (1 : ℝ))
  have hCS := abs_integral_mul_le_sqrt_integrals gaussianProduct2 A _ hA hS
  have hbound := gaussianSymmetricRatio_small_error ρ hρ
  calc
    _ ≤ Real.sqrt (∫ z, (A z) ^ 2 ∂gaussianProduct2) *
      Real.sqrt (∫ z, (gaussianSymmetricRatio ρ z - 1) ^ 2 ∂gaussianProduct2) := hCS
    _ ≤ Real.sqrt (∫ z, (A z) ^ 2 ∂gaussianProduct2) * (2 * ρ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem correlationDiagonalRatio_swap (ρ : ℝ) (z : ℝ × ℝ) :
    correlationDiagonalRatio ρ z.swap = correlationDiagonalRatio (-ρ) z := by
  simp only [correlationDiagonalRatio, diagonalGaussianRatio, Prod.fst_swap, Prod.snd_swap,
    sub_neg_eq_add, ← sub_eq_add_neg]
  ring

theorem symmetric_test_reweighting_identity (ρ : ℝ) (hρ : |ρ| < 1)
    (A : ℝ × ℝ → ℝ) (hA : MemLp A 2 gaussianProduct2) (hAsym : ∀ z, A z.swap = A z) :
    (∫ z, A z * (gaussianSymmetricRatio ρ z - 1) ∂gaussianProduct2) =
      (∫ z, A z * correlationDiagonalRatio ρ z ∂gaussianProduct2) - ∫ z, A z ∂gaussianProduct2 := by
  have hR := correlationDiagonalRatio_memLp_two ρ hρ
  have hN := correlationDiagonalRatio_memLp_two (-ρ) (by simpa only [abs_neg] using hρ)
  have hAR : Integrable (fun z => A z * correlationDiagonalRatio ρ z) gaussianProduct2 := hA.integrable_mul hR
  have hAN : Integrable (fun z => A z * correlationDiagonalRatio (-ρ) z) gaussianProduct2 := hA.integrable_mul hN
  have hA1 := hA.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hEq : (∫ z, A z * correlationDiagonalRatio (-ρ) z ∂gaussianProduct2) =
      ∫ z, A z * correlationDiagonalRatio ρ z ∂gaussianProduct2 := by
    have h := integral_prod_swap (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (fun z => A z * correlationDiagonalRatio ρ z)
    simpa only [hAsym, correlationDiagonalRatio_swap, gaussianProduct2] using h
  have hsum : Integrable (fun z => (A z * correlationDiagonalRatio ρ z + A z * correlationDiagonalRatio (-ρ) z) / 2)
      gaussianProduct2 := (hAR.add hAN).div_const 2
  have he : (fun z => A z * (gaussianSymmetricRatio ρ z - 1)) =
      (fun z => (A z * correlationDiagonalRatio ρ z + A z * correlationDiagonalRatio (-ρ) z) / 2 - A z) := by
    funext z
    unfold gaussianSymmetricRatio
    ring
  rw [he, integral_sub hsum hA1, integral_div, integral_add hAR hAN, hEq]
  ring

theorem symmetric_test_reweighting_bound (ρ : ℝ) (hρ : |ρ| ≤ 1 / 2)
    (A : ℝ × ℝ → ℝ) (hA : MemLp A 2 gaussianProduct2) (hAsym : ∀ z, A z.swap = A z) :
    |(∫ z, A z * correlationDiagonalRatio ρ z ∂gaussianProduct2) - ∫ z, A z ∂gaussianProduct2| ≤
      2 * ρ ^ 2 * Real.sqrt (∫ z, (A z) ^ 2 ∂gaussianProduct2) := by
  rw [← symmetric_test_reweighting_identity ρ (by linarith : |ρ| < 1) A hA hAsym]
  exact gaussianSymmetricRatio_test_bound ρ hρ A hA

end Hurst
