import Hurst.GaussianFinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual one-dimensional harmonizable features from files 05 and 09.
The complex-valued L² space will be used as a real Hilbert space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Hurst

def rawHarmonizable (h t x : ℝ) : ℂ :=
  (Complex.exp (Complex.I * (t * x : ℝ)) - 1) / (|x| ^ (h + 1 / 2) : ℝ)

theorem rawHarmonizable_measurable (h t : ℝ) : Measurable (rawHarmonizable h t) := by
  unfold rawHarmonizable
  fun_prop

theorem rawHarmonizable_norm_sq (h t x : ℝ) :
    ‖rawHarmonizable h t x‖ ^ 2 =
      ‖Complex.exp (Complex.I * (t * x : ℝ)) - 1‖ ^ 2 / |x| ^ (2 * h + 1) := by
  unfold rawHarmonizable
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), div_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  ring

theorem rawHarmonizable_norm_sq_even (h t x : ℝ) :
    ‖rawHarmonizable h t (-x)‖ ^ 2 = ‖rawHarmonizable h t x‖ ^ 2 := by
  simp only [rawHarmonizable_norm_sq, abs_neg, mul_neg,
    Complex.norm_exp_I_mul_ofReal_sub_one, neg_div, Real.sin_neg, mul_neg, norm_neg]

/-- The precise integrable power controlling the origin. -/
theorem rawHarmonizable_norm_sq_near (h t x : ℝ) (hx : 0 < x) :
    ‖rawHarmonizable h t x‖ ^ 2 ≤ t ^ 2 * x ^ (1 - 2 * h) := by
  have hn := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * x)
  have hs := mul_self_le_mul_self (norm_nonneg _) hn
  have hs' : ‖Complex.exp (Complex.I * (t * x : ℝ)) - 1‖ ^ 2 ≤ t ^ 2 * x ^ 2 := by
    simpa only [← sq, Real.norm_eq_abs, sq_abs, mul_pow] using hs
  rw [rawHarmonizable_norm_sq, abs_of_pos hx]
  calc
    _ ≤ (t ^ 2 * x ^ 2) / x ^ (2 * h + 1) :=
      div_le_div_of_nonneg_right hs' (Real.rpow_nonneg hx.le _)
    _ = t ^ 2 * x ^ (1 - 2 * h) := by
      rw [mul_div_assoc, ← Real.rpow_natCast x 2, ← Real.rpow_sub hx]
      congr 2
      ring

/-- The precise integrable power controlling infinity. -/
theorem rawHarmonizable_norm_sq_far (h t x : ℝ) (hx : 0 < x) :
    ‖rawHarmonizable h t x‖ ^ 2 ≤ 4 * x ^ (-1 - 2 * h) := by
  have hn : ‖Complex.exp (Complex.I * (t * x : ℝ)) - 1‖ ≤ 2 := by
    have hn := norm_sub_le (Complex.exp (Complex.I * (t * x : ℝ))) (1 : ℂ)
    simpa only [Complex.norm_exp_I_mul_ofReal, norm_one, one_add_one_eq_two] using hn
  have hs : ‖Complex.exp (Complex.I * (t * x : ℝ)) - 1‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (Complex.exp (Complex.I * (t * x : ℝ)) - 1)]
  rw [rawHarmonizable_norm_sq, abs_of_pos hx]
  calc
    _ ≤ 4 / x ^ (2 * h + 1) := div_le_div_of_nonneg_right hs (Real.rpow_nonneg hx.le _)
    _ = 4 * x ^ (-1 - 2 * h) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
      congr 2
      ring

/-- Membership in L² is proved for the paper's actual exponential feature. -/
theorem rawHarmonizable_memLp (h t : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    MemLp (rawHarmonizable h t) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (rawHarmonizable_measurable h t).aestronglyMeasurable).mpr
  have hm : AEStronglyMeasurable (fun x => ‖rawHarmonizable h t x‖ ^ 2) volume :=
    ((rawHarmonizable_measurable h t).norm.pow_const 2).aestronglyMeasurable
  have hpos : IntegrableOn (fun x => ‖rawHarmonizable h t x‖ ^ 2) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) (by norm_num), integrableOn_union]
    constructor
    · have hi : IntegrableOn (fun x : ℝ => x ^ (1 - 2 * h)) (Ioc 0 1) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
      apply (hi.const_mul (t ^ 2)).mono' hm.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      simpa only [Real.norm_eq_abs, abs_sq] using
        rawHarmonizable_norm_sq_near h t x hx.1
    · have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - 2 * h < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul 4
      apply hi.mono' hm.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [Real.norm_eq_abs, abs_sq] using
        rawHarmonizable_norm_sq_far h t x (lt_trans (by norm_num) hx)
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, rawHarmonizable_norm_sq_even, neg_preimage, neg_Iio,
    neg_zero] using hpos

/-- The cosine spectral density used to define the normalization. -/
def spectralCosineDensity (h t x : ℝ) : ℝ :=
  (1 - Real.cos (t * x)) / |x| ^ (2 * h + 1)

theorem rawHarmonizable_norm_sq_density (h t x : ℝ) :
    ‖rawHarmonizable h t x‖ ^ 2 = 2 * spectralCosineDensity h t x := by
  rw [rawHarmonizable_norm_sq, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, sq_abs]
  have hc := Real.cos_two_mul_eq_one_sub (t * x / 2)
  have he : 2 * (t * x / 2) = t * x := by ring
  rw [he] at hc
  unfold spectralCosineDensity
  rw [hc]
  ring

theorem spectralCosineDensity_nonneg (h t x : ℝ) :
    0 ≤ spectralCosineDensity h t x :=
  div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Real.rpow_nonneg (abs_nonneg _) _)

theorem spectralCosineDensity_integrable (h t : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    Integrable (spectralCosineDensity h t) volume := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (rawHarmonizable_measurable h t).aestronglyMeasurable).mp
    (rawHarmonizable_memLp h t hh hh1)
  apply (hi.const_mul (1 / 2 : ℝ)).congr
  filter_upwards [] with x
  rw [rawHarmonizable_norm_sq_density]
  ring

theorem spectralCosineDensity_integral_pos (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    0 < ∫ x, spectralCosineDensity h 1 x := by
  apply (integral_pos_iff_support_of_nonneg (spectralCosineDensity_nonneg h 1)
    (spectralCosineDensity_integrable h 1 hh hh1)).mpr
  have hs : Ioo (0 : ℝ) Real.pi ⊆ Function.support (spectralCosineDensity h 1) := by
    intro x hx
    apply ne_of_gt
    apply div_pos
    · have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hx.2.le hx.1
      simpa only [Real.cos_zero, one_mul, sub_pos] using hc
    · exact Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_gt hx.1)) _
  exact lt_of_lt_of_le (by simpa using Real.pi_pos : 0 < volume (Ioo (0 : ℝ) Real.pi))
    (measure_mono hs)

def harmonizableD (h : ℝ) : ℝ := Real.sqrt (∫ x, spectralCosineDensity h 1 x)

theorem harmonizableD_pos (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    0 < harmonizableD h := Real.sqrt_pos.mpr (spectralCosineDensity_integral_pos h hh hh1)

theorem harmonizableD_sq (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    harmonizableD h ^ 2 = ∫ x, spectralCosineDensity h 1 x :=
  Real.sq_sqrt (spectralCosineDensity_integral_pos h hh hh1).le

theorem spectralCosineDensity_scale (h t x : ℝ) (ht : t ≠ 0) :
    spectralCosineDensity h t x = |t| ^ (2 * h + 1) * spectralCosineDensity h 1 (t * x) := by
  unfold spectralCosineDensity
  rw [one_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hp : |t| ^ (2 * h + 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr ht) _)
  rw [div_mul_eq_div_div, ← mul_div_assoc, mul_div_cancel₀ _ hp]

theorem spectralCosineDensity_integral_scale (h t : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    (∫ x, spectralCosineDensity h t x) = |t| ^ (2 * h) * harmonizableD h ^ 2 := by
  by_cases ht : t = 0
  · subst t
    simp [spectralCosineDensity, Real.zero_rpow (by linarith : 2 * h ≠ 0)]
  · simp_rw [spectralCosineDensity_scale h t _ ht]
    rw [integral_const_mul, Measure.integral_comp_mul_left, smul_eq_mul,
      ← harmonizableD_sq h hh hh1, abs_inv, Real.rpow_add_one (abs_ne_zero.mpr ht)]
    field_simp

/-- The normalized feature, with the normalization in the written repair. -/
def normalizedHarmonizable (h t : ℝ) : ℝ → ℂ :=
  (Real.sqrt 2 * harmonizableD h)⁻¹ • rawHarmonizable h t

theorem normalizedHarmonizable_memLp (h t : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    MemLp (normalizedHarmonizable h t) 2 volume :=
  (rawHarmonizable_memLp h t hh hh1).const_smul _

def harmonizableFeature (h : Ioo (0 : ℝ) 1) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (normalizedHarmonizable_memLp h t h.property.1 h.property.2).toLp _

theorem harmonizableFeature_ae (h : Ioo (0 : ℝ) 1) (t : ℝ) :
    harmonizableFeature h t =ᵐ[volume] normalizedHarmonizable h t :=
  MemLp.coeFn_toLp _

theorem harmonizableFeature_inner (h k : Ioo (0 : ℝ) 1) (s t : ℝ) :
    ⟪harmonizableFeature h s, harmonizableFeature k t⟫ =
      ∫ x, ⟪normalizedHarmonizable h s x, normalizedHarmonizable k t x⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [harmonizableFeature_ae h s, harmonizableFeature_ae k t] with x hx hy
  rw [hx, hy]

theorem exponential_increment_inner (s t : ℝ) :
    ⟪Complex.exp (Complex.I * (s : ℂ)) - 1,
      Complex.exp (Complex.I * (t : ℂ)) - 1⟫ =
      (1 - Real.cos s) + (1 - Real.cos t) - (1 - Real.cos (s - t)) := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, Complex.exp_re,
    Complex.exp_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, mul_zero, sub_self, zero_add, Real.exp_zero,
    Real.cos_sub]
  ring

theorem rawHarmonizable_smul (h t x : ℝ) :
    rawHarmonizable h t x = (|x| ^ (h + 1 / 2))⁻¹ •
      (Complex.exp (Complex.I * (t * x : ℝ)) - 1) := by
  simp only [rawHarmonizable, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem rawHarmonizable_inner_density (h k s t x : ℝ) :
    ⟪rawHarmonizable h s x, rawHarmonizable k t x⟫ =
      spectralCosineDensity ((h + k) / 2) s x +
      spectralCosineDensity ((h + k) / 2) t x -
      spectralCosineDensity ((h + k) / 2) (s - t) x := by
  by_cases hx : x = 0
  · subst x
    simp [rawHarmonizable, spectralCosineDensity]
  · rw [rawHarmonizable_smul, rawHarmonizable_smul, real_inner_smul_left,
      real_inner_smul_right, exponential_increment_inner]
    have he : |x| ^ (2 * ((h + k) / 2) + 1) =
        |x| ^ (h + 1 / 2) * |x| ^ (k + 1 / 2) := by
      rw [← Real.rpow_add (abs_pos.mpr hx)]
      congr 1
      ring
    dsimp only [spectralCosineDensity]
    rw [he]
    simp only [mul_inv, sub_mul, div_eq_mul_inv]
    ring

theorem normalizedHarmonizable_inner_density (h k : Ioo (0 : ℝ) 1) (s t x : ℝ) :
    ⟪normalizedHarmonizable h s x, normalizedHarmonizable k t x⟫ =
      (2 * harmonizableD h * harmonizableD k)⁻¹ *
      (spectralCosineDensity (((h : ℝ) + k) / 2) s x +
      spectralCosineDensity (((h : ℝ) + k) / 2) t x -
      spectralCosineDensity (((h : ℝ) + k) / 2) (s - t) x) := by
  simp only [normalizedHarmonizable, Pi.smul_apply, real_inner_smul_left,
    real_inner_smul_right, rawHarmonizable_inner_density, mul_inv]
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (by norm_num)]
  calc
    _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * (harmonizableD h)⁻¹ *
        (harmonizableD k)⁻¹ *
        (spectralCosineDensity (((h : ℝ) + k) / 2) s x +
          spectralCosineDensity (((h : ℝ) + k) / 2) t x -
          spectralCosineDensity (((h : ℝ) + k) / 2) (s - t) x) := by ring
    _ = _ := by rw [hs]

/-- Exact covariance kernel for possibly different Hurst parameters. -/
theorem harmonizableFeature_inner_formula (h k : Ioo (0 : ℝ) 1) (s t : ℝ) :
    ⟪harmonizableFeature h s, harmonizableFeature k t⟫ =
      harmonizableD (((h : ℝ) + k) / 2) ^ 2 / (2 * harmonizableD h * harmonizableD k) *
      (|s| ^ ((h : ℝ) + k) + |t| ^ ((h : ℝ) + k) - |s - t| ^ ((h : ℝ) + k)) := by
  have ha : 0 < ((h : ℝ) + k) / 2 := by linarith [h.property.1, k.property.1]
  have hb : ((h : ℝ) + k) / 2 < 1 := by linarith [h.property.2, k.property.2]
  have hi := spectralCosineDensity_integrable (((h : ℝ) + k) / 2)
  rw [harmonizableFeature_inner]
  simp_rw [normalizedHarmonizable_inner_density]
  have hsum : Integrable (fun x => spectralCosineDensity (((h : ℝ) + k) / 2) s x +
      spectralCosineDensity (((h : ℝ) + k) / 2) t x) volume := (hi s ha hb).add (hi t ha hb)
  rw [integral_const_mul, integral_sub hsum (hi (s - t) ha hb),
    integral_add (hi s ha hb) (hi t ha hb)]
  simp_rw [spectralCosineDensity_integral_scale _ _ ha hb]
  have he : 2 * (((h : ℝ) + k) / 2) = (h : ℝ) + k := by ring
  rw [he]
  ring

/-- A concrete finite observation law for a variable Hurst function on a grid. -/
def harmonizableGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → Ioo (0 : ℝ) 1) (t : ι → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  featureGaussian (fun i => harmonizableFeature (h i) (t i))

instance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → Ioo (0 : ℝ) 1) (t : ι → ℝ) : IsGaussian (harmonizableGaussian h t) := by
  unfold harmonizableGaussian
  infer_instance

instance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → Ioo (0 : ℝ) 1) (t : ι → ℝ) : IsProbabilityMeasure (harmonizableGaussian h t) := by
  unfold harmonizableGaussian
  infer_instance

theorem harmonizableGaussian_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → Ioo (0 : ℝ) 1) (t : ι → ℝ) (i j : ι) :
    cov[fun x => x i, fun x => x j; harmonizableGaussian h t] =
      ∫ x, ⟪normalizedHarmonizable (h i) (t i) x,
        normalizedHarmonizable (h j) (t j) x⟫ := by
  rw [harmonizableGaussian, featureGaussian_covariance, harmonizableFeature_inner]

theorem harmonizableFeature_norm_sq (h : Ioo (0 : ℝ) 1) (t : ℝ) :
    ‖harmonizableFeature h t‖ ^ 2 = |t| ^ (2 * (h : ℝ)) := by
  rw [← real_inner_self_eq_norm_sq, harmonizableFeature_inner]
  simp_rw [real_inner_self_eq_norm_sq, normalizedHarmonizable, Pi.smul_apply,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, rawHarmonizable_norm_sq_density]
  simp_rw [← mul_assoc]
  rw [integral_const_mul, spectralCosineDensity_integral_scale h t h.property.1 h.property.2]
  have hd := (harmonizableD_pos h h.property.1 h.property.2).ne'
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [inv_pow, mul_pow, hs]
  field_simp

theorem harmonizableGaussian_coordinate_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → Ioo (0 : ℝ) 1) (t : ι → ℝ) (i : ι) :
    Var[fun x => x i; harmonizableGaussian h t] = |t i| ^ (2 * (h i : ℝ)) := by
  rw [harmonizableGaussian, featureGaussian_coordinate_variance, harmonizableFeature_norm_sq]

theorem harmonizableGaussian_covariance_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → Ioo (0 : ℝ) 1) (t : ι → ℝ) (i j : ι) :
    cov[fun x => x i, fun x => x j; harmonizableGaussian h t] =
      harmonizableD (((h i : ℝ) + h j) / 2) ^ 2 /
        (2 * harmonizableD (h i) * harmonizableD (h j)) *
      (|t i| ^ ((h i : ℝ) + h j) + |t j| ^ ((h i : ℝ) + h j) -
        |t i - t j| ^ ((h i : ℝ) + h j)) := by
  rw [harmonizableGaussian, featureGaussian_covariance, harmonizableFeature_inner_formula]

theorem harmonizableFeature_inner_same (h : Ioo (0 : ℝ) 1) (s t : ℝ) :
    ⟪harmonizableFeature h s, harmonizableFeature h t⟫ =
      (|s| ^ (2 * (h : ℝ)) + |t| ^ (2 * (h : ℝ)) - |s - t| ^ (2 * (h : ℝ))) / 2 := by
  rw [harmonizableFeature_inner_formula]
  have he : ((h : ℝ) + h) / 2 = h := by ring
  rw [he, ← two_mul]
  have hd := (harmonizableD_pos h h.property.1 h.property.2).ne'
  field_simp

theorem harmonizableFeature_increment_norm_sq (h : Ioo (0 : ℝ) 1) (s t : ℝ) :
    ‖harmonizableFeature h s - harmonizableFeature h t‖ ^ 2 = |s - t| ^ (2 * (h : ℝ)) := by
  rw [norm_sub_sq_real, harmonizableFeature_norm_sq, harmonizableFeature_norm_sq,
    harmonizableFeature_inner_same]
  ring

/-- The correctly normalized Brownian reference kernel used for whitening. -/
theorem harmonizableFeature_brownian_inner (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ⟪harmonizableFeature ⟨1 / 2, by norm_num, by norm_num⟩ s,
      harmonizableFeature ⟨1 / 2, by norm_num, by norm_num⟩ t⟫ = min s t := by
  rw [harmonizableFeature_inner_same]
  norm_num
  rw [abs_of_nonneg hs, abs_of_nonneg ht]
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [min_eq_right hts, abs_of_nonneg (sub_nonneg.mpr hts)]
    ring

end Hurst
