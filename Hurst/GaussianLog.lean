import Hurst.GaussianFinite
import Hurst.Moments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Asymptotics

/-! Logarithmic moments for actual Gaussian laws. The singularity at zero is handled
by comparison with an integrable negative power; Gaussian decay handles the tails. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics Set
open scoped Topology ENNReal NNReal RealInnerProductSpace
namespace Hurst

/-- Every natural power of the logarithm is integrable against a Gaussian weight. -/
theorem integrable_log_pow_mul_gaussian (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => (Real.log x) ^ k * Real.exp (-b * x ^ 2)) := by
  have hzero : (fun x : ℝ => (Real.log x) ^ k) =O[𝓝[>] 0]
      (fun x => x ^ (-1 / 2 : ℝ)) := by
    have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ)
      (by norm_num : (-1 / 2 : ℝ) < 0)).isBigO
    apply IsBigO.of_norm_left
    simpa only [Real.rpow_natCast, norm_pow, Real.norm_eq_abs] using h
  have htop : (fun x : ℝ => (Real.log x) ^ k) =O[atTop] (fun x => x ^ (1 : ℝ)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 1)).isBigO
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (Real.log x) ^ k * Real.exp (-b * x ^ 2)) volume := by
    fun_prop
  have hpos : IntegrableOn (fun x : ℝ => (Real.log x) ^ k * Real.exp (-b * x ^ 2))
      (Ioi 0) := by
    rw [integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin]
    refine ⟨?_, ?_, ?_⟩
    · exact (htop.mul (isBigO_refl (fun x => Real.exp (-b * x ^ 2)) atTop)).integrableAtFilter
        hmeas.stronglyMeasurableAtFilter
        ((integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 1)).integrableAtFilter atTop)
    · exact (hzero.mul (isBigO_refl (fun x => Real.exp (-b * x ^ 2)) (𝓝[>] 0))).integrableAtFilter
        hmeas.stronglyMeasurableAtFilter
        ((integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < -1 / 2)).integrableAtFilter (𝓝[>] 0))
    · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
      intro x hx
      exact ((Real.continuousAt_log (ne_of_gt hx)).pow k).mul
        (by fun_prop) |>.continuousWithinAt
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, Real.log_neg_eq_log, neg_sq, neg_preimage, neg_Iio,
    neg_zero] using hpos

/-- Natural logarithmic moments of a centered, nondegenerate Gaussian. -/
theorem integrable_log_pow_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) (k : ℕ) :
    Integrable (fun x : ℝ => (Real.log x) ^ k) (gaussianReal 0 v) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal, sub_zero]
  convert (integrable_log_pow_mul_gaussian k (1 / (2 * (v : ℝ))) (by positivity)).const_mul
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ using 1
  congr 1
  funext x
  rw [show -(x ^ 2) / (2 * (v : ℝ)) = -(1 / (2 * (v : ℝ))) * x ^ 2 by ring]
  ring

/-- Every natural power of log-square is genuinely integrable, including the second moment. -/
theorem integrable_log_square_pow_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) (k : ℕ) :
    Integrable (fun x : ℝ => (Real.log (x ^ 2)) ^ k) (gaussianReal 0 v) := by
  simpa only [Real.log_pow, Nat.cast_ofNat, mul_pow] using
    (integrable_log_pow_gaussianReal v hv k).const_mul ((2 : ℝ) ^ k)

theorem integrable_abs_log_square_pow_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) (k : ℕ) :
    Integrable (fun x : ℝ => |Real.log (x ^ 2)| ^ k) (gaussianReal 0 v) := by
  simpa only [abs_pow] using (integrable_log_square_pow_gaussianReal v hv k).abs

theorem log_square_memLp_two_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) :
    MemLp (fun x : ℝ => Real.log (x ^ 2)) 2 (gaussianReal 0 v) := by
  exact (memLp_two_iff_integrable_sq
    (by exact (by fun_prop : Measurable (fun x : ℝ => Real.log (x ^ 2))).aestronglyMeasurable)).mpr
    (integrable_log_square_pow_gaussianReal v hv 2)

/-- The constant E log(chi-square with one degree of freedom), defined by its actual law. -/
def gaussianLogSquareMean : ℝ := ∫ x : ℝ, Real.log (x ^ 2) ∂gaussianReal 0 1

/-- The corrected expectation identity in Lemma 8.3, with all Gaussian inputs proved. -/
theorem expected_log_square_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x : ℝ, Real.log (x ^ 2) ∂gaussianReal 0 v) =
      Real.log (v : ℝ) + gaussianLogSquareMean := by
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hvpos).ne'
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt (v : ℝ) * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt (le_of_lt hvpos)]
  letI := noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hz : ∀ᵐ x ∂gaussianReal 0 1, (id x : ℝ) ≠ 0 := by
    rw [ae_iff]
    have he : {x : ℝ | ¬ id x ≠ 0} = {0} := by ext x; simp
    rw [he]
    exact measure_singleton 0
  rw [← hmap, integral_map (by fun_prop)
    (by exact (by fun_prop : Measurable (fun x : ℝ => Real.log (x ^ 2))).aestronglyMeasurable)]
  simpa only [id_eq, Real.sq_sqrt (le_of_lt hvpos), gaussianLogSquareMean] using
    expected_log_square_scale id (Real.sqrt (v : ℝ)) hs hz
      (by simpa using integrable_log_square_pow_gaussianReal 1 one_ne_zero 1)

section FeatureObservations
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Logarithmic moments transferred to the actual correlated finite Gaussian model. -/
theorem featureGaussian_integrable_log_square_pow (v : ι → E) (a : EuclideanSpace ℝ ι)
    (h : ∑ i, a i • v i ≠ 0) (k : ℕ) :
    Integrable (fun x => (Real.log (⟪a, x⟫ ^ 2)) ^ k) (featureGaussian v) := by
  have hv : (‖∑ i, a i • v i‖ ^ 2).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr h)))
  have ht := integrable_log_square_pow_gaussianReal _ hv k
  rw [← featureGaussian_linear_map] at ht
  exact ht.comp_measurable (by fun_prop)

theorem featureGaussian_log_square_memLp_two (v : ι → E) (a : EuclideanSpace ℝ ι)
    (h : ∑ i, a i • v i ≠ 0) :
    MemLp (fun x => Real.log (⟪a, x⟫ ^ 2)) 2 (featureGaussian v) := by
  exact (memLp_two_iff_integrable_sq
    (by exact (by fun_prop : Measurable (fun x => Real.log (⟪a, x⟫ ^ 2))).aestronglyMeasurable)).mpr
    (featureGaussian_integrable_log_square_pow v a h 2)

/-- Corrected 8.3 identity for each nondegenerate linear observation, with no log-integrability
or expectation identity assumed in the hypotheses. -/
theorem featureGaussian_expected_log_square (v : ι → E) (a : EuclideanSpace ℝ ι)
    (h : ∑ i, a i • v i ≠ 0) :
    (∫ x, Real.log (⟪a, x⟫ ^ 2) ∂featureGaussian v) =
      Real.log (‖∑ i, a i • v i‖ ^ 2) + gaussianLogSquareMean := by
  have hv : (‖∑ i, a i • v i‖ ^ 2).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr h)))
  rw [← integral_map (f := fun x : ℝ => Real.log (x ^ 2))
    (by fun_prop : AEMeasurable (fun x => ⟪a, x⟫) (featureGaussian v))
    (by exact (by fun_prop : Measurable (fun x : ℝ => Real.log (x ^ 2))).aestronglyMeasurable),
    featureGaussian_linear_map, expected_log_square_gaussianReal _ hv,
    Real.coe_toNNReal _ (sq_nonneg _)]

/-- A finite weighted log statistic on possibly correlated Gaussian observations. -/
def gaussianLogStatistic {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ j, w j * Real.log (⟪a j, x⟫ ^ 2)

theorem gaussianLogStatistic_memLp_two {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) :
    MemLp (gaussianLogStatistic w a) 2 (featureGaussian v) := by
  exact memLp_finsetSum _ fun j _ => (featureGaussian_log_square_memLp_two v (a j) (h j)).const_mul (w j)

theorem gaussianLogStatistic_expectation {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) :
    (∫ x, gaussianLogStatistic w a x ∂featureGaussian v) =
      ∑ j, w j * (Real.log (‖∑ i, a j i • v i‖ ^ 2) + gaussianLogSquareMean) := by
  unfold gaussianLogStatistic
  rw [integral_finsetSum _ (fun j _ =>
    ((featureGaussian_log_square_memLp_two v (a j) (h j)).integrable one_le_two).const_mul (w j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, featureGaussian_expected_log_square v (a j) (h j)]

/-- The variance retains all cross covariances; independence is not required. -/
theorem gaussianLogStatistic_variance {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) :
    Var[gaussianLogStatistic w a; featureGaussian v] =
      ∑ j, ∑ k, w j * w k *
        cov[fun x => Real.log (⟪a j, x⟫ ^ 2), fun x => Real.log (⟪a k, x⟫ ^ 2); featureGaussian v] := by
  unfold gaussianLogStatistic
  rw [variance_fun_sum (fun j =>
    (featureGaussian_log_square_memLp_two v (a j) (h j)).const_mul (w j))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, mul_assoc, mul_left_comm]

/-- The actual finite weighted statistic satisfies the MSE decomposition because its
second moment has been proved, without any independence assumption. -/
theorem gaussianLogStatistic_mse {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι) (θ : ℝ)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) :
    (∫ x, (gaussianLogStatistic w a x - θ) ^ 2 ∂featureGaussian v) =
      Var[gaussianLogStatistic w a; featureGaussian v] +
        ((∫ x, gaussianLogStatistic w a x ∂featureGaussian v) - θ) ^ 2 := by
  exact mse_decomposition _ θ (gaussianLogStatistic_memLp_two v w a h)

end FeatureObservations
end Hurst
