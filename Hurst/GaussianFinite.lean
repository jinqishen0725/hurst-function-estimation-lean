import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! Finite Gaussian observations built from Hilbert-space features.
The covariance is proved to be a Gram matrix, rather than assumed positive.
Concrete one-dimensional spectral features and their kernel are in Hurst.Harmonizable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace ENNReal
namespace Hurst
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def featureGaussian (v : ι → E) : Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian 0 (Matrix.gram ℝ v)

instance featureGaussian_isGaussian (v : ι → E) : IsGaussian (featureGaussian v) := by
  unfold featureGaussian
  infer_instance

instance featureGaussian_isProbability (v : ι → E) :
    IsProbabilityMeasure (featureGaussian v) := inferInstance

theorem featureGaussian_covariance (v : ι → E) (i j : ι) :
    cov[fun x => x i, fun x => x j; featureGaussian v] = ⟪v i, v j⟫ := by
  exact covariance_eval_multivariateGaussian (Matrix.posSemidef_gram ℝ v) i j

theorem featureGaussian_coordinate_variance (v : ι → E) (i : ι) :
    Var[fun x => x i; featureGaussian v] = ‖v i‖ ^ 2 := by
  rw [← covariance_self (by fun_prop), featureGaussian_covariance]
  exact real_inner_self_eq_norm_sq _

theorem featureGaussian_linear_covariance (v : ι → E) (a b : EuclideanSpace ℝ ι) :
    cov[fun x => ⟪a, x⟫, fun x => ⟪b, x⟫; featureGaussian v] =
      ⟪∑ i, a i • v i, ∑ i, b i • v i⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
  rw [featureGaussian, covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simpa using Matrix.star_dotProduct_gram_mulVec v (fun i => a i) (fun i => b i)

theorem featureGaussian_linear_variance (v : ι → E) (a : EuclideanSpace ℝ ι) :
    Var[fun x => ⟪a, x⟫; featureGaussian v] = ‖∑ i, a i • v i‖ ^ 2 := by
  rw [← covariance_self (by fun_prop), featureGaussian_linear_covariance]
  exact real_inner_self_eq_norm_sq _

theorem featureGaussian_linear_hasGaussianLaw (v : ι → E) (a : EuclideanSpace ℝ ι) :
    HasGaussianLaw (fun x => ⟪a, x⟫) (featureGaussian v) := by
  exact IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ a)

theorem featureGaussian_linear_memLp (v : ι → E) (a : EuclideanSpace ℝ ι)
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x => ⟪a, x⟫) p (featureGaussian v) :=
  (featureGaussian_linear_hasGaussianLaw v a).memLp hp

theorem featureGaussian_linear_mean (v : ι → E) (a : EuclideanSpace ℝ ι) :
    (∫ x, ⟪a, x⟫ ∂featureGaussian v) = 0 := by
  change (∫ x, (innerSL ℝ a) x ∂featureGaussian v) = 0
  rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id]
  simp [featureGaussian]

theorem featureGaussian_linear_map (v : ι → E) (a : EuclideanSpace ℝ ι) :
    (featureGaussian v).map (fun x => ⟪a, x⟫) =
      gaussianReal 0 (‖∑ i, a i • v i‖ ^ 2).toNNReal := by
  rw [(featureGaussian_linear_hasGaussianLaw v a).map_eq_gaussianReal,
    featureGaussian_linear_mean, featureGaussian_linear_variance]

/-- A nonzero feature combination gives a strictly positive observation variance. -/
theorem featureGaussian_linear_variance_pos (v : ι → E) (a : EuclideanSpace ℝ ι)
    (h : ∑ i, a i • v i ≠ 0) :
    0 < Var[fun x => ⟪a, x⟫; featureGaussian v] := by
  rw [featureGaussian_linear_variance]
  exact sq_pos_of_pos (norm_pos_iff.mpr h)

/-- Nondegenerate linear observations avoid the singularity of the logarithm almost surely.
This does not yet assert integrability of the logarithm. -/
theorem featureGaussian_linear_ae_ne_zero (v : ι → E) (a : EuclideanSpace ℝ ι)
    (h : ∑ i, a i • v i ≠ 0) :
    ∀ᵐ x ∂featureGaussian v, ⟪a, x⟫ ≠ 0 := by
  have hv : (‖∑ i, a i • v i‖ ^ 2).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr h)))
  letI := noAtoms_gaussianReal (μ := 0) hv
  have hz : (featureGaussian v).map (fun x => ⟪a, x⟫) {0} = 0 := by
    rw [featureGaussian_linear_map]
    exact measure_singleton 0
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)] at hz
  rw [ae_iff]
  have he : {x : EuclideanSpace ℝ ι | ¬ ⟪a, x⟫ ≠ 0} =
      (fun x => ⟪a, x⟫) ⁻¹' {0} := by
    ext x
    simp
  rw [he]
  exact hz

/-- File 20: perturbing features preserves a variance floor. The concrete harmonizable
feature estimates giving `hU` and `hV` are still separate obligations. -/
theorem featureGaussian_perturb_variance_lower
    (U V : ι → E) (a : EuclideanSpace ℝ ι)
    (hU : (3 / 4 : ℝ) * ‖a‖ ≤ ‖∑ i, a i • U i‖)
    (hV : ‖∑ i, a i • V i‖ ≤ (1 / 4 : ℝ) * ‖a‖) :
    (1 / 4 : ℝ) * ‖a‖ ^ 2 ≤
      Var[fun x => ⟪a, x⟫; featureGaussian (fun i => U i + V i)] := by
  rw [featureGaussian_linear_variance]
  simp only [smul_add, Finset.sum_add_distrib]
  have ht := norm_sub_le (∑ i, a i • U i + ∑ i, a i • V i) (∑ i, a i • V i)
  simp only [add_sub_cancel_right] at ht
  have hl : (1 / 2 : ℝ) * ‖a‖ ≤ ‖∑ i, a i • U i + ∑ i, a i • V i‖ := by
    linarith
  nlinarith [norm_nonneg a, norm_nonneg (∑ i, a i • U i + ∑ i, a i • V i)]

end Hurst
