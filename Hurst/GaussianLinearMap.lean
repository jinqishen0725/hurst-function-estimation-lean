import Hurst.GaussianFinite
import Hurst.KLDataProcessing
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! Identify a transformed observation law with the Gram law of transformed features. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InformationTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem matrix_row_inner (B : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    ⟪WithLp.toLp 2 (B i), x⟫ = (Matrix.toEuclideanCLM (𝕜 := ℝ) B x) i := by
  have he := congrFun (Matrix.ofLp_toEuclideanCLM B x) i
  simpa [PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm] using he.symm

theorem featureGaussian_matrix_covariance (v : ι → E) (B : Matrix ι ι ℝ) (i j : ι) :
    cov[fun x => x i, fun x => x j; (featureGaussian v).map (Matrix.toEuclideanCLM (𝕜 := ℝ) B)] =
      ⟪∑ r, B i r • v r, ∑ r, B j r • v r⟫ := by
  rw [covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
  have he (k : ι) : (fun x => x k) ∘ (Matrix.toEuclideanCLM (𝕜 := ℝ) B) =
      fun x => ⟪WithLp.toLp 2 (B k), x⟫ := by
    ext x
    exact (matrix_row_inner B x k).symm
  rw [he i, he j, featureGaussian_linear_covariance]

set_option backward.isDefEq.respectTransparency false in
/-- Equality of actual probability measures, including singular covariance matrices. -/
theorem featureGaussian_map_matrix (v : ι → E) (B : Matrix ι ι ℝ) :
    (featureGaussian v).map (Matrix.toEuclideanCLM (𝕜 := ℝ) B) =
      featureGaussian (fun i => ∑ j, B i j • v j) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp [featureGaussian]
    · exact IsGaussian.integrable_id
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_inner]
    rw [featureGaussian_matrix_covariance, featureGaussian_covariance]

/-- KL is unchanged by a measurable transformation admitting a measurable left inverse. -/
theorem klDiv_map_eq_of_leftInverse {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (g : β → α) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) : klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply le_antisymm (klDiv_map_le hf μ ν)
  have hb := klDiv_map_le hg (μ.map f) (ν.map f)
  have he : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf, he, Measure.map_id] using hb

/-- Invertible whitening preserves the divergence of the actual feature Gaussian laws. -/
theorem featureGaussian_klDiv_matrix (v w : ι → E) (B : Matrix ι ι ℝ) (hB : IsUnit B.det) :
    klDiv (featureGaussian (fun i => ∑ j, B i j • v j))
      (featureGaussian (fun i => ∑ j, B i j • w j)) = klDiv (featureGaussian v) (featureGaussian w) := by
  rw [← featureGaussian_map_matrix, ← featureGaussian_map_matrix]
  apply klDiv_map_eq_of_leftInverse _ _ _ (Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹)
    (by fun_prop) (by fun_prop)
  intro x
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹ * Matrix.toEuclideanCLM (𝕜 := ℝ) B) x = x
  rw [← map_mul, Matrix.nonsing_inv_mul B hB, map_one]
  rfl

end Hurst
