import Hurst.GaussianLinearMap

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace ENNReal
namespace Hurst

variable {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restrict a Euclidean vector to coordinates selected by `e`. -/
def euclideanCoordinateRestriction (e : κ → ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : κ =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) (e k)).comp
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).toContinuousLinearMap))

@[simp]
theorem euclideanCoordinateRestriction_apply (e : κ → ι)
    (x : EuclideanSpace ℝ ι) (k : κ) :
    euclideanCoordinateRestriction e x k = x (e k) := by
  simp [euclideanCoordinateRestriction]

/-- Projecting a feature Gaussian onto selected coordinates gives the feature
Gaussian built from the selected features, even when the covariance is singular. -/
theorem featureGaussian_map_coordinateRestriction (v : ι → E) (e : κ → ι) :
    (featureGaussian v).map (euclideanCoordinateRestriction e) =
      featureGaussian (fun k => v (e k)) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp [featureGaussian]
    · exact IsGaussian.integrable_id
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_inner]
    rw [covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
    have hi : ((fun u : EuclideanSpace ℝ κ => u i) ∘
        (euclideanCoordinateRestriction e)) =
        (fun u : EuclideanSpace ℝ ι => u (e i)) := by
      funext x
      exact euclideanCoordinateRestriction_apply e x i
    have hj : ((fun u : EuclideanSpace ℝ κ => u j) ∘
        (euclideanCoordinateRestriction e)) =
        (fun u : EuclideanSpace ℝ ι => u (e j)) := by
      funext x
      exact euclideanCoordinateRestriction_apply e x j
    rw [hi, hj, featureGaussian_covariance, featureGaussian_covariance]

end Hurst
