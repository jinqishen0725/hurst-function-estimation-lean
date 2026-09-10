import Hurst.FiniteGaussianSpectral

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace Hurst

/-- The continuous coordinate projection from `m` standard Gaussian
coordinates to the first `K` coordinates. -/
def euclideanFinPrefix (K m : ℕ) (hKm : K ≤ m) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin K => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin K =>
      EuclideanSpace.proj (Fin.castLE hKm i))

@[simp]
theorem euclideanFinPrefix_apply (K m : ℕ) (hKm : K ≤ m)
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin K) :
    euclideanFinPrefix K m hKm x i = x (Fin.castLE hKm i) := by
  simp [euclideanFinPrefix, EuclideanSpace.proj]

/-- A prefix of a canonical finite standard Gaussian vector is again a
canonical standard Gaussian vector. -/
theorem stdGaussian_map_euclideanFinPrefix (K m : ℕ) (hKm : K ≤ m) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).map
        (euclideanFinPrefix K m hKm) =
      stdGaussian (EuclideanSpace ℝ (Fin K)) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin K) ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply,
      ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
    simp only [OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_inner]
    rw [covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
    have hi : ((fun u : EuclideanSpace ℝ (Fin K) => u i) ∘
        euclideanFinPrefix K m hKm) =
        fun u : EuclideanSpace ℝ (Fin m) => u (Fin.castLE hKm i) := by
      funext x
      exact euclideanFinPrefix_apply K m hKm x i
    have hj : ((fun u : EuclideanSpace ℝ (Fin K) => u j) ∘
        euclideanFinPrefix K m hKm) =
        fun u : EuclideanSpace ℝ (Fin m) => u (Fin.castLE hKm j) := by
      funext x
      exact euclideanFinPrefix_apply K m hKm x j
    rw [hi, hj, stdGaussian_coordinate_covariance,
      stdGaussian_coordinate_covariance]
    simp

theorem euclideanFinPrefix_measurePreserving (K m : ℕ) (hKm : K ≤ m) :
    MeasurePreserving (euclideanFinPrefix K m hKm)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (stdGaussian (EuclideanSpace ℝ (Fin K))) :=
  ⟨(euclideanFinPrefix K m hKm).continuous.measurable,
    stdGaussian_map_euclideanFinPrefix K m hKm⟩

end Hurst
