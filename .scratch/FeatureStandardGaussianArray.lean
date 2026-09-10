import Hurst.FeatureStandardGaussian
import Hurst.ExternalMomentBound

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem standardizedFeatureObservation_joint
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι) :
    HasGaussianLaw (fun x => fun j => standardizedFeatureObservation v (a j) x)
      (featureGaussian v) := by
  let L : EuclideanSpace ℝ ι →L[ℝ] (κ → ℝ) :=
    ContinuousLinearMap.pi (fun j => ‖∑ i, a j i • v i‖⁻¹ • innerSL ℝ (a j))
  convert IsGaussian.hasGaussianLaw_id.map_fun L using 1 <;>
    first
    | rfl
    | infer_instance
    | (funext x j
       simp only [L, ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
         smul_eq_mul, standardizedFeatureObservation, div_eq_mul_inv, id_eq]
       change ⟪a j, x⟫ * ‖∑ i, a j i • v i‖⁻¹ =
         ‖∑ i, a j i • v i‖⁻¹ * ⟪a j, x⟫
       ring)

/-- The external scalar lemma is applicable to every finite nondegenerate family
of feature observations; joint Gaussianity and standard marginal laws are discharged
internally here. -/
theorem featureGaussian_bardetSurgailis_interface
    (hBS : BardetSurgailisLemmaOneScalar)
    {ι κ E : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j, ∑ i, a j i • v i ≠ 0) :
    BardetSurgailisBoundsFor (featureGaussian v)
      (fun j => standardizedFeatureObservation v (a j)) := by
  exact hBS (featureGaussian v) (fun j => standardizedFeatureObservation v (a j))
    (standardizedFeatureObservation_joint v a)
    (fun j => standardizedFeatureObservation_law v (a j) (ha j))

end Hurst
