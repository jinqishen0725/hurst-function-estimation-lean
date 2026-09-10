import Hurst.GaussianArrayL2
import Hurst.GaussianLogRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def standardizedFeatureObservation (v : ι → E) (a : EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : ℝ := ⟪a,x⟫/‖∑ i,a i • v i‖

theorem standardizedFeatureObservation_pair (v : ι → E) (a b : EuclideanSpace ℝ ι) :
    HasGaussianLaw (fun x => (standardizedFeatureObservation v a x,standardizedFeatureObservation v b x))
      (featureGaussian v) := by
  convert IsGaussian.hasGaussianLaw_id.map_fun
    ((‖∑ i,a i • v i‖⁻¹ • innerSL ℝ a).prod (‖∑ i,b i • v i‖⁻¹ • innerSL ℝ b)) using 1 <;> first | rfl | infer_instance | (funext x; simp [standardizedFeatureObservation,div_eq_mul_inv,mul_comm])

theorem standardizedFeatureObservation_covariance (v : ι → E) (a b : EuclideanSpace ℝ ι) :
    cov[standardizedFeatureObservation v a,standardizedFeatureObservation v b;featureGaussian v] =
      featureCorrelation v a b := by
  unfold standardizedFeatureObservation
  rw [covariance_fun_div_left,covariance_fun_div_right,featureGaussian_linear_covariance]
  unfold featureCorrelation
  ring

theorem standardizedFeatureObservation_law (v : ι → E) (a : EuclideanSpace ℝ ι)
    (ha : ∑ i,a i • v i≠0) :
    MeasurePreserving (standardizedFeatureObservation v a) (featureGaussian v) (gaussianReal 0 1) := by
  have hG := (standardizedFeatureObservation_pair v a a).fst
  have hs : ‖∑ i,a i • v i‖≠0 := norm_ne_zero_iff.mpr ha
  have hm : (∫ x,standardizedFeatureObservation v a x ∂featureGaussian v)=0 := by
    unfold standardizedFeatureObservation
    rw [integral_div,featureGaussian_linear_mean,zero_div]
  have hv : Var[standardizedFeatureObservation v a;featureGaussian v]=1 := by
    unfold standardizedFeatureObservation
    simp only [div_eq_mul_inv]
    rw [variance_mul_const,featureGaussian_linear_variance]
    field_simp
  refine ⟨by unfold standardizedFeatureObservation; fun_prop,?_⟩
  rw [hG.map_eq_gaussianReal,hm,hv]
  norm_num

end Hurst
