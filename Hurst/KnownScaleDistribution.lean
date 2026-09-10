import Hurst.DistributionTestTransfer
import Hurst.KnownScaleRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem featureGaussian_known_scale_distribution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (v : ∀ n,Fin n → E) (X : ∀ n,EuclideanSpace ℝ (Fin n) → ℝ)
    (hX : ∀ n,Measurable (X n)) (Z : Ω' → ℝ) (σ : ℝ) (hσ : σ≠0)
    (hCLT : TendstoInDistribution X atTop Z (fun n => featureGaussian (v n)) P') :
    TendstoInDistribution (fun n x => X n (σ⁻¹ • x)) atTop Z
      (fun n => featureGaussian (fun i => σ • v n i)) P' := by
  apply distribution_transfer_of_eventual_test_equality (fun n => featureGaussian (v n))
    (fun n => featureGaussian (fun i => σ • v n i)) P' X _ Z hCLT
    (fun n => ((hX n).comp (by fun_prop)).aemeasurable)
  exact Eventually.of_forall (fun n φ => featureGaussian_known_scale_integral (v n) σ hσ (fun x => φ (X n x)))

end Hurst
