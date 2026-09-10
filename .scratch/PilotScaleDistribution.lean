import Hurst.KnownScaleDistribution
import Hurst.PilotScale

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem featureGaussian_pilot_scale_distribution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (κ : ℕ → Type*) [∀ n,Fintype (κ n)] (v : ∀ n,Fin n → E)
    (w : ∀ n,κ n → ℝ) (a b : ∀ n,κ n → EuclideanSpace ℝ (Fin n))
    (A : ℕ → ℝ) (Z : Ω' → ℝ) (σ : ℝ) (hσ : σ≠0)
    (ha : ∀ᶠ n in atTop,∀ i,∑ j,a n i j • v n j≠0)
    (hb : ∀ᶠ n in atTop,∀ i,∑ j,b n i j • v n j≠0)
    (hunit : TendstoInDistribution (fun n x => A n*(twoScalePilot (gaussianLogStatistic (w n) (a n)) (gaussianLogStatistic (w n) (b n)) x-
      (∫ y,twoScalePilot (gaussianLogStatistic (w n) (a n)) (gaussianLogStatistic (w n) (b n)) y ∂featureGaussian (v n)))) atTop Z
      (fun n => featureGaussian (v n)) P') :
    TendstoInDistribution (fun n x => A n*(twoScalePilot (gaussianLogStatistic (w n) (a n)) (gaussianLogStatistic (w n) (b n)) x-
      (∫ y,twoScalePilot (gaussianLogStatistic (w n) (a n)) (gaussianLogStatistic (w n) (b n)) y ∂featureGaussian (fun i => σ • v n i)))) atTop Z
      (fun n => featureGaussian (fun i => σ • v n i)) P' := by
  apply distribution_transfer_of_eventual_test_equality _ _ P' _ _ Z hunit
  · intro n
    unfold twoScalePilot gaussianLogStatistic
    fun_prop
  · filter_upwards [ha,hb] with n hn hn'
    intro φ
    have he := twoScalePilot_scale_integral (v n) (w n) (a n) (b n) hn hn' σ hσ (fun z => z)
    rw [he]
    exact twoScalePilot_scale_integral (v n) (w n) (a n) (b n) hn hn' σ hσ (fun z => φ (A n*(z-_)))

end Hurst
