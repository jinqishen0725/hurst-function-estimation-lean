import Hurst.FeatureHermiteApproximation
import Hurst.GaussianFiniteMoments
import Hurst.FeatureStandardGaussianArray

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace Hurst

theorem gaussianLogStatistic_centered_memLp_finite
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j, ∑ i, a j i • v i ≠ 0) (s : ℝ) :
    MemLp (fun x => gaussianLogStatistic w a x -
      (∫ y, gaussianLogStatistic w a y ∂featureGaussian v))
      (ENNReal.ofReal s) (featureGaussian v) :=
  (gaussianLogStatistic_memLp_finite v w a ha s).sub (memLp_const _)

/-- Exact transfer of every even centered moment of an actual feature statistic to
the standardized Gaussian log array to which the external moment lemma applies. -/
theorem gaussianLogStatistic_centered_evenMoment_standardized
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j, ∑ i, a j i • v i ≠ 0) (k : ℕ) :
    (∫ x, |gaussianLogStatistic w a x -
        (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)| ^ (2 * k)
      ∂featureGaussian v) =
    ∫ x, |∑ j, w j * centeredGaussianLog
        (standardizedFeatureObservation v (a j) x)| ^ (2 * k) ∂featureGaussian v := by
  apply integral_congr_ae
  filter_upwards [gaussianLogStatistic_centered_standardized v w a ha] with x hx
  rw [hx]

end Hurst
