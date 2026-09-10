import Hurst.FeatureFiniteMomentTransfer
import Hurst.GroupedMomentIntegral

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace Hurst

/-- Final transfer from per-color Bardet--Surgailis estimates to the actual
centered feature log statistic. The factor depending on the fixed number of
colors is explicit, and no independence between colors is assumed. -/
theorem gaussianLogStatistic_centered_evenMoment_of_coloring
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j, ∑ i, a j i • v i ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) {d : ℕ} (color : κ → Fin d) (B : ℝ)
    (hgroup : ∀ c,
      (∫ x, |colorClassSum color
        (fun j => w j * centeredGaussianLog
          (standardizedFeatureObservation v (a j) x)) c| ^ (2 * k)
        ∂featureGaussian v) ≤ B) :
    (∫ x, |gaussianLogStatistic w a x -
        (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)| ^ (2 * k)
      ∂featureGaussian v) ≤ (d : ℝ) ^ (2 * k) * B := by
  rw [gaussianLogStatistic_centered_evenMoment_standardized v w a ha k]
  let Y : κ → EuclideanSpace ℝ ι → ℝ := fun j x =>
    w j * centeredGaussianLog (standardizedFeatureObservation v (a j) x)
  have hY : ∀ j, MemLp (Y j) (2 * k : ℕ) (featureGaussian v) := by
    intro j
    have hg := centeredGaussianLog_memLp_finite (2 * k : ℝ)
    have hs := hg.comp_measurePreserving (standardizedFeatureObservation_law v (a j) (ha j))
    have hw := hs.const_mul (w j)
    have he : (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by norm_num
    rw [he, ENNReal.ofReal_natCast] at hw
    simpa only [Y, Function.comp_apply] using hw
  exact grouped_evenMoment_integral_uniform (featureGaussian v) Y k hk hY color B hgroup

end Hurst
