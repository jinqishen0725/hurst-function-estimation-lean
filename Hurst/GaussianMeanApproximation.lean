import Hurst.GaussianLog
import Hurst.LocalPolynomial

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem gaussianLogStatistic_mean_approximation {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j,∑ i,a j i • v i≠0) (m : κ → ℝ) (e : ℝ)
    (hm : ∀ j,|Real.log (‖∑ i,a j i • v i‖^2)+gaussianLogSquareMean-m j|≤e) :
    |(∫ x,gaussianLogStatistic w a x ∂featureGaussian v)-smooth w m| ≤ (∑ j,|w j|)*e := by
  rw [gaussianLogStatistic_expectation v w a ha]
  have he : (∑ j,w j*(Real.log (‖∑ i,a j i • v i‖^2)+gaussianLogSquareMean))-smooth w m =
      smooth w (fun j => Real.log (‖∑ i,a j i • v i‖^2)+gaussianLogSquareMean-m j) := by
    simp only [smooth,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  exact smooth_residual_bound w _ e hm

end Hurst
