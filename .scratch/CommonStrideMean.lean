import Hurst.CommonStrideVariance
import Hurst.StrideLogMean

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

theorem hurstHolder_common_stride_log_mean (p a b M : ℝ) (d q : ℕ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (hd : 0 < d) (hq : 2*d ≤ q) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ i : Fin (n-q),
      (∑ j, commonStrideCoefficients n d q hq i j • gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0) ∧
      |(Real.log (‖∑ j, commonStrideCoefficients n d q hq i j • gridObservationFeatures n (midpointSampleHurst f hf.1 n) j‖^2)+gaussianLogSquareMean) -
        (-2*f (grid n i.val)*Real.log n + 2*f (grid n i.val)*Real.log d + q2LogCorrection (f (grid n i.val))+gaussianLogSquareMean)| ≤
        gridCovarianceError (1/2) C n := by
  obtain ⟨C, hC, he⟩ := hurstHolder_grid_stride_second_log_mean p a b M hp ha hb hab hM d hd
  refine ⟨C, hC, he.mono ?_⟩
  intro n hn f hf hF i
  obtain ⟨hz, hm⟩ := hn f hf hF (commonStrideIndex n d q hq i)
  rw [featureGaussian_expected_log_square _ _ hz] at hm
  exact ⟨hz, hm⟩

end Hurst
