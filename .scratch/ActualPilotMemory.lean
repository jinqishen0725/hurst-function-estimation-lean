import Hurst.ActualPilotCLT
import Hurst.WeightedQuadraticLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem hurstHolder_q1_conditional_pilot_memory_limit (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (δ A : ℕ → ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (htail : Tendsto (fun n => (A n)^2*(∑ i,∑ j,
      |pilotJoinedWeights (localPolynomialWeights r n 2 (δ n) t) i| *
      |pilotJoinedWeights (localPolynomialWeights r n 2 (δ n) t) j| *
      |featureCorrelation (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (q1PilotJoinedCoefficients n i) (q1PilotJoinedCoefficients n j)|^4)) atTop (𝓝 0))
    (hquad : TendstoInDistribution (fun n x => A n*gaussianLogQuadraticStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (pilotJoinedWeights (localPolynomialWeights r n 2 (δ n) t)) (q1PilotJoinedCoefficients n) x) atTop
      Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun n x => A n*(q1Pilot r n (δ n) t x-
      (∫ y,q1Pilot r n (δ n) t y ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop
      Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P' := by
  obtain ⟨C₁,hC₁,h₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,hC₂,h₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha hb hab hM (by norm_num) (by norm_num)
  have hfeat : ∀ᶠ n in atTop,∀ i,∑ j,q1PilotJoinedCoefficients n i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j≠0 := by
    filter_upwards [h₁,h₂] with n hn₁ hn₂
    intro i
    cases i with
    | inl i => exact (hn₁ f hf hF i).1
    | inr i => exact (hn₂ f hf hF i).1
  have hh := featureGaussian_log_limit_of_quadratic_weighted_limit P' (fun n => Fin (n-2) ⊕ Fin (n-2))
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => pilotJoinedWeights (localPolynomialWeights r n 2 (δ n) t)) q1PilotJoinedCoefficients
    A Z hfeat htail hquad
  simp_rw [q1Pilot_joined_statistic] at hh
  exact hh


end Hurst
