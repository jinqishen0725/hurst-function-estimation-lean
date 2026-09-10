import Hurst.ActualPilotCLT
import Hurst.ActualPilotMemory
import Hurst.PilotScaleDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem hurstHolder_q1_conditional_all_scale_pilot_CLT (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (σ : ℝ) (hσ : σ≠0) (t : ℝ) (δ A R : ℕ → ℝ) (C V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hrow : ∀ᶠ n in atTop,∀ i,∑ j,featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (q1PilotJoinedCoefficients n i) (q1PilotJoinedCoefficients n j)^2≤R n)
    (hweight : ∀ᶠ n in atTop,(A n)^2*R n*∑ i,pilotJoinedWeights (localPolynomialWeights r n 2 (δ n) t) i^2≤C)
    (hpoly : ∀ k,TendstoInDistribution (fun n x => A n*gaussianLogTruncationStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (pilotJoinedWeights (localPolynomialWeights r n 2 (δ n) t)) (q1PilotJoinedCoefficients n) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1)) :
    TendstoInDistribution (fun n x => A n*(q1Pilot r n (δ n) t x-
      (∫ y,q1Pilot r n (δ n) t y ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)))) atTop
      (fun z : ℝ => Real.sqrt V*z)
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  have hunit := hurstHolder_q1_conditional_pilot_CLT p a b M r hp ha hb hab hM f hf hF t δ A R C V Vk hV hrow hweight hpoly
  obtain ⟨C₁,_,h₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,_,h₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha hb hab hM (by norm_num) (by norm_num)
  exact featureGaussian_pilot_scale_distribution (gaussianReal 0 1)
    (fun n => Fin (n-2)) (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => localPolynomialWeights r n 2 (δ n) t)
    (fun n => commonFirstStrideCoefficients n 1 2 (by norm_num))
    (fun n => commonFirstStrideCoefficients n 2 2 (by norm_num)) A _ σ hσ
    (h₁.mono (fun n hn i => (hn f hf hF i).1)) (h₂.mono (fun n hn i => (hn f hf hF i).1)) hunit

theorem hurstHolder_q2_conditional_all_scale_pilot_CLT (p a b M : ℝ) (r : ℕ)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (σ : ℝ) (hσ : σ≠0) (t : ℝ) (δ A R : ℕ → ℝ) (C V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hrow : ∀ᶠ n in atTop,∀ i,∑ j,featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (q2PilotJoinedCoefficients n i) (q2PilotJoinedCoefficients n j)^2≤R n)
    (hweight : ∀ᶠ n in atTop,(A n)^2*R n*∑ i,pilotJoinedWeights (localPolynomialWeights r n 4 (δ n) t) i^2≤C)
    (hpoly : ∀ k,TendstoInDistribution (fun n x => A n*gaussianLogTruncationStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (pilotJoinedWeights (localPolynomialWeights r n 4 (δ n) t)) (q2PilotJoinedCoefficients n) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1)) :
    TendstoInDistribution (fun n x => A n*(q2Pilot r n (δ n) t x-
      (∫ y,q2Pilot r n (δ n) t y ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)))) atTop
      (fun z : ℝ => Real.sqrt V*z)
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) (gaussianReal 0 1) := by
  have hunit := hurstHolder_q2_conditional_pilot_CLT p a b M r hp ha hb hab hM f hf hF t δ A R C V Vk hV hrow hweight hpoly
  obtain ⟨C₁,_,h₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,_,h₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  exact featureGaussian_pilot_scale_distribution (gaussianReal 0 1)
    (fun n => Fin (n-4)) (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => localPolynomialWeights r n 4 (δ n) t)
    (fun n => commonStrideCoefficients n 1 4 (by norm_num))
    (fun n => commonStrideCoefficients n 2 4 (by norm_num)) A _ σ hσ
    (h₁.mono (fun n hn i => (hn f hf hF i).1)) (h₂.mono (fun n hn i => (hn f hf hF i).1)) hunit

theorem hurstHolder_q1_conditional_all_scale_pilot_memory_limit (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (σ : ℝ) (hσ : σ≠0) (t : ℝ) (δ A : ℕ → ℝ)
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
      (∫ y,q1Pilot r n (δ n) t y ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)))) atTop
      Z
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' := by
  have hunit := hurstHolder_q1_conditional_pilot_memory_limit p a b M r hp ha hb hab hM f hf hF t δ A P' Z htail hquad
  obtain ⟨C₁,_,h₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,_,h₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha hb hab hM (by norm_num) (by norm_num)
  exact featureGaussian_pilot_scale_distribution P'
    (fun n => Fin (n-2)) (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => localPolynomialWeights r n 2 (δ n) t)
    (fun n => commonFirstStrideCoefficients n 1 2 (by norm_num))
    (fun n => commonFirstStrideCoefficients n 2 2 (by norm_num)) A _ σ hσ
    (h₁.mono (fun n hn i => (hn f hf hF i).1)) (h₂.mono (fun n hn i => (hn f hf hF i).1)) hunit

end Hurst
