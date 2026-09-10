import Hurst.DistributionTestTransfer
import Hurst.NormalizedInverseMeasurability
import Hurst.FirstUnknownScaleTests
import Hurst.SecondUnknownScaleTests

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem hurstHolder_q1_unknown_scale_distribution_transfer (p a b M : ℝ) (r : ℕ) 
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (A : ℕ → ℝ) (σ : ℝ) (hσ : σ≠0)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (hunit : TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1UnknownLocalEstimator r n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x-f t)) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1UnknownLocalEstimator r n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x-f t)) atTop Z
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' := by
  have he := hurstHolder_q1_unknown_scale_test_eq p a b M  r hp ha hb hab hM f hf hF t ht
  apply distribution_transfer_of_eventual_test_equality _ _ P' _ _ Z hunit
  · intro n
    have hX : Measurable (gaussianLogStatistic (localPolynomialWeights r n 1 (optimalLocalBandwidth p n) t) (gridDifferenceCoefficients n)) := by
      unfold gaussianLogStatistic; fun_prop
    have hS := q1LogScaleEstimator_measurable  r n (scaleAverageResolution p n) (optimalLocalBandwidth p n)
    exact (normalized_q1_inverse_measurable n  _ (hX.sub hS) (A n) (f t)).aemeasurable
  · filter_upwards [he] with n hn
    intro φ
    exact hn σ hσ (fun z => φ (2*A n*Real.log n*(z-f t)))

theorem hurstHolder_q2_unknown_scale_distribution_transfer (p a b M : ℝ) (r : ℕ) (l u : ℝ) (hu0 : 0≤u) (hu : u<1)
    (hp : 2≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (A : ℕ → ℝ) (σ : ℝ) (hσ : σ≠0)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (hunit : TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q2UnknownLocalEstimator l u r n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x-f t)) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q2UnknownLocalEstimator l u r n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x-f t)) atTop Z
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' := by
  have he := hurstHolder_q2_unknown_scale_test_eq p a b M l u r hp ha hb hab hM f hf hF t ht
  apply distribution_transfer_of_eventual_test_equality _ _ P' _ _ Z hunit
  · intro n
    have hX : Measurable (gaussianLogStatistic (localPolynomialWeights r n 2 (optimalLocalBandwidth p n) t) (gridSecondCoefficients n)) := by
      unfold gaussianLogStatistic; fun_prop
    have hS := q2LogScaleEstimator_measurable l u r n (scaleAverageResolution p n) (optimalLocalBandwidth p n)
    exact (normalized_q2_inverse_measurable n u hu0 hu _ (hX.sub hS) (A n) (f t)).aemeasurable
  · filter_upwards [he] with n hn
    intro φ
    exact hn σ hσ (fun z => φ (2*A n*Real.log n*(z-f t)))

end Hurst
