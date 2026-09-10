from pathlib import Path
s='''import Hurst.GeneralFeatureCLT
import Hurst.JoinedPilot
import Hurst.CommonStrideMean

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst
'''
for q in [1,2]:
 d=2*q
 s+=f'''
theorem hurstHolder_q{q}_conditional_pilot_CLT (p a b M : ℝ) (r : ℕ)
    (hp : {q}≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (δ A R : ℕ → ℝ) (C V : ℝ) (Vk : ℕ → ℝ) (hV : Tendsto Vk atTop (𝓝 V))
    (hrow : ∀ᶠ n in atTop,∀ i,∑ j,featureCorrelation
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (q{q}PilotJoinedCoefficients n i) (q{q}PilotJoinedCoefficients n j)^2≤R n)
    (hweight : ∀ᶠ n in atTop,(A n)^2*R n*∑ i,pilotJoinedWeights (localPolynomialWeights r n {d} (δ n) t) i^2≤C)
    (hpoly : ∀ k,TendstoInDistribution (fun n x => A n*gaussianLogTruncationStatistic
      (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
      (pilotJoinedWeights (localPolynomialWeights r n {d} (δ n) t)) (q{q}PilotJoinedCoefficients n) k x) atTop
      (fun z : ℝ => Real.sqrt (Vk k)*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1)) :
    TendstoInDistribution (fun n x => A n*(q{q}Pilot r n (δ n) t x-
      (∫ y,q{q}Pilot r n (δ n) t y ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))) atTop
      (fun z : ℝ => Real.sqrt V*z)
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) (gaussianReal 0 1) := by
  obtain ⟨C₁,hC₁,h₁⟩ := hurstHolder_common_{'first_stride' if q==1 else 'stride'}_log_mean p a b M 1 {d} hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,hC₂,h₂⟩ := hurstHolder_common_{'first_stride' if q==1 else 'stride'}_log_mean p a b M 2 {d} hp ha hb hab hM (by norm_num) (by norm_num)
  have hfeat : ∀ᶠ n in atTop,∀ i,∑ j,q{q}PilotJoinedCoefficients n i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j≠0 := by
    filter_upwards [h₁,h₂] with n hn₁ hn₂
    intro i
    cases i with
    | inl i => exact (hn₁ f hf hF i).1
    | inr i => exact (hn₂ f hf hF i).1
  have hh := featureGaussian_log_CLT_general_indices (fun n => Fin (n-{d}) ⊕ Fin (n-{d}))
    (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => pilotJoinedWeights (localPolynomialWeights r n {d} (δ n) t)) q{q}PilotJoinedCoefficients
    A R C hfeat hrow hweight V Vk hV hpoly
  simp_rw [q{q}Pilot_joined_statistic] at hh
  exact hh
'''
s+='\nend Hurst\n';Path('.scratch/ActualPilotCLT.lean').write_text(s)
