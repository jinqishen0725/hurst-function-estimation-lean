import Hurst.FirstUnknownInvariance
import Hurst.FirstScaleSharperRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_unknown_scale_test_eq (p a b M : ℝ) (r : ℕ) (hp : 1≤p)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    ∀ᶠ n in atTop,∀ σ : ℝ,σ≠0 → ∀ Φ : ℝ → ℝ,
      (∫ x,Φ (q1UnknownLocalEstimator r n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x)
        ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i))=
      ∫ x,Φ (q1UnknownLocalEstimator r n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n)) := by
  obtain ⟨N₁,hN₁,D₁,hD₁,hw₁⟩ := localPolynomialWeights_uniform_stability r 1
  obtain ⟨N₂,hN₂,D₂,hD₂,hw₂⟩ := localPolynomialWeights_uniform_stability r 2
  obtain ⟨E₀,_,hm₀⟩ := hurstHolder_stride_first_log_mean p a b M hp ha hb hab hM 1 (by norm_num)
  obtain ⟨E₁,_,hm₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂,_,hm₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha hb hab hM (by norm_num) (by norm_num)
  filter_upwards [hm₀,hm₁,hm₂,optimalLocalBandwidth_eventual_design p (max N₁ N₂) hp] with n h₀ h₁ h₂ hd
  intro σ hσ Φ
  obtain ⟨hn1,hδ,hδhalf,hnd,_,_⟩ := hd
  obtain ⟨hm,hmd⟩ := scaleAverageResolution_design p n hδ
  have hws : ∑ i,localPolynomialWeights r n 1 (optimalLocalBandwidth p n) t i=1 := by
    have he := (hw₁ n (by omega) (by omega) _ t hδ hδhalf ht ((le_max_left _ _).trans hnd)).2.2.2 0
    simpa using he
  have hwm : ∑ i,averagedLocalWeights r n 2 (scaleAverageResolution p n) (optimalLocalBandwidth p n) i=1 := by
    apply averagedLocalWeights_sum _ _ _ _ hm
    intro j
    have hj := grid_mem (scaleAverageResolution p n) j.val hm j.isLt
    have he := (hw₂ n (by omega) (by omega) _ _ hδ hδhalf ⟨hj.1.le,hj.2.le⟩ ((le_max_right _ _).trans hnd)).2.2.2 0
    simpa using he
  exact q1UnknownLocalEstimator_scale_integral r n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t _ hws hwm
    (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1) (fun i => (h₂ f hf hF i).1) σ hσ Φ

end Hurst
