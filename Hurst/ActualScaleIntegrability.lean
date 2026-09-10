import Hurst.FirstScale
import Hurst.ScaleMeasurability
import Hurst.CommonStrideMean

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q1_scale_memLp_eventually (p a b M : ℝ) (hp : 1≤p)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (r : ℕ) (m : ℕ → ℕ) (δ : ℕ → ℝ) :
    ∀ᶠ n in atTop,MemLp (q1LogScaleEstimator r n (m n) (δ n)) 2
      (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) := by
  obtain ⟨C₁,hC₁,h₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,hC₂,h₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha hb hab hM (by norm_num) (by norm_num)
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  have hG₁ := gaussianLogStatistic_memLp_two _ (averagedLocalWeights r n 2 (m n) (δ n)) _
    (fun i => (hn₁ f hf hF i).1)
  have hG₂ := gaussianLogStatistic_memLp_two _ (averagedLocalWeights r n 2 (m n) (δ n)) _
    (fun i => (hn₂ f hf hF i).1)
  exact ((hG₁.const_mul _).add (hG₂.const_mul _)).sub (memLp_const gaussianLogSquareMean)

theorem hurstHolder_q2_scale_memLp_eventually (p a b M l u : ℝ) (hp : 2≤p)
    (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M) (hl : 0<l) (hu : u<1) (hlu : l≤u)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (r : ℕ) (m : ℕ → ℕ) (δ : ℕ → ℝ) :
    ∀ᶠ n in atTop,MemLp (q2LogScaleEstimator l u r n (m n) (δ n)) 2
      (featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) := by
  obtain ⟨C₁,hC₁,h₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,hC₂,h₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  exact q2LogScaleEstimator_memLp r n (m n) (δ n) l u hl hu hlu _
    (fun i => (hn₁ f hf hF i).1) (fun i => (hn₂ f hf hF i).1)

end Hurst
