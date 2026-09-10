import Hurst.ActualMemoryMainline
import Hurst.FirstUnknownInvariance
import Hurst.KnownScaleDistribution
import Hurst.NormalizedInverseMeasurability

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem q1TwoBandwidth_scale_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ₁ δ₂ t : ℝ) (v : Fin n → E)
    (hw : ∑ i,localPolynomialWeights r n 1 δ₂ t i=1)
    (hwm : ∑ i,averagedLocalWeights r n 2 m δ₁ i=1)
    (h₀ : ∀ i,∑ j,gridDifferenceCoefficients n i j • v j≠0)
    (h₁ : ∀ i,∑ j,commonFirstStrideCoefficients n 1 2 (by norm_num) i j • v j≠0)
    (h₂ : ∀ i,∑ j,commonFirstStrideCoefficients n 2 2 (by norm_num) i j • v j≠0)
    (σ : ℝ) (hσ : σ≠0) (Φ : ℝ → ℝ) :
    (∫ x,Φ (q1UnknownTwoBandwidthEstimator r n m δ₁ δ₂ t x) ∂featureGaussian (fun i => σ • v i))=
      ∫ x,Φ (q1UnknownTwoBandwidthEstimator r n m δ₁ δ₂ t x) ∂featureGaussian v := by
  have hz : ∀ᵐ x ∂featureGaussian v,∀ i,⟪gridDifferenceCoefficients n i,x⟫≠0 :=
    ae_all_iff.mpr (fun i => featureGaussian_linear_ae_ne_zero v (gridDifferenceCoefficients n i) (h₀ i))
  have hscale : ∀ᵐ x ∂featureGaussian v,
      q1UnknownTwoBandwidthEstimator r n m δ₁ δ₂ t (σ • x)=q1UnknownTwoBandwidthEstimator r n m δ₁ δ₂ t x := by
    filter_upwards [hz,q1LogScaleEstimator_scale_ae r n m δ₁ v hwm h₁ h₂ σ hσ] with x hx hs
    unfold q1UnknownTwoBandwidthEstimator
    rw [gaussianLogStatistic_smul _ _ x σ hσ hx,hw,mul_one,hs]
    congr 1
    ring
  have he := featureGaussian_known_scale_integral v σ hσ (fun x => Φ (q1UnknownTwoBandwidthEstimator r n m δ₁ δ₂ t (σ • x)))
  simp only [smul_smul,mul_inv_cancel₀ hσ,one_smul] at he
  apply he.trans
  exact integral_congr_ae (hscale.mono (fun _ hx => congrArg Φ hx))

theorem hurstHolder_q1_twoBandwidth_scale_distribution_transfer (p a b M : ℝ) (r : ℕ)
    (hp : 1≤p) (ha : 0<a) (hb : b<1) (hab : a≤b) (hM : 0≤M)
    (f : ℝ → ℝ) (hf : f∈hurstHolderClass p M) (hF : MapsTo f (Ioo (0:ℝ) 1) (Icc a b))
    (t : ℝ) (δ₁ δ₂ A : ℕ → ℝ) (m : ℕ → ℕ) (σ : ℝ) (hσ : σ≠0)
    (hw : ∀ᶠ n in atTop,∑ i,localPolynomialWeights r n 1 (δ₂ n) t i=1)
    (hwm : ∀ᶠ n in atTop,∑ i,averagedLocalWeights r n 2 (m n) (δ₁ n) i=1)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ)
    (hunit : TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop Z
      (fun n => featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) P') :
    TendstoInDistribution (fun (n : ℕ) x => 2*A n*Real.log n*(q1UnknownTwoBandwidthEstimator r n (m n) (δ₁ n) (δ₂ n) t x-f t)) atTop Z
      (fun n => featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) P' := by
  obtain ⟨C₀,_,he₀⟩ := hurstHolder_stride_first_log_mean p a b M hp ha hb hab hM 1 (by norm_num)
  obtain ⟨C₁,_,he₁⟩ := hurstHolder_common_first_stride_log_mean p a b M 1 2 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,_,he₂⟩ := hurstHolder_common_first_stride_log_mean p a b M 2 2 hp ha hb hab hM (by norm_num) (by norm_num)
  apply distribution_transfer_of_eventual_test_equality _ _ P' _ _ Z hunit
  · intro n
    have hX : Measurable (gaussianLogStatistic (localPolynomialWeights r n 1 (δ₂ n) t) (gridDifferenceCoefficients n)) := by unfold gaussianLogStatistic; fun_prop
    have hS := q1LogScaleEstimator_measurable r n (m n) (δ₁ n)
    exact (normalized_q1_inverse_measurable n _ (hX.sub hS) (A n) (f t)).aemeasurable
  · filter_upwards [hw,hwm,he₀,he₁,he₂] with n hn hn' h₀ h₁ h₂
    intro Φ
    exact q1TwoBandwidth_scale_integral r n (m n) (δ₁ n) (δ₂ n) t _ hn hn'
      (fun i => (h₀ f hf hF i).1) (fun i => (h₁ f hf hF i).1) (fun i => (h₂ f hf hF i).1)
      σ hσ (fun z => Φ (2*A n*Real.log n*(z-f t)))

end Hurst
