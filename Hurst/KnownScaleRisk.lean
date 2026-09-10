import Hurst.HolderIntegratedRisk
import Hurst.GaussianScale

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem featureGaussian_map_smul {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E) (σ : ℝ) :
    (featureGaussian v).map (fun x => σ • x) = featureGaussian (fun i => σ • v i) := by
  have h := featureGaussian_map_matrix v (σ • (1 : Matrix ι ι ℝ))
  have hf : (Matrix.toEuclideanCLM (𝕜 := ℝ) (σ • (1 : Matrix ι ι ℝ)) : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) = (fun x => σ • x) := by
    funext x
    apply PiLp.ext
    intro i
    change (WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℝ) (σ • (1 : Matrix ι ι ℝ)) x)) i = _
    rw [Matrix.ofLp_toEuclideanCLM]
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, mul_ite]
  have hv : (fun i => ∑ j, (σ • (1 : Matrix ι ι ℝ)) i j • v j) = fun i => σ • v i := by
    funext i
    simp [Matrix.one_apply, mul_ite]
  rwa [hf, hv] at h

/-- Exact removal of a known common scale for any real-valued loss functional. -/
theorem featureGaussian_known_scale_integral {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E) (σ : ℝ) (hσ : σ ≠ 0)
    (F : EuclideanSpace ℝ ι → ℝ) :
    (∫ x, F (σ⁻¹ • x) ∂featureGaussian (fun i => σ • v i)) = ∫ x, F x ∂featureGaussian v := by
  let e : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι :=
    { toFun := fun x => σ • x
      invFun := fun x => σ⁻¹ • x
      left_inv := by intro x; simp [smul_smul, inv_mul_cancel₀ hσ]
      right_inv := by intro x; simp [smul_smul, mul_inv_cancel₀ hσ]
      measurable_toFun := by change Measurable (fun x : EuclideanSpace ℝ ι => σ • x); fun_prop
      measurable_invFun := by change Measurable (fun x : EuclideanSpace ℝ ι => σ⁻¹ • x); fun_prop }
  have hm : (featureGaussian v).map e = featureGaussian (fun i => σ • v i) := featureGaussian_map_smul v σ
  rw [← hm, integral_map_equiv]
  congr 1
  funext x
  change F (σ⁻¹ • (σ • x)) = F x
  rw [smul_smul, inv_mul_cancel₀ hσ, one_smul]

/-- The whole-class pointwise MSE constant is independent of every known nonzero common scale. -/
theorem hurstHolder_q1_known_scale_mse_rate (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ σ : ℝ, σ ≠ 0 → ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x, (q1LocalEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) t (σ⁻¹ • x) - g t) ^ 2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤
          C * (lowerBoundRate p n) ^ 2 := by
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q1_uniform_mse_rate p a b M hp ha hb hab hM
  refine ⟨C, hC, N, hN, ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgRisk⟩ := hrisk f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro σ hσ n hn t ht
  change (∫ x, (q1LocalEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) t (σ⁻¹ • x) - g t) ^ 2
    ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) ≤ _
  rw [featureGaussian_known_scale_integral _ σ hσ (fun x => (q1LocalEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) t x - g t) ^ 2)]
  exact hgRisk n hn t ht

/-- The same scale removal applies to the actual integrated squared L2 loss. -/
theorem hurstHolder_q1_known_scale_integrated_rate (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ σ : ℝ, σ ≠ 0 → ∀ n : ℕ, N ≤ n →
      (∫ x, (∫ t in Ioo (0 : ℝ) 1,
        (q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) (σ⁻¹ • x) t - g t) ^ 2)
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤
          C * (lowerBoundRate p n) ^ 2 := by
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q1_integrated_mse_rate p a b M hp ha hb hab hM
  refine ⟨C, hC, N, hN, ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgRisk⟩ := hrisk f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro σ hσ n hn
  change (∫ x, (∫ t in Ioo (0 : ℝ) 1,
    (q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) (σ⁻¹ • x) t - g t) ^ 2)
    ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) ≤ _
  rw [featureGaussian_known_scale_integral _ σ hσ (fun x => ∫ t in Ioo (0 : ℝ) 1,
    (q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) x t - g t) ^ 2)]
  exact hgRisk n hn

end Hurst
