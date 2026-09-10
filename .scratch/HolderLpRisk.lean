import Hurst.KnownScaleRisk
import Hurst.UnitLpRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- All 1 ≤ s ≤ 2 squared Ls risks share the same whole-class, whole-interval upper rate. -/
theorem hurstHolder_q1_known_scale_Lp_risk (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ σ : ℝ, σ ≠ 0 → ∀ s ∈ Icc (1 : ℝ) 2, ∀ n : ℕ, N ≤ n →
      (∫ x, (unitLpLoss s (q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) (σ⁻¹ • x)) g) ^ 2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤
          C * (lowerBoundRate p n) ^ 2 := by
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q1_known_scale_integrated_rate p a b M hp ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design p Nw hp)
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgRisk⟩ := hrisk f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro σ hσ s hs n hn
  obtain ⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩ := hK n ((le_max_right N K).trans hn)
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  let μ := scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)
  haveI : IsProbabilityMeasure μ := by dsimp [μ, scaledHarmonizableGaussian]; infer_instance
  let F := fun x t => q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) (σ⁻¹ • x) t
  have hFm : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => F z.1 z.2) :=
    (q1SpatialEstimator_joint_measurable _ n hn1 _ hdet).comp (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => (σ⁻¹ • z.1, z.2)))
  have h := unitLpRisk_le_integrated_mse μ s hs.1 hs.2 F g hFm hg
    (fun x => q1SpatialEstimator_continuous _ n hn1 _ hdet _) (fun x t => q1SpatialEstimator_mem _ _ _ _ _) hmap
  exact h.trans (hgRisk σ hσ n ((le_max_left N K).trans hn))

end Hurst
