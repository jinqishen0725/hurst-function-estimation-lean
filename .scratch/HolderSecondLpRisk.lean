import Hurst.HolderSecondRate
import Hurst.SecondSpatial
import Hurst.KnownScaleRisk
import Hurst.UnitLpRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Full-interval squared Ls risk for q=2,p=2 and every fixed Hurst range below one. -/
theorem hurstHolder_q2_p2_known_scale_Lp_risk (a b M : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass 2 M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ σ : ℝ, σ ≠ 0 → ∀ s ∈ Icc (1 : ℝ) 2, ∀ n : ℕ, N ≤ n →
      (∫ x, (unitLpLoss s (q2SpatialEstimator b 1 n (optimalLocalBandwidth 2 n) (σ⁻¹ • x)) g) ^ 2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤
          C * (lowerBoundRate 2 n) ^ 2 := by
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q2_p2_uniform_mse_rate a b M ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability 1 2
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design 2 Nw (by norm_num))
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgRisk⟩ := hrisk f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro σ hσ s hs n hn
  change (∫ x, (unitLpLoss s (q2SpatialEstimator b 1 n (optimalLocalBandwidth 2 n) (σ⁻¹ • x)) g) ^ 2
    ∂featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)) ≤ _
  rw [featureGaussian_known_scale_integral _ σ hσ (fun x => (unitLpLoss s (q2SpatialEstimator b 1 n (optimalLocalBandwidth 2 n) x) g) ^ 2)]
  obtain ⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩ := hK n ((le_max_right N K).trans hn)
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram 1 n 2 (optimalLocalBandwidth 2 n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  let μ := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let F := q2SpatialEstimator b 1 n (optimalLocalBandwidth 2 n)
  have hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1 := by
    intro x t
    have hh := q2SpatialEstimator_mem b hb0 hb 1 n (optimalLocalBandwidth 2 n) x t
    exact ⟨hh.1, hh.2.trans hb.le⟩
  have hgb : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    fun t ht => ⟨ha.le.trans (hmap ht).1, (hmap ht).2.trans hb.le⟩
  have hFm := q2SpatialEstimator_joint_measurable b hb0 hb 1 n hn1 _ hdet
  have hi := integrated_mse_of_uniform μ F (fun t => g (clip 0 1 t)) (C * (lowerBoundRate 2 n) ^ 2)
    hFm (hg.comp (clip_continuous 0 1)).measurable hFb (fun t => hgb (clip_mem 0 1 t (by norm_num)))
    (by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      dsimp only [F]
      simp only [q2SpatialEstimator_agrees b 1 n _ _ t ht', clip_identity 0 1 t ht']
      exact hgRisk n ((le_max_left N K).trans hn) t ht')
  have he : (∫ x, (∫ t in Ioo (0 : ℝ) 1, (F x t - g (clip 0 1 t)) ^ 2) ∂μ) =
      ∫ x, (∫ t in Ioo (0 : ℝ) 1, (F x t - g t) ^ 2) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [clip_identity 0 1 t ⟨ht.1.le, ht.2.le⟩]
  rw [he] at hi
  have hlp := unitLpRisk_le_integrated_mse μ s hs.1 hs.2 F g hFm hg
    (fun x => q2SpatialEstimator_continuous b hb0 hb 1 n hn1 _ hdet x) hFb hgb
  exact hlp.trans hi

end Hurst
