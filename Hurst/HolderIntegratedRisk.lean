import Hurst.HolderGridRate
import Hurst.SpatialRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Actual squared L2 risk on the full interval, with a common threshold over the original class. -/
theorem hurstHolder_q1_integrated_mse_rate (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ n : ℕ, N ≤ n →
      (∫ x, (∫ t in Ioo (0 : ℝ) 1,
        (q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n) x t - g t) ^ 2)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
          C * (lowerBoundRate p n) ^ 2 := by
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q1_uniform_mse_rate p a b M hp ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design p Nw hp)
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgRisk⟩ := hrisk f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro n hn
  obtain ⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩ := hK n ((le_max_right N K).trans hn)
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  let μ := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let F := q1SpatialEstimator (Nat.ceil p - 1) n (optimalLocalBandwidth p n)
  have hi := integrated_mse_of_uniform μ F (fun t => g (clip 0 1 t)) (C * (lowerBoundRate p n) ^ 2)
    (q1SpatialEstimator_joint_measurable _ n hn1 _ hdet)
    (hg.comp (clip_continuous 0 1)).measurable
    (fun x t => q1SpatialEstimator_mem _ _ _ _ _) (fun t => hmap (clip_mem 0 1 t (by norm_num)))
    (by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      dsimp only [F]
      simp only [q1SpatialEstimator_agrees _ _ _ _ t ht', clip_identity 0 1 t ht']
      exact hgRisk n ((le_max_left N K).trans hn) t ht')
  have he : (∫ x, (∫ t in Ioo (0 : ℝ) 1, (F x t - g (clip 0 1 t)) ^ 2) ∂μ) =
      ∫ x, (∫ t in Ioo (0 : ℝ) 1, (F x t - g t) ^ 2) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [clip_identity 0 1 t ⟨ht.1.le, ht.2.le⟩]
  rwa [he] at hi

end Hurst
