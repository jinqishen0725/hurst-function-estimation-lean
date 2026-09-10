import Hurst.FirstUnknownMSE
import Hurst.SecondSpatial
import Hurst.KnownScaleRisk
import Hurst.UnitLpRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Full-interval optimal squared Ls risk for the actual unknown-scale q=1 estimator. -/
theorem hurstHolder_q1_unknown_Lp_risk (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3/4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ σ : ℝ, σ ≠ 0 → ∀ s ∈ Icc (1 : ℝ) 2, ∀ n : ℕ, N ≤ n →
      (∫ x, (unitLpLoss s (q1UnknownSpatialEstimator (Nat.ceil p - 1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x) g) ^ 2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤
          C * (lowerBoundRate p n) ^ 2 := by
  obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q1_unknown_mse_rate p a b M hp ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hw⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (optimalLocalBandwidth_eventual_design p Nw (by linarith))
  refine ⟨C, hC, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgRisk⟩ := hrisk f hf hF
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro σ hσ s hs n hn
  obtain ⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩ := hK n ((le_max_right N K).trans hn)
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t).det :=
    fun t ht => (hw n (by omega) (by omega) _ t hδ hδhalf ht hnd).1
  let μ := scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)
  haveI : IsProbabilityMeasure μ := by dsimp [μ, scaledHarmonizableGaussian]; infer_instance
  let F := q1UnknownSpatialEstimator (Nat.ceil p - 1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n)
  have hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1 := by
    intro x t
    have hh := q1UnknownSpatialEstimator_mem (Nat.ceil p - 1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x t
    exact hh
  have hgb : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    hmap
  have hFm := q1UnknownSpatialEstimator_joint_measurable (Nat.ceil p - 1) n (scaleAverageResolution p n) hn1 _ hdet
  have hi := integrated_mse_of_uniform μ F (fun t => g (clip 0 1 t)) (C * (lowerBoundRate p n) ^ 2)
    hFm (hg.comp (clip_continuous 0 1)).measurable hFb (fun t => hgb (clip_mem 0 1 t (by norm_num)))
    (by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      dsimp only [F]
      simp only [q1UnknownSpatialEstimator_agrees (Nat.ceil p - 1) n (scaleAverageResolution p n) _ _ t ht', clip_identity 0 1 t ht']
      exact hgRisk σ hσ n ((le_max_left N K).trans hn) t ht')
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
    (fun x => q1UnknownSpatialEstimator_continuous (Nat.ceil p - 1) n (scaleAverageResolution p n) hn1 _ hdet x) hFb hgb
  exact hlp.trans hi

end Hurst
