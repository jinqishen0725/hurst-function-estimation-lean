import Hurst.ActualPilot
import Hurst.PilotScale

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

theorem hurstHolder_q2_pilot_mse_unknown_scale (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ V ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧ MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ σ : ℝ, σ ≠ 0 → ∀ n : ℕ, N ≤ n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1/2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n:ℝ)*δ →
      (∫ x, (q2Pilot (Nat.ceil p-1) n δ t x-g t)^2
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ≤
        V/((n:ℝ)*δ) + 2*(B*δ^p)^2 + 2*(gridCovarianceError (1/2) E n)^2 := by
  obtain ⟨N₀, hN₀, B, hB, E, hE, V, hV, N, hN, hpilot⟩ := hurstHolder_q2_pilot_moments p a b M hp ha hb hab hM
  obtain ⟨E₁, _, hm₁⟩ := hurstHolder_common_stride_log_mean p a b M 1 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨E₂, _, hm₂⟩ := hurstHolder_common_stride_log_mean p a b M 2 4 hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hm₁.and hm₂)
  refine ⟨N₀, hN₀, B, hB, E, hE, V, hV, max N K, hN.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgb, hgpilot⟩ := hpilot f hf hF
  refine ⟨g, hg, heq, hgb, ?_⟩
  intro σ hσ n hn δ t hδ hδhalf ht hnd
  obtain ⟨hmem, hmean, hvar⟩ := hgpilot n ((le_max_left N K).trans hn) δ t hδ hδhalf ht hnd
  obtain ⟨hm1, hm2⟩ := hK n ((le_max_right N K).trans hn)
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := localPolynomialWeights (Nat.ceil p-1) n 4 δ t
  let a₁ := commonStrideCoefficients n 1 4 (by norm_num)
  let a₂ := commonStrideCoefficients n 2 4 (by norm_num)
  have hs := twoScalePilot_scale_integral v w a₁ a₂
    (fun i => (hm1 f hf hF i).1) (fun i => (hm2 f hf hF i).1) σ hσ (fun z => (z-g t)^2)
  change (∫ x, (twoScalePilot (gaussianLogStatistic w a₁) (gaussianLogStatistic w a₂) x-g t)^2
    ∂featureGaussian (fun i => σ • v i)) ≤ _
  rw [hs]
  change (∫ x, (q2Pilot (Nat.ceil p-1) n δ t x-g t)^2 ∂featureGaussian v) ≤ _
  rw [mse_decomposition _ _ hmem]
  have hb := pow_le_pow_left₀ (abs_nonneg _) hmean 2
  rw [sq_abs] at hb
  nlinarith [sq_nonneg (B*δ^p-gridCovarianceError (1/2) E n)]

end Hurst
