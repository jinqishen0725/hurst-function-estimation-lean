import Hurst.ActualPilotEvenMoment
import Hurst.EvenMomentAlgebra

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_q2Pilot_evenMoment_about_extension
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ Cp > 0, ∃ B ≥ 0, ∃ E ≥ 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ n : ℕ, N ≤ n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 →
        t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      (∫ x, |q2Pilot (Nat.ceil p - 1) n δ t x - g t| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        2 ^ (2 * k - 1) *
          (Cp / ((n : ℝ) * δ) ^ k +
            (B * δ ^ p + gridCovarianceError (1 / 2) E n) ^ (2 * k)) := by
  let r := Nat.ceil p - 1
  obtain ⟨Nc, hNc, Cp, hCp, hcenter⟩ :=
    hurstHolder_q2Pilot_centered_evenMoment hBS k hk p a b M hp ha hb hab hM r
  obtain ⟨Nb, hNb, B, hB, E, hE, V, hV, Np, hNp, hpilot⟩ :=
    hurstHolder_q2_pilot_moments p a b M hp ha hb hab hM
  obtain ⟨_, _, hz₁⟩ := hurstHolder_common_stride_log_mean
    p a b M 1 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨_, _, hz₂⟩ := hurstHolder_common_stride_log_mean
    p a b M 2 4 hp ha hb hab hM (by omega) (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hcenter.and (hz₁.and hz₂))
  let N₀ := max Nc Nb
  let N := max Np K
  refine ⟨N₀, lt_of_lt_of_le hNc (le_max_left _ _), Cp, hCp, B, hB, E, hE,
    N, hNp.trans (le_max_left _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgmap, hpb⟩ := hpilot f hf hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro n hn δ t hδ hδhalf ht hnδ
  obtain ⟨hcent, hnz1, hnz2⟩ := hK n ((le_max_right _ _).trans hn)
  obtain ⟨hmem, hbias, _⟩ := hpb n ((le_max_left _ _).trans hn)
    δ t hδ hδhalf ht ((le_max_right _ _).trans hnδ)
  have hc := hcent f hf hF δ t hδ hδhalf ht ((le_max_left _ _).trans hnδ)
  let P := featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let w := localPolynomialWeights r n 4 δ t
  let a₁ := commonStrideCoefficients n 1 4 (by omega)
  let a₂ := commonStrideCoefficients n 2 4 (by omega)
  have hfeat₁ : ∀ i, ∑ j, a₁ i j • v j ≠ 0 := fun i => (hnz1 f hf hF i).1
  have hfeat₂ : ∀ i, ∑ j, a₂ i j • v j ≠ 0 := fun i => (hnz2 f hf hF i).1
  have hpow := twoScalePilot_centered_evenPower_integrable v w a₁ a₂ hfeat₁ hfeat₂ k
  have hraw := evenMoment_le_centered_add_bias P
    (q2Pilot r n δ t) (g t) k hk (hmem.integrable one_le_two) hpow
  apply hraw.trans
  have hbpow := pow_le_pow_left₀ (abs_nonneg _) hbias (2 * k)
  gcongr

end Hurst
