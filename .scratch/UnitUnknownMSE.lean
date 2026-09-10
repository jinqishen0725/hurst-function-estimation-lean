import Hurst.UnknownEstimator
import Hurst.OptimalScaleRisk
import Hurst.BackfitTransfer
import Hurst.HolderQ2Rate

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst
set_option maxHeartbeats 800000

theorem hurstHolder_q2_unknown_unit_mse_rate (p a b M : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M, MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0:ℝ) 1) ∧ MapsTo g (Icc (0:ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0:ℝ) 1,
      (∫ x, (q2UnknownLocalEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) t x-g t)^2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤ C*(lowerBoundRate p n)^2 := by
  obtain ⟨Cr, hCr, Nr, hNr, hknown⟩ := hurstHolder_q2_uniform_mse_rate p a b M hp ha hb hab hM
  obtain ⟨Cs, hCs, Ns, hNs, hscale⟩ := hurstHolder_q2_optimal_scale_risk p a b M hp ha hb hab hM
  obtain ⟨E, hE, hmean⟩ := hurstHolder_grid_second_log_mean p a b M hp ha hb hab hM
  obtain ⟨K, hK⟩ := eventually_atTop.mp hmean
  let N := max Nr (max Ns K)
  refine ⟨2*Cr+Cs, by positivity, N, hNs.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgb, hr⟩ := hknown f hf hF
  refine ⟨g, hg, heq, hgb, ?_⟩
  intro n hn t ht
  have hnr : Nr ≤ n := (le_max_left _ _).trans hn
  have hns : Ns ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnk : K ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hn1 : 1 < n := by omega
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn1)
  let v := gridObservationFeatures n (midpointSampleHurst f hf.1 n)
  let X := gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n 2 (optimalLocalBandwidth p n) t) (gridSecondCoefficients n)
  let Y := q2LogScaleEstimator a b (Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n)
  have hX : MemLp X 2 (featureGaussian v) := gaussianLogStatistic_memLp_two v _ _ (fun i => (hK n hnk f hf hF i).1)
  obtain ⟨hY, hscaleR⟩ := hscale f hf hF n hns
  have he := boundedInverse_backfit_mse (featureGaussian v) X Y (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 b (2*Real.log n) (g t)
    (by positivity) (ha.le.trans hab) (calibrationTwo_continuousOn _ _ b hb) (calibrationTwo_strongDecrease _ _ b hb)
    ⟨ha.le.trans (hgb ht).1, (hgb ht).2⟩ hX hY
  apply he.trans
  have hrisk := hr n hnr t ht
  have hid : 2/(2*Real.log n)^2*(∫ x, (Y x)^2 ∂featureGaussian v) =
      ((∫ x, (Y x)^2 ∂featureGaussian v)/(Real.log n)^2)/2 := by ring
  rw [hid]
  have hpos : 0 ≤ Cs*(lowerBoundRate p n)^2 := mul_nonneg hCs (sq_nonneg _)
  change (∫ x, (q2LocalEstimator b (Nat.ceil p-1) n (optimalLocalBandwidth p n) t x-g t)^2 ∂featureGaussian v) ≤ _ at hrisk
  change 2*(∫ x, (q2LocalEstimator b (Nat.ceil p-1) n (optimalLocalBandwidth p n) t x-g t)^2 ∂featureGaussian v)+
    ((∫ x, (Y x)^2 ∂featureGaussian v)/(Real.log n)^2)/2 ≤ _
  nlinarith

end Hurst
