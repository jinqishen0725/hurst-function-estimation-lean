import Hurst.SecondMSE
import Hurst.SmoothCompositeQuadratic
import Hurst.HolderGridMSE

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

def q2LocalEstimator (u : ℝ) (r n : ℕ) (δ t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  boundedInverse (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u
    (gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x)

/-- Full-interval q=2 MSE for the original p=2 class, with a common sample threshold. -/
theorem hurstHolder_q2_p2_local_mse (a b M : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ Cb ≥ 0, ∃ Cv ≥ 0, ∃ D > 0, ∃ Ce ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass 2 M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      (∫ x, (q2LocalEstimator b 1 n δ t x - g t) ^ 2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        2 * Cb ^ 2 * δ ^ 4 + Cv / (4 * (n : ℝ) * δ * Real.log n ^ 2) +
          D ^ 2 * (gridCovarianceError (1 / 2) Ce n) ^ 2 / (2 * Real.log n ^ 2) := by
  obtain ⟨Nv, hNv, Cv, hCv, hvar⟩ := hurstHolder_grid_second_log_variance 2 a b M 1 (by norm_num) ha hb hab hM
  obtain ⟨Ce, hCe, hmean⟩ := hurstHolder_grid_second_log_mean 2 a b M (by norm_num) ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hweights⟩ := localPolynomialWeights_uniform_stability 1 2
  obtain ⟨Nb, hNb, Cb, hCb, hbias⟩ := hurstHolder_localPolynomial_bias 2 (by norm_num) 2
  obtain ⟨Nc, hNc, Cc, hCc, hcbias⟩ := hurstHolder_smooth_composite_linear_bias 2 a b M q2LogCorrection 2
    (by norm_num) ha hb hM q2LogCorrection_smooth
  let N₀ := max Nv (max Nw (max Nb Nc))
  refine ⟨N₀, lt_of_lt_of_le hNv (le_max_left _ _), Cb * (1 + M) + Cc, by positivity,
    Cv, hCv, D, hD, Ce, hCe, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  obtain ⟨N, hNall⟩ := eventually_atTop.mp (hvar.and (hmean.and (hlog.and (eventually_ge_atTop 2))))
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro f hf hF
  obtain ⟨g, hg, hfg, hg01, hgbias⟩ := hbias M hM f hf
  have hgmap := continuous_extension_fixed_range f g a b hg hfg hF
  refine ⟨g, hg, hfg, hgmap, ?_⟩
  intro n hn δ t hδ hδhalf ht hN
  obtain ⟨hvn, hmn, hLn, hn2⟩ := hNall n (le_trans (le_max_left _ _) hn)
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let H := midpointSampleHurst f hf.1 n
  have hNw' : Nw ≤ (n : ℝ) * δ := (le_trans (le_max_left Nw (max Nb Nc)) (le_max_right Nv _)).trans hN
  have hNb' : Nb ≤ (n : ℝ) * δ := (le_trans (le_max_left Nb Nc) (le_trans (le_max_right Nw _) (le_max_right Nv _))).trans hN
  have hNc' : Nc ≤ (n : ℝ) * δ := (le_trans (le_max_right Nb Nc) (le_trans (le_max_right Nw _) (le_max_right Nv _))).trans hN
  obtain ⟨hdet, hmax, hl1, hmom⟩ := hweights n hn0 hn2 δ t hδ hδhalf ht hNw'
  have hw : ∑ i, localPolynomialWeights 1 n 2 δ t i = 1 := by
    simpa using hmom 0
  have hb0 := hgbias n hn0 hn2 δ hδ hδhalf hNb' t ht
  norm_num only [show Nat.ceil (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_ofNat] at hb0
  have hb1 := hcbias f hf hF g hg hfg n hn0 hn2 δ hδ hδhalf hNc' t ht
  have hθ : g t ∈ Icc (0 : ℝ) b := ⟨ha.le.trans (hgmap ht).1, (hgmap ht).2⟩
  have he0 : 0 ≤ gridCovarianceError (1 / 2) Ce n := by
    unfold gridCovarianceError
    have hln := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by exact_mod_cast (show 1 ≤ 2 * n by omega))
    positivity
  have hmse := actual_q2_mse_from_mean_variance n (by omega) hLn H (localPolynomialWeights 1 n 2 δ t)
    b (g t) (Cb * (1 + M) * δ ^ 2) (Cc * δ ^ 2) D (gridCovarianceError (1 / 2) Ce n)
    (Cv / ((n : ℝ) * δ)) hb hθ (by positivity) (by positivity) hD.le he0 hw hl1
    (fun i => (hmn f hf hF i).1) (fun i => (hmn f hf hF i).2) hb0 hb1
    (hvn f hf hF δ t hδ hδhalf ht ((le_max_left _ _).trans hN))
  exact hmse.trans_eq (by ring)

end Hurst
