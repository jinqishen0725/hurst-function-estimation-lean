import Hurst.GridMSE

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_adjacent_grid_bound (p : ℝ) (hp : 1 ≤ p) :
    ∃ D > 0, ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      ∀ n : ℕ, 0 < n → ∀ i : Fin (n - 1),
      |(midpointSampleHurst f hf.1 n (firstDiffRight n i) : ℝ) - midpointSampleHurst f hf.1 n (firstDiffLeft n i)| ≤ D * (1 + M) / n := by
  obtain ⟨D, hD, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  refine ⟨D, hD, ?_⟩
  intro M hM f hf n hn i
  have hl := grid_mem n (firstDiffLeft n i).val hn (firstDiffLeft n i).isLt
  have hr := grid_mem n (firstDiffRight n i).val hn (firstDiffRight n i).isLt
  have hd : |grid n (firstDiffRight n i).val - grid n (firstDiffLeft n i).val| = 1 / (n : ℝ) := by
    rw [grid_firstDifference_step n i, add_sub_cancel_left, abs_of_nonneg (by positivity)]
  have h := hLip M hM f hf 0 (by have := hurstHolder_floor_pos p hp; omega) _ hl _ hr
  simpa only [iteratedDeriv_zero, hd, midpointSampleHurst, div_eq_mul_inv, one_mul] using h

def q1LocalEstimator (r n : ℕ) (δ t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  boundedInverse (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1
    (gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x)

/-- Full-interval MSE from the original Holder class, for the actual q=1 observation model. -/
theorem hurstHolder_q1_local_mse (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 3 / 4) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ Cb > 0, ∃ Cv ≥ 0, ∃ D > 0, ∃ Ce ≥ 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ∀ n : ℕ, N ≤ n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      (∫ x, (q1LocalEstimator (Nat.ceil p - 1) n δ t x - g t) ^ 2
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        2 * Cb ^ 2 * δ ^ (2 * p) + Cv / (4 * (n : ℝ) * δ * Real.log n ^ 2) +
          2 * D ^ 2 * (gridCovarianceError b Ce n) ^ 2 / Real.log n ^ 2 := by
  obtain ⟨L, hL, hstep⟩ := hurstHolder_adjacent_grid_bound p hp
  let B := L * (1 + M)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨Nv, hNv, Cv, hCv, hvar⟩ := actual_grid_local_log_variance a b B (Nat.ceil p - 1) ha hb hab hB
  obtain ⟨Ce, hCe, hmean⟩ := actual_grid_log_mean_sharp a b B ha (by linarith) hab hB
  obtain ⟨Nw, hNw, D, hD, hweights⟩ := localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨Nb, hNb, Cb, hCb, hbias⟩ := hurstHolder_localPolynomial_bias p hp 1
  refine ⟨max Nv (max Nw Nb), lt_of_lt_of_le hNv (le_max_left _ _), Cb * (1 + M), by positivity,
    Cv, hCv, D, hD, Ce, hCe, ?_⟩
  have hsmall := (gridCovarianceError_tendsto b Ce (by linarith)).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨N, hNall⟩ := eventually_atTop.mp (hvar.and (hsmall.and (eventually_ge_atTop 2)))
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hmap, hgbias⟩ := hbias M hM f hf
  refine ⟨g, hg, heq, hmap, ?_⟩
  intro n hnN δ t hδ hδhalf ht hN
  obtain ⟨hv, hs, hn⟩ := hNall n ((le_max_left N 2).trans hnN)
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let H := midpointSampleHurst f hf.1 n
  have hH : ∀ i, (H i : ℝ) ∈ Icc a b := fun i => hF _ (grid_mem n i.val hn0 i.isLt)
  have hHS : ∀ i : Fin (n - 1), |(H (firstDiffRight n i) : ℝ) - H (firstDiffLeft n i)| ≤ B / n :=
    hstep M hM f hf n hn0
  have hnv : Nv ≤ (n : ℝ) * δ := (le_max_left _ _).trans hN
  have hnw : Nw ≤ (n : ℝ) * δ := (le_max_left Nw Nb).trans ((le_max_right Nv _).trans hN)
  have hnb : Nb ≤ (n : ℝ) * δ := (le_max_right Nw Nb).trans ((le_max_right Nv _).trans hN)
  obtain ⟨hdet, hmax, hl1, hmom⟩ := hweights n hn0 (by omega) δ t hδ hδhalf ht hnw
  have hsum : ∑ i, localPolynomialWeights (Nat.ceil p - 1) n 1 δ t i = 1 := by
    simpa only [Fin.val_zero, pow_zero, mul_one, ite_true] using hmom 0
  have he0 : 0 ≤ gridCovarianceError b Ce n := by
    unfold gridCovarianceError
    have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  have hm := hmean n hn0 hs.le H hH hHS
  have hb' : |smooth (localPolynomialWeights (Nat.ceil p - 1) n 1 δ t) (fun i => (H (firstDiffLeft n i) : ℝ)) - g t| ≤
      (Cb * (1 + M)) * δ ^ p := by
    simpa only [H, midpointSampleHurst, firstDiffLeft] using hgbias n hn0 (by omega) δ hδ hδhalf hnb t ht
  have h := actual_q1_mse_from_mean_variance n (by omega) H (localPolynomialWeights (Nat.ceil p - 1) n 1 δ t)
    (g t) ((Cb * (1 + M)) * δ ^ p) D (2 * gridCovarianceError b Ce n) (Cv / ((n : ℝ) * δ))
    (hmap ht) (by positivity) hD.le (by positivity) hsum hl1 (fun i => (hm i).1) (fun i => (hm i).2) hb'
    (hv H hH hHS δ t hδ hδhalf ht hnv)
  apply h.trans_eq
  rw [mul_pow]
  have hpow : (δ ^ p) ^ 2 = δ ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hpow]
  ring

end Hurst
