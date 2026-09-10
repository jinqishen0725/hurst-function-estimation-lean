import Hurst.ActualLocalEvenMoment
import Hurst.EvenMomentAlgebra
import Hurst.HolderGridMSE
import Hurst.HolderQ2MSE

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

/-- Raw (pre-inversion) `2k` moment for the actual first-difference local
statistic, including its deterministic calibration bias. -/
theorem hurstHolder_q1_local_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C > 0, ∃ Cb > 0, ∃ D > 0, ∃ Ce ≥ 0,
      ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 →
      t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      (∫ x, |gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1 δ t)
          (gridDifferenceCoefficients n) x -
          calibrationOne (Real.log n) gaussianLogSquareMean (g t)| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        2 ^ (2 * k - 1) *
          (C / ((n : ℝ) * δ) ^ k +
            (2 * Real.log n * (Cb * δ ^ p) +
              2 * D * gridCovarianceError b Ce n) ^ (2 * k)) := by
  obtain ⟨Nm, hNm, C, hC, hmom⟩ := hurstHolder_local_first_averaged_evenMoment
    hBS k hk p a b M hp ha hb hab hM (Nat.ceil p - 1)
  obtain ⟨Lstep, hLstep, hstep⟩ := hurstHolder_adjacent_grid_bound p hp
  let Bstep := Lstep * (1 + M)
  have hBstep : 0 ≤ Bstep := by dsimp only [Bstep]; positivity
  obtain ⟨Ce, hCe, hmean⟩ :=
    actual_grid_log_mean_sharp a b Bstep ha (by linarith) hab hBstep
  obtain ⟨Nw, hNw, D, hD, hweights⟩ :=
    localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨Nb, hNb, Cb0, hCb0, hbias⟩ := hurstHolder_localPolynomial_bias p hp 1
  let Cb := Cb0 * (1 + M)
  have hCb : 0 < Cb := by dsimp only [Cb]; positivity
  let N₀ := max Nm (max Nw Nb)
  have hN₀ : 0 < N₀ := hNm.trans_le (le_max_left _ _)
  have hsmall := (gridCovarianceError_tendsto b Ce (by linarith)).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hmom.and (hsmall.and (eventually_ge_atTop 2)))
  refine ⟨N₀, hN₀, C, hC, Cb, hCb, D, hD, Ce, hCe,
    max K 2, le_max_right _ _, ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hg01, hgbias⟩ := hbias M hM f hf
  have hgmap := continuous_extension_fixed_range f g a b hg heq hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro n hn δ t hδ hδhalf ht hnδ
  obtain ⟨hmn, hsmalln, hn2⟩ := hK n ((le_max_left K 2).trans hn)
  have hn0 : 0 < n := by omega
  let H := midpointSampleHurst f hf.1 n
  let P := featureGaussian (gridObservationFeatures n H)
  let w := localPolynomialWeights (Nat.ceil p - 1) n 1 δ t
  let X := gaussianLogStatistic w (gridDifferenceCoefficients n)
  have hH : ∀ i, (H i : ℝ) ∈ Icc a b := fun i =>
    hF (grid_mem n i.val hn0 i.isLt)
  have hHS : ∀ i : Fin (n - 1),
      |(H (firstDiffRight n i) : ℝ) - H (firstDiffLeft n i)| ≤ Bstep / n := by
    simpa only [H, Bstep] using hstep M hM f hf n hn0
  have hm := hmean n hn0 hsmalln.le H hH hHS
  have hnw : Nw ≤ (n : ℝ) * δ :=
    (le_max_left Nw Nb).trans ((le_max_right Nm _).trans hnδ)
  have hnb : Nb ≤ (n : ℝ) * δ :=
    (le_max_right Nw Nb).trans ((le_max_right Nm _).trans hnδ)
  obtain ⟨_, _, hl1, hmomw⟩ := hweights n hn0 (by omega) δ t hδ hδhalf ht hnw
  have hsum : ∑ i, w i = 1 := by
    simpa only [w, Fin.val_zero, pow_zero, mul_one, ite_true] using hmomw 0
  have hfeat : ∀ i, ∑ j, gridDifferenceCoefficients n i j •
      gridObservationFeatures n H j ≠ 0 := fun i => (hm i).1
  let μi := fun i : Fin (n - 1) =>
    ∫ x, Real.log (⟪gridDifferenceCoefficients n i, x⟫ ^ 2) ∂P
  have hmu : (∫ x, X x ∂P) = smooth w μi := by
    unfold X gaussianLogStatistic smooth
    rw [integral_finsetSum _ (fun i _ =>
      ((featureGaussian_log_square_memLp_two _ _ (hfeat i)).integrable
        (by norm_num)).const_mul (w i))]
    simp only [integral_const_mul, μi, P]
  have hbpoly : |smooth w (fun i => (H (firstDiffLeft n i) : ℝ)) - g t| ≤
      Cb * δ ^ p := by
    simpa only [Cb, H, midpointSampleHurst, firstDiffLeft] using
      hgbias n hn0 (by omega) δ hδ hδhalf hnb t ht
  have hmeanerr : ∀ i, |μi i -
      (-2 * Real.log n * (H (firstDiffLeft n i) : ℝ) + gaussianLogSquareMean)| ≤
      2 * gridCovarianceError b Ce n := by
    intro i
    convert (hm i).2 using 1 <;> congr 1 <;> ring
  have he0 : 0 ≤ 2 * gridCovarianceError b Ce n := by
    unfold gridCovarianceError
    have hln := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
      exact_mod_cast (show 1 ≤ 2 * n by omega))
    positivity
  have hmeanBias := weighted_affine_bias_bound w
    (fun i => (H (firstDiffLeft n i) : ℝ)) μi (Real.log n)
    gaussianLogSquareMean (g t) (Cb * δ ^ p) D
    (2 * gridCovarianceError b Ce n) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    he0 hsum hl1 hbpoly hmeanerr
  rw [← hmu] at hmeanBias
  have hcenter := hmn f hf hF δ t hδ hδhalf ht
    ((le_max_left Nm _).trans hnδ)
  have hXmem := gaussianLogStatistic_memLp_finite
    (gridObservationFeatures n H) w (gridDifferenceCoefficients n) hfeat (2 * k : ℝ)
  have hXi : Integrable X P :=
    (gaussianLogStatistic_memLp_two _ _ _ hfeat).integrable one_le_two
  have hXcenter : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P := by
    have hc := hXmem.sub (memLp_const (c := ∫ y, X y ∂P))
    have hi := hc.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hraw := evenMoment_le_centered_add_bias P X
    (calibrationOne (Real.log n) gaussianLogSquareMean (g t)) k hk hXi hXcenter
  apply hraw.trans
  have hbpow := pow_le_pow_left₀ (abs_nonneg _) hmeanBias (2 * k)
  have hmeanBiasCal : |(∫ y, X y ∂P) -
      calibrationOne (Real.log n) gaussianLogSquareMean (g t)| ≤
      2 * Real.log n * (Cb * δ ^ p) + D * (2 * gridCovarianceError b Ce n) := by
    simpa only [calibrationOne] using hmeanBias
  calc
    2 ^ (2 * k - 1) *
        ((∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
          |(∫ y, X y ∂P) - calibrationOne (Real.log n) gaussianLogSquareMean (g t)| ^
            (2 * k)) ≤
      2 ^ (2 * k - 1) *
        (C / ((n : ℝ) * δ) ^ k +
          (2 * Real.log n * (Cb * δ ^ p) +
            D * (2 * gridCovarianceError b Ce n)) ^ (2 * k)) := by
      gcongr
    _ = 2 ^ (2 * k - 1) *
        (C / ((n : ℝ) * δ) ^ k +
          (2 * Real.log n * (Cb * δ ^ p) +
            2 * D * gridCovarianceError b Ce n) ^ (2 * k)) := by ring

/-- Raw (pre-inversion) `2k` moment for the actual second-difference local
statistic, including the nonlinear deterministic calibration bias. -/
theorem hurstHolder_q2_local_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ N₀ > 0, ∃ C > 0, ∃ Cb ≥ 0, ∃ D > 0, ∃ Ce ≥ 0,
      ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 →
      t ∈ Icc (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      (∫ x, |gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 2 δ t)
          (gridSecondCoefficients n) x -
          calibrationTwo (Real.log n) gaussianLogSquareMean (g t)| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        2 ^ (2 * k - 1) *
          (C / ((n : ℝ) * δ) ^ k +
            (2 * Real.log n * (Cb * δ ^ p) +
              D * gridCovarianceError (1 / 2) Ce n) ^ (2 * k)) := by
  obtain ⟨Nm, hNm, C, hC, hmom⟩ := hurstHolder_local_second_averaged_evenMoment
    hBS k hk p a b M hp ha hb hab hM (Nat.ceil p - 1)
  obtain ⟨Ce, hCe, hmean⟩ := hurstHolder_grid_second_log_mean
    p a b M hp ha hb hab hM
  obtain ⟨Nw, hNw, D, hD, hweights⟩ :=
    localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 2
  obtain ⟨Nb, hNb, Cb0, hCb0, hbias⟩ :=
    hurstHolder_localPolynomial_bias p (by linarith) 2
  obtain ⟨Nc, hNc, Cc, hCc, hcbias⟩ :=
    hurstHolder_smooth_composite_local_bias p a b M q2LogCorrection 2
      hp ha hb hM q2LogCorrection_smooth
  let Cb := Cb0 * (1 + M) + Cc
  have hCb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  let N₀ := max Nm (max Nw (max Nb Nc))
  have hN₀ : 0 < N₀ := hNm.trans_le (le_max_left _ _)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hmom.and (hmean.and ((Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))))
  refine ⟨N₀, hN₀, C, hC, Cb, hCb, D, hD, Ce, hCe,
    max K 2, le_max_right _ _, ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hg01, hgbias⟩ := hbias M hM f hf
  have hgmap := continuous_extension_fixed_range f g a b hg heq hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro n hn δ t hδ hδhalf ht hnδ
  obtain ⟨hmn, hmeann, hlog⟩ := hK n ((le_max_left K 2).trans hn)
  have hn0 : 0 < n := by omega
  let H := midpointSampleHurst f hf.1 n
  let P := featureGaussian (gridObservationFeatures n H)
  let w := localPolynomialWeights (Nat.ceil p - 1) n 2 δ t
  let X := gaussianLogStatistic w (gridSecondCoefficients n)
  have hnw : Nw ≤ (n : ℝ) * δ :=
    (le_max_left Nw (max Nb Nc)).trans ((le_max_right Nm _).trans hnδ)
  have hnb : Nb ≤ (n : ℝ) * δ :=
    (le_max_left Nb Nc).trans
      ((le_max_right Nw _).trans ((le_max_right Nm _).trans hnδ))
  have hnc : Nc ≤ (n : ℝ) * δ :=
    (le_max_right Nb Nc).trans
      ((le_max_right Nw _).trans ((le_max_right Nm _).trans hnδ))
  obtain ⟨_, _, hl1, hmomw⟩ := hweights n hn0 (by omega) δ t hδ hδhalf ht hnw
  have hsum : ∑ i, w i = 1 := by
    simpa only [w, Fin.val_zero, pow_zero, mul_one, ite_true] using hmomw 0
  have hm := hmeann f hf hF
  have hfeat : ∀ i, ∑ j, gridSecondCoefficients n i j •
      gridObservationFeatures n H j ≠ 0 := fun i => (hm i).1
  let μi := fun i : Fin (n - 2) =>
    ∫ x, Real.log (⟪gridSecondCoefficients n i, x⟫ ^ 2) ∂P
  have hmu : (∫ x, X x ∂P) = smooth w μi := by
    unfold X gaussianLogStatistic smooth
    rw [integral_finsetSum _ (fun i _ =>
      ((featureGaussian_log_square_memLp_two _ _ (hfeat i)).integrable
        (by norm_num)).const_mul (w i))]
    simp only [integral_const_mul, μi, P]
  have hbpoly : |smooth w (fun i => (H (secondDiffLeft n i) : ℝ)) - g t| ≤
      Cb0 * (1 + M) * δ ^ p := by
    simpa only [H, midpointSampleHurst, secondDiffLeft] using
      hgbias n hn0 (by omega) δ hδ hδhalf hnb t ht
  have hcomp : |smooth w (fun i => q2LogCorrection (H (secondDiffLeft n i))) -
      q2LogCorrection (g t)| ≤ Cc * δ ^ p := by
    simpa only [H, midpointSampleHurst, secondDiffLeft] using
      hcbias f hf hF g hg heq n hn0 (by omega) δ hδ hδhalf hnc t ht
  have hmeanerr : ∀ i, |μi i -
      (-2 * Real.log n * (H (secondDiffLeft n i) : ℝ) +
        q2LogCorrection (H (secondDiffLeft n i)) + gaussianLogSquareMean)| ≤
      gridCovarianceError (1 / 2) Ce n := by
    intro i
    convert (hm i).2 using 1 <;> congr 1 <;>
      simp only [μi, P, H, midpointSampleHurst, secondDiffLeft] <;> ring
  have he0 : 0 ≤ gridCovarianceError (1 / 2) Ce n := by
    unfold gridCovarianceError
    have hln := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
      exact_mod_cast (show 1 ≤ 2 * n by omega))
    positivity
  have hmeanBias := weighted_nonlinear_bias_bound w
    (fun i => (H (secondDiffLeft n i) : ℝ)) μi q2LogCorrection
    (Real.log n) gaussianLogSquareMean (g t)
    (Cb0 * (1 + M) * δ ^ p) (Cc * δ ^ p) D
    (gridCovarianceError (1 / 2) Ce n) hlog (by positivity) he0
    hsum hl1 hbpoly hcomp hmeanerr
  rw [← hmu] at hmeanBias
  have hmeanBias' : |(∫ y, X y ∂P) -
      calibrationTwo (Real.log n) gaussianLogSquareMean (g t)| ≤
      2 * Real.log n * (Cb * δ ^ p) + D * gridCovarianceError (1 / 2) Ce n := by
    have hcombine : Cb0 * (1 + M) * δ ^ p + Cc * δ ^ p = Cb * δ ^ p := by
      dsimp only [Cb]
      ring
    have hcal : calibrationTwo (Real.log n) gaussianLogSquareMean (g t) =
        gaussianLogSquareMean - 2 * Real.log n * g t + q2LogCorrection (g t) := rfl
    rw [hcal]
    simpa only [hcombine] using hmeanBias
  have hcenter := hmn f hf hF δ t hδ hδhalf ht
    ((le_max_left Nm _).trans hnδ)
  have hXmem := gaussianLogStatistic_memLp_finite
    (gridObservationFeatures n H) w (gridSecondCoefficients n) hfeat (2 * k : ℝ)
  have hXi : Integrable X P :=
    (gaussianLogStatistic_memLp_two _ _ _ hfeat).integrable one_le_two
  have hXcenter : Integrable (fun x => |X x - ∫ y, X y ∂P| ^ (2 * k)) P := by
    have hc := hXmem.sub (memLp_const (c := ∫ y, X y ∂P))
    have hi := hc.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * k),
      show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by norm_num] at hi
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.rpow_natCast] using hi
  have hraw := evenMoment_le_centered_add_bias P X
    (calibrationTwo (Real.log n) gaussianLogSquareMean (g t)) k hk hXi hXcenter
  apply hraw.trans
  calc
    2 ^ (2 * k - 1) *
        ((∫ x, |X x - ∫ y, X y ∂P| ^ (2 * k) ∂P) +
          |(∫ y, X y ∂P) - calibrationTwo (Real.log n) gaussianLogSquareMean (g t)| ^
            (2 * k)) ≤
      2 ^ (2 * k - 1) *
        (C / ((n : ℝ) * δ) ^ k +
          (2 * Real.log n * (Cb * δ ^ p) +
            D * gridCovarianceError (1 / 2) Ce n) ^ (2 * k)) := by
      gcongr

end Hurst
