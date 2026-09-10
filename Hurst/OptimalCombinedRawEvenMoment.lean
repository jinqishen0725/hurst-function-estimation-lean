import Hurst.ActualCombinedRawEvenMoment
import Hurst.ScaleBandwidth

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace Hurst

theorem optimal_bandwidth_bias_even_power (p : ℝ) (n k : ℕ)
    (hn : 1 < n) (kpos : 1 ≤ k) :
    ((optimalLocalBandwidth p n) ^ p) ^ (2 * k) =
      (lowerBoundRate p n) ^ (2 * k) := by
  have hδ := optimalLocalBandwidth_pos p n hn
  have htwo : ((optimalLocalBandwidth p n) ^ p) ^ 2 =
      (optimalLocalBandwidth p n) ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [show 2 * k = 2 * k from rfl, pow_mul, htwo,
    optimalLocalBandwidth_bias_balance, ← pow_mul]

theorem optimal_bandwidth_local_even_power (p : ℝ) (hp : 1 ≤ p)
    (n k : ℕ) (hn : 1 < n) :
    1 / ((n : ℝ) * optimalLocalBandwidth p n) ^ k =
      (Real.log n * lowerBoundRate p n) ^ (2 * k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ := optimalLocalBandwidth_pos p n hn
  have hL := Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hv := optimalLocalBandwidth_variance_balance p hp n hn
  have hbase : 1 / ((n : ℝ) * optimalLocalBandwidth p n) =
      (Real.log n * lowerBoundRate p n) ^ 2 := by
    calc
      1 / ((n : ℝ) * optimalLocalBandwidth p n) =
          Real.log n ^ 2 *
            (1 / ((n : ℝ) * optimalLocalBandwidth p n * Real.log n ^ 2)) := by
        field_simp [hnR.ne', hδ.ne', hL.ne']
      _ = Real.log n ^ 2 * lowerBoundRate p n ^ 2 := by rw [hv]
      _ = _ := by ring
  rw [one_div, ← inv_pow, ← one_div, hbase, ← pow_mul]

theorem grid_error_even_power_le_optimal
    (p e : ℝ) (hp : 1 ≤ p) (n k : ℕ) (hk : 1 ≤ k)
    (hn : 1 < n) (hlog : 1 ≤ Real.log n)
    (hrate : 1 / (n : ℝ) ≤ lowerBoundRate p n ^ 2)
    (he : (n : ℝ) * e ^ 2 ≤ 1) :
    e ^ (2 * k) ≤ (lowerBoundRate p n) ^ (2 * k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < lowerBoundRate p n := by unfold lowerBoundRate; positivity
  have he2 : e ^ 2 ≤ 1 / (n : ℝ) := (le_div_iff₀ hnR).mpr (by
    simpa only [mul_comm] using he)
  have hepow : e ^ (2 * k) ≤ (lowerBoundRate p n) ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg e) (he2.trans hrate) k
  exact hepow

theorem gridCovarianceError_nonneg_of_constant
    (b C : ℝ) (n : ℕ) (hC : 0 ≤ C) (hn : 0 < n) :
    0 ≤ gridCovarianceError b C n := by
  unfold gridCovarianceError
  have hn2 : (1 : ℝ) ≤ 2 * n := by
    exact_mod_cast (show 1 ≤ 2 * n by omega)
  exact mul_nonneg
    (mul_nonneg hC (add_nonneg zero_le_one (Real.log_nonneg hn2)))
    (add_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _))

/-- The complete q1 unit-scale raw moment at the paper's bandwidth and scale
grid, with all explicit remainders absorbed into the minimax rate. -/
theorem hurstHolder_q1_optimal_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 2 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x, |(gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1 (optimalLocalBandwidth p n) t)
          (gridDifferenceCoefficients n) x -
          q1LogScaleEstimator (Nat.ceil p - 1) n (scaleAverageResolution p n)
            (optimalLocalBandwidth p n) x) -
          calibrationOne (Real.log n) gaussianLogSquareMean (g t)| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        (C * Real.log n * lowerBoundRate p n) ^ (2 * k) := by
  obtain ⟨N₀, hN₀, Cl, hCl, Cb, hCb, D, hD, El, hEl,
    Cs, hCs, Es, hEs, Nc, hNc, hcombined⟩ :=
    hurstHolder_q1_combined_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  have heEl := (gridCovarianceError_square_row_tendsto b El hb).eventually_le_const
    zero_lt_one
  have heEs := (gridCovarianceError_square_row_tendsto b Es hb).eventually_le_const
    zero_lt_one
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((optimalLocalBandwidth_eventual_design p N₀ hp).and (heEl.and heEs))
  let A : ℝ := 2 ^ (2 * k - 1) *
    (2 ^ (2 * k - 1) *
      (Cl + 2 ^ (2 * k - 1) * ((2 * Cb) ^ (2 * k) + (2 * D) ^ (2 * k))) +
     2 ^ (2 * k - 1) * (Cs + 1))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let C := A + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let N := max Nc (max K 2)
  refine ⟨C, hC, N, (le_max_right K 2).trans (le_max_right _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgmap, hraw⟩ := hcombined f hf hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro n hn t ht
  obtain ⟨hdesign, heElN, heEsN⟩ := hK n
    ((le_max_left K 2).trans ((le_max_right Nc _).trans hn))
  obtain ⟨hn1, hδ, hδhalf, hnδ, hrate, hlog⟩ := hdesign
  obtain ⟨hm, hmδ⟩ := scaleAverageResolution_design p n hδ
  have hbase := hraw n ((le_max_left Nc _).trans hn) hlog
    (scaleAverageResolution p n) hm (optimalLocalBandwidth p n) t hδ hδhalf ht hnδ hmδ
  let z := Real.log n * lowerBoundRate p n
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    exact mul_nonneg (by linarith) (by unfold lowerBoundRate; positivity)
  have hloc : 1 / ((n : ℝ) * optimalLocalBandwidth p n) ^ k = z ^ (2 * k) := by
    simpa only [z] using optimal_bandwidth_local_even_power p hp n k hn1
  have hbias : ((optimalLocalBandwidth p n) ^ p) ^ (2 * k) =
      (lowerBoundRate p n) ^ (2 * k) :=
    optimal_bandwidth_bias_even_power p n k hn1 hk
  have hLb : (Real.log n * (optimalLocalBandwidth p n) ^ p) ^ (2 * k) =
      z ^ (2 * k) := by
    rw [mul_pow, hbias]
    dsimp only [z]
    rw [mul_pow]
  have hElN' := grid_error_even_power_le_optimal p (gridCovarianceError b El n)
    hp n k hk hn1 hlog hrate heElN
  have hEsN' := grid_error_even_power_le_optimal p (gridCovarianceError b Es n)
    hp n k hk hn1 hlog hrate heEsN
  have hLEs : (Real.log n * gridCovarianceError b Es n) ^ (2 * k) ≤ z ^ (2 * k) := by
    rw [mul_pow]
    dsimp only [z]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hEsN' (pow_nonneg (by linarith : 0 ≤ Real.log n) _)
  have hlocalBias :
      (2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) +
        2 * D * gridCovarianceError b El n) ^ (2 * k) ≤
      2 ^ (2 * k - 1) * ((2 * Cb) ^ (2 * k) + (2 * D) ^ (2 * k)) *
        z ^ (2 * k) := by
    have hEl0 : 0 ≤ gridCovarianceError b El n := by
      unfold gridCovarianceError
      have hn2 : (1 : ℝ) ≤ 2 * n := by
        exact_mod_cast (show 1 ≤ 2 * n by omega)
      exact mul_nonneg
        (mul_nonneg hEl (add_nonneg zero_le_one (Real.log_nonneg hn2)))
        (add_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by positivity) _))
    have hsum := add_pow_le
      (show 0 ≤ 2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) by
        exact mul_nonneg (mul_nonneg (by positivity) (by linarith))
          (mul_nonneg hCb.le (Real.rpow_nonneg hδ.le _)))
      (show 0 ≤ 2 * D * gridCovarianceError b El n by
        exact mul_nonneg (mul_nonneg (by positivity) hD.le) hEl0) (2 * k)
    apply hsum.trans
    have hfirst : (2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p)) ^
        (2 * k) = (2 * Cb) ^ (2 * k) * z ^ (2 * k) := by
      rw [show 2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) =
        (2 * Cb) * (Real.log n * (optimalLocalBandwidth p n) ^ p) by ring,
        mul_pow, hLb]
    have hsecond : (2 * D * gridCovarianceError b El n) ^ (2 * k) ≤
        (2 * D) ^ (2 * k) * z ^ (2 * k) := by
      rw [show 2 * D * gridCovarianceError b El n =
        (2 * D) * gridCovarianceError b El n by ring, mul_pow]
      exact mul_le_mul_of_nonneg_left
        (hElN'.trans (pow_le_pow_left₀
          (by unfold lowerBoundRate; positivity)
          (show lowerBoundRate p n ≤ z by dsimp only [z]; nlinarith)
          (2 * k))) (pow_nonneg (by positivity) _)
    rw [hfirst]
    calc
      2 ^ (2 * k - 1) *
          ((2 * Cb) ^ (2 * k) * z ^ (2 * k) +
            (2 * D * gridCovarianceError b El n) ^ (2 * k)) ≤
        2 ^ (2 * k - 1) *
          ((2 * Cb) ^ (2 * k) * z ^ (2 * k) +
            (2 * D) ^ (2 * k) * z ^ (2 * k)) := by gcongr
      _ = 2 ^ (2 * k - 1) * ((2 * Cb) ^ (2 * k) +
          (2 * D) ^ (2 * k)) * z ^ (2 * k) := by ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscaleCenter : Cs * Real.log n ^ (2 * k) / (n : ℝ) ^ k ≤
      Cs * z ^ (2 * k) := by
    have hnrate : 1 / (n : ℝ) ^ k ≤ (lowerBoundRate p n) ^ (2 * k) := by
      rw [one_div, ← inv_pow, ← one_div, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hrate k
    calc
      Cs * Real.log n ^ (2 * k) / (n : ℝ) ^ k =
          Cs * Real.log n ^ (2 * k) * (1 / (n : ℝ) ^ k) := by ring
      _ ≤ Cs * Real.log n ^ (2 * k) * lowerBoundRate p n ^ (2 * k) := by
        gcongr
      _ = Cs * z ^ (2 * k) := by dsimp only [z]; rw [mul_pow]; ring
  have hlocalVar : Cl / ((n : ℝ) * optimalLocalBandwidth p n) ^ k =
      Cl * z ^ (2 * k) := by
    rw [div_eq_mul_inv, ← one_div, hloc]
  have hlocalBlock :
      2 ^ (2 * k - 1) *
          (Cl / ((n : ℝ) * optimalLocalBandwidth p n) ^ k +
            (2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) +
              2 * D * gridCovarianceError b El n) ^ (2 * k)) ≤
        2 ^ (2 * k - 1) *
          (Cl + 2 ^ (2 * k - 1) *
            ((2 * Cb) ^ (2 * k) + (2 * D) ^ (2 * k))) * z ^ (2 * k) := by
    rw [hlocalVar]
    calc
      _ ≤ 2 ^ (2 * k - 1) *
          (Cl * z ^ (2 * k) +
            (2 ^ (2 * k - 1) * ((2 * Cb) ^ (2 * k) + (2 * D) ^ (2 * k))) *
              z ^ (2 * k)) := by gcongr
      _ = _ := by ring
  have hscaleBlock :
      2 ^ (2 * k - 1) *
          (Cs * Real.log n ^ (2 * k) / (n : ℝ) ^ k +
            (Real.log n * gridCovarianceError b Es n) ^ (2 * k)) ≤
        2 ^ (2 * k - 1) * (Cs + 1) * z ^ (2 * k) := by
    calc
      _ ≤ 2 ^ (2 * k - 1) * (Cs * z ^ (2 * k) + z ^ (2 * k)) := by
        gcongr
      _ = _ := by ring
  apply hbase.trans
  calc
    _ ≤ A * z ^ (2 * k) := by
      dsimp only [A]
      calc
        _ ≤ 2 ^ (2 * k - 1) *
            (2 ^ (2 * k - 1) *
                (Cl + 2 ^ (2 * k - 1) *
                  ((2 * Cb) ^ (2 * k) + (2 * D) ^ (2 * k))) * z ^ (2 * k) +
              2 ^ (2 * k - 1) * (Cs + 1) * z ^ (2 * k)) := by gcongr
        _ = _ := by ring
    _ ≤ C ^ (2 * k) * z ^ (2 * k) := by
      gcongr
      exact (le_add_of_nonneg_right zero_le_one).trans
        (le_self_pow₀ (show 1 ≤ C by dsimp only [C]; linarith) (by omega))
    _ = (C * Real.log n * lowerBoundRate p n) ^ (2 * k) := by
      dsimp only [z]
      rw [mul_pow, mul_pow]
      ring

/-- The complete q2 unit-scale raw moment at the paper's bandwidth and scale
grid, with all explicit remainders absorbed into the minimax rate. -/
theorem hurstHolder_q2_optimal_raw_evenMoment
    (hBS : BardetSurgailisLemmaOneScalar) (k : ℕ) (hk : 1 ≤ k)
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C > 0, ∃ N : ℕ, 4 ≤ N ∧
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∃ g : ℝ → ℝ, Continuous g ∧ EqOn f g (Ioo (0 : ℝ) 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc a b) ∧
      ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x, |(gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 2 (optimalLocalBandwidth p n) t)
          (gridSecondCoefficients n) x -
          q2LogScaleEstimator a b (Nat.ceil p - 1) n (scaleAverageResolution p n)
            (optimalLocalBandwidth p n) x) -
          calibrationTwo (Real.log n) gaussianLogSquareMean (g t)| ^ (2 * k)
        ∂featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))) ≤
        (C * Real.log n * lowerBoundRate p n) ^ (2 * k) := by
  obtain ⟨N₀, hN₀, Cl, hCl, Cb, hCb, D, hD, El, hEl,
    Cs, hCs, Bs, hBs, Es, hEs, Cp, hCp, Bp, hBp, Ep, hEp, L, hL,
    Nc, hNc, hcombined⟩ :=
    hurstHolder_q2_combined_raw_evenMoment hBS k hk p a b M hp ha hb hab hM
  have heEl := (gridCovarianceError_square_row_tendsto (1 / 2) El (by norm_num)).eventually_le_const
    zero_lt_one
  have heEs := (gridCovarianceError_square_row_tendsto (1 / 2) Es (by norm_num)).eventually_le_const
    zero_lt_one
  have heEp := (gridCovarianceError_square_row_tendsto (1 / 2) Ep (by norm_num)).eventually_le_const
    zero_lt_one
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((optimalLocalBandwidth_eventual_design p N₀ (by linarith)).and
      (heEl.and (heEs.and heEp)))
  let P : ℝ := 2 ^ (2 * k - 1)
  let A : ℝ := P *
    (P * (Cl + P * ((2 * Cb) ^ (2 * k) + D ^ (2 * k))) +
     P * (P * (Cs + P * (Bs ^ (2 * k) + 1)) +
       L ^ (2 * k) * P * (Cp + P * (Bp ^ (2 * k) + 1))))
  have hA : 0 ≤ A := by dsimp only [A, P]; positivity
  let C := A + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let N := max Nc (max K 4)
  refine ⟨C, hC, N, (le_max_right K 4).trans (le_max_right _ _), ?_⟩
  intro f hf hF
  obtain ⟨g, hg, heq, hgmap, hraw⟩ := hcombined f hf hF
  refine ⟨g, hg, heq, hgmap, ?_⟩
  intro n hn t ht
  obtain ⟨hdesign, heElN, heEsN, heEpN⟩ := hK n
    ((le_max_left K 4).trans ((le_max_right Nc _).trans hn))
  obtain ⟨hn1, hδ, hδhalf, hnδ, hrate, hlog⟩ := hdesign
  obtain ⟨hm, hmδ⟩ := scaleAverageResolution_design p n hδ
  have hbase := hraw n ((le_max_left Nc _).trans hn) hlog
    (scaleAverageResolution p n) hm (optimalLocalBandwidth p n) t hδ hδhalf ht hnδ hmδ
  let z := Real.log n * lowerBoundRate p n
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    exact mul_nonneg (by linarith) (by unfold lowerBoundRate; positivity)
  have hr0 : 0 ≤ lowerBoundRate p n := by unfold lowerBoundRate; positivity
  have hrz : lowerBoundRate p n ≤ z := by
    dsimp only [z]
    nlinarith
  have hloc : 1 / ((n : ℝ) * optimalLocalBandwidth p n) ^ k = z ^ (2 * k) := by
    simpa only [z] using optimal_bandwidth_local_even_power p (by linarith) n k hn1
  have hbias : ((optimalLocalBandwidth p n) ^ p) ^ (2 * k) =
      (lowerBoundRate p n) ^ (2 * k) :=
    optimal_bandwidth_bias_even_power p n k hn1 hk
  have hbiasZ : ((optimalLocalBandwidth p n) ^ p) ^ (2 * k) ≤ z ^ (2 * k) := by
    rw [hbias]
    exact pow_le_pow_left₀ hr0 hrz _
  have hLb : (Real.log n * (optimalLocalBandwidth p n) ^ p) ^ (2 * k) =
      z ^ (2 * k) := by
    rw [mul_pow, hbias]
    dsimp only [z]
    rw [mul_pow]
  have hElN' := grid_error_even_power_le_optimal p
    (gridCovarianceError (1 / 2) El n) (by linarith) n k hk hn1 hlog hrate heElN
  have hEsN' := grid_error_even_power_le_optimal p
    (gridCovarianceError (1 / 2) Es n) (by linarith) n k hk hn1 hlog hrate heEsN
  have hEpN' := grid_error_even_power_le_optimal p
    (gridCovarianceError (1 / 2) Ep n) (by linarith) n k hk hn1 hlog hrate heEpN
  have hgridZ (E : ℝ) (hE : 0 ≤ E)
      (he : gridCovarianceError (1 / 2) E n ^ (2 * k) ≤
        lowerBoundRate p n ^ (2 * k)) :
      gridCovarianceError (1 / 2) E n ^ (2 * k) ≤ z ^ (2 * k) :=
    he.trans (pow_le_pow_left₀ hr0 hrz _)
  have hElZ := hgridZ El hEl hElN'
  have hEsZ := hgridZ Es hEs hEsN'
  have hEpZ := hgridZ Ep hEp hEpN'
  have hLEs : (Real.log n * gridCovarianceError (1 / 2) Es n) ^ (2 * k) ≤
      z ^ (2 * k) := by
    rw [mul_pow]
    dsimp only [z]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hEsN' (pow_nonneg (by linarith) _)
  have hn0 : 0 < n := by omega
  have hEl0 := gridCovarianceError_nonneg_of_constant (1 / 2) El n hEl hn0
  have hEs0 := gridCovarianceError_nonneg_of_constant (1 / 2) Es n hEs hn0
  have hEp0 := gridCovarianceError_nonneg_of_constant (1 / 2) Ep n hEp hn0
  have hlocalBias :
      (2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) +
        D * gridCovarianceError (1 / 2) El n) ^ (2 * k) ≤
      P * ((2 * Cb) ^ (2 * k) + D ^ (2 * k)) * z ^ (2 * k) := by
    have hsum := add_pow_le
      (show 0 ≤ 2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) by
        exact mul_nonneg (mul_nonneg (by positivity) (by linarith))
          (mul_nonneg hCb (Real.rpow_nonneg hδ.le _)))
      (show 0 ≤ D * gridCovarianceError (1 / 2) El n by positivity) (2 * k)
    apply hsum.trans
    have hfirst : (2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p)) ^
        (2 * k) = (2 * Cb) ^ (2 * k) * z ^ (2 * k) := by
      rw [show 2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) =
        (2 * Cb) * (Real.log n * (optimalLocalBandwidth p n) ^ p) by ring,
        mul_pow, hLb]
    have hsecond : (D * gridCovarianceError (1 / 2) El n) ^ (2 * k) ≤
        D ^ (2 * k) * z ^ (2 * k) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hElZ (pow_nonneg hD.le _)
    rw [hfirst]
    dsimp only [P]
    calc
      _ ≤ 2 ^ (2 * k - 1) *
          ((2 * Cb) ^ (2 * k) * z ^ (2 * k) + D ^ (2 * k) * z ^ (2 * k)) := by
            gcongr
      _ = _ := by ring
  have hscaleBias :
      (Bs * Real.log n * (optimalLocalBandwidth p n) ^ p +
        Real.log n * gridCovarianceError (1 / 2) Es n) ^ (2 * k) ≤
      P * (Bs ^ (2 * k) + 1) * z ^ (2 * k) := by
    have hsum := add_pow_le
      (show 0 ≤ Bs * Real.log n * (optimalLocalBandwidth p n) ^ p by
        exact mul_nonneg (mul_nonneg hBs (by linarith)) (Real.rpow_nonneg hδ.le _))
      (show 0 ≤ Real.log n * gridCovarianceError (1 / 2) Es n by positivity) (2 * k)
    apply hsum.trans
    have hfirst : (Bs * Real.log n * (optimalLocalBandwidth p n) ^ p) ^ (2 * k) =
        Bs ^ (2 * k) * z ^ (2 * k) := by
      rw [show Bs * Real.log n * (optimalLocalBandwidth p n) ^ p =
        Bs * (Real.log n * (optimalLocalBandwidth p n) ^ p) by ring, mul_pow, hLb]
    rw [hfirst]
    dsimp only [P]
    calc
      _ ≤ 2 ^ (2 * k - 1) *
          (Bs ^ (2 * k) * z ^ (2 * k) + z ^ (2 * k)) := by gcongr
      _ = _ := by ring
  have hpilotBias :
      (Bp * (optimalLocalBandwidth p n) ^ p +
        gridCovarianceError (1 / 2) Ep n) ^ (2 * k) ≤
      P * (Bp ^ (2 * k) + 1) * z ^ (2 * k) := by
    have hsum := add_pow_le
      (show 0 ≤ Bp * (optimalLocalBandwidth p n) ^ p by
        exact mul_nonneg hBp (Real.rpow_nonneg hδ.le _))
      hEp0 (2 * k)
    apply hsum.trans
    rw [mul_pow]
    dsimp only [P]
    calc
      _ ≤ 2 ^ (2 * k - 1) *
          (Bp ^ (2 * k) * z ^ (2 * k) + z ^ (2 * k)) := by
            gcongr
      _ = _ := by ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hscaleCenter : Cs * Real.log n ^ (2 * k) / (n : ℝ) ^ k ≤
      Cs * z ^ (2 * k) := by
    have hnrate : 1 / (n : ℝ) ^ k ≤ lowerBoundRate p n ^ (2 * k) := by
      rw [one_div, ← inv_pow, ← one_div, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hrate k
    rw [div_eq_mul_inv, ← one_div, mul_assoc]
    dsimp only [z]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hnrate (pow_nonneg (by linarith) _)) hCs.le
  have hlocalVar : Cl / ((n : ℝ) * optimalLocalBandwidth p n) ^ k =
      Cl * z ^ (2 * k) := by rw [div_eq_mul_inv, ← one_div, hloc]
  have hpilotVar : Cp / ((n : ℝ) * optimalLocalBandwidth p n) ^ k =
      Cp * z ^ (2 * k) := by rw [div_eq_mul_inv, ← one_div, hloc]
  have hlocalBlock :
      P * (Cl / ((n : ℝ) * optimalLocalBandwidth p n) ^ k +
        (2 * Real.log n * (Cb * (optimalLocalBandwidth p n) ^ p) +
          D * gridCovarianceError (1 / 2) El n) ^ (2 * k)) ≤
      P * (Cl + P * ((2 * Cb) ^ (2 * k) + D ^ (2 * k))) * z ^ (2 * k) := by
    rw [hlocalVar]
    calc
      _ ≤ P * (Cl * z ^ (2 * k) +
          P * ((2 * Cb) ^ (2 * k) + D ^ (2 * k)) * z ^ (2 * k)) := by gcongr
      _ = _ := by ring
  have hlinearBlock :
      P * (Cs * Real.log n ^ (2 * k) / (n : ℝ) ^ k +
        (Bs * Real.log n * (optimalLocalBandwidth p n) ^ p +
          Real.log n * gridCovarianceError (1 / 2) Es n) ^ (2 * k)) ≤
      P * (Cs + P * (Bs ^ (2 * k) + 1)) * z ^ (2 * k) := by
    calc
      _ ≤ P * (Cs * z ^ (2 * k) + P * (Bs ^ (2 * k) + 1) * z ^ (2 * k)) := by
        gcongr
      _ = _ := by ring
  have hpilotBlock :
      L ^ (2 * k) * P *
        (Cp / ((n : ℝ) * optimalLocalBandwidth p n) ^ k +
          (Bp * (optimalLocalBandwidth p n) ^ p +
            gridCovarianceError (1 / 2) Ep n) ^ (2 * k)) ≤
      L ^ (2 * k) * P * (Cp + P * (Bp ^ (2 * k) + 1)) * z ^ (2 * k) := by
    rw [hpilotVar]
    calc
      _ ≤ L ^ (2 * k) * P *
          (Cp * z ^ (2 * k) + P * (Bp ^ (2 * k) + 1) * z ^ (2 * k)) := by
            gcongr
      _ = _ := by ring
  apply hbase.trans
  calc
    _ ≤ A * z ^ (2 * k) := by
      dsimp only [A]
      calc
        _ ≤ P *
            (P * (Cl + P * ((2 * Cb) ^ (2 * k) + D ^ (2 * k))) * z ^ (2 * k) +
             P * (P * (Cs + P * (Bs ^ (2 * k) + 1)) * z ^ (2 * k) +
               L ^ (2 * k) * P * (Cp + P * (Bp ^ (2 * k) + 1)) * z ^ (2 * k))) := by
                 gcongr
        _ = _ := by ring
    _ ≤ C ^ (2 * k) * z ^ (2 * k) := by
      exact mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_right zero_le_one).trans
          (le_self_pow₀ (show 1 ≤ C by dsimp only [C]; linarith)
            (Nat.mul_ne_zero (show 2 ≠ 0 by norm_num) (show k ≠ 0 by omega))))
        (pow_nonneg hz0 _)
    _ = (C * Real.log n * lowerBoundRate p n) ^ (2 * k) := by
      dsimp only [z]
      rw [mul_pow, mul_pow]
      ring

end Hurst
