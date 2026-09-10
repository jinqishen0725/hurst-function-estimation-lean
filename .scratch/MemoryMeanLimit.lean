import Hurst.FirstScaleMemoryScale
import Hurst.ActualMeanResidual
import Hurst.LocalBias
import Hurst.CorrelationLimit
import Hurst.EventualWeightMass

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem logSquaredMemoryBandwidth_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 < logSquaredMemoryBandwidth n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  unfold logSquaredMemoryBandwidth
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  positivity

theorem logSquaredMemoryBandwidth_tendsto_zero :
    Tendsto logSquaredMemoryBandwidth atTop (nhds 0) := by
  have h := nat_log_power_div_rpow_tendsto 1 (by norm_num) 2
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold logSquaredMemoryBandwidth
  rw [Real.rpow_one]

theorem logSquaredMemoryBandwidth_effective_sample_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) * logSquaredMemoryBandwidth n)
      atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => (Real.log n) ^ 2) atTop atTop :=
    tendsto_atTop_mono' atTop (by
      filter_upwards [hlog.eventually_ge_atTop 1] with n hn
      nlinarith [sq_nonneg (Real.log n)]) hlog
  apply hsq.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold logSquaredMemoryBandwidth
  field_simp

theorem mesh_log_four_mul_logSquaredBandwidth_tendsto :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) ^ 2 *
        Real.log n * logSquaredMemoryBandwidth n) atTop (nhds 0) := by
  have h := mesh_log_power_rpow_tendsto (-1) (by norm_num) 5
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_ge_atTop 1] with n hn
    unfold logSquaredMemoryBandwidth
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hL0 : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      linarith
    have hlogL : Real.log (n : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
      have h2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      linarith
    unfold logSquaredMemoryBandwidth
    rw [show (n : ℝ) ^ (-1 : ℝ) = 1 / n by
      rw [Real.rpow_neg_one, one_div]]
    have hpow := pow_le_pow_left₀ hlog0 hlogL 3
    calc
      (1 + Real.log (2 * (n : ℝ))) ^ 2 * Real.log n *
          ((Real.log n) ^ 2 / n) =
        (1 + Real.log (2 * (n : ℝ))) ^ 2 *
          (Real.log n) ^ 3 / n := by ring
      _ ≤ (1 + Real.log (2 * (n : ℝ))) ^ 5 / n := by
        rw [div_le_div_iff_of_pos_right hnR]
        nlinarith [mul_le_mul_of_nonneg_left hpow (sq_nonneg (1 + Real.log (2 * (n : ℝ))))]
      _ = (1 + Real.log (2 * (n : ℝ))) ^ 5 * (1 / n) := by ring

/-- With the explicit memory bandwidth, any nonnegative normalization bounded
by the mesh logarithm kills the deterministic q=1 local-log mean error. -/
theorem hurstHolder_q1_logSquared_mean_of_normalization_le_mesh
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (A : ℕ → ℝ) (hA0 : ∀ᶠ n in atTop, 0 ≤ A n)
    (hAle : ∀ᶠ n in atTop,
      A n ≤ 1 + Real.log (2 * (n : ℝ))) :
    Tendsto (fun n : ℕ => A n *
      ((∫ x, gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1
            (logSquaredMemoryBandwidth n) t)
          (gridDifferenceCoefficients n) x
        ∂featureGaussian (gridObservationFeatures n
          (midpointSampleHurst f hf.1 n))) -
        calibrationOne (Real.log n) gaussianLogSquareMean (f t)))
      atTop (nhds 0) := by
  let L : ℕ → ℝ := fun n => 1 + Real.log (2 * (n : ℝ))
  obtain ⟨N₀, hN₀, C, hC, hres⟩ :=
    hurstHolder_stride_first_log_expectation_residual
      p a b M (Nat.ceil p - 1) 1 hp ha hb hab hM (by norm_num)
  obtain ⟨Nb, hNb, Cb, hCb, hbias⟩ :=
    hurstHolder_localPolynomial_bias p hp 1
  obtain ⟨g, hg, heq, hgmap, hgbias⟩ := hbias M hM f hf
  have hgrid := (gridCovarianceError_mesh_log_sq_tendsto b 1 hb).const_mul C
  have hbw := mesh_log_four_mul_logSquaredBandwidth_tendsto.const_mul
    (2 * Cb * (1 + M))
  have he : Tendsto (fun n : ℕ =>
      C * (L n ^ 2 * gridCovarianceError b 1 n) +
        (2 * Cb * (1 + M)) *
          (L n ^ 2 * Real.log n * logSquaredMemoryBandwidth n))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, L] using hgrid.add hbw
  apply tendsto_of_abs_sub_le_zero _ (fun _ => 0) _ 0 tendsto_const_nhds he
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hL0 : 0 ≤ L n := by
      dsimp only [L]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      linarith
    have herr0 : 0 ≤ gridCovarianceError b 1 n := by
      unfold gridCovarianceError
      positivity
    have hMp : 0 ≤ 1 + M := by linarith
    have hlog0 : 0 ≤ Real.log (n : ℝ) := by
      by_cases hn : n = 0
      · simp [hn]
      · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))
    have hδ0 : 0 ≤ logSquaredMemoryBandwidth n := by
      unfold logSquaredMemoryBandwidth
      positivity
    exact add_nonneg
      (mul_nonneg hC (mul_nonneg (sq_nonneg _) herr0))
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCb.le) hMp)
        (mul_nonneg (mul_nonneg (sq_nonneg _) hlog0) hδ0))
  · have hmass := localPolynomialWeights_eventual_mass
      (Nat.ceil p - 1) 1 logSquaredMemoryBandwidth
      logSquaredMemoryBandwidth_eventually_pos
      logSquaredMemoryBandwidth_tendsto_zero
      logSquaredMemoryBandwidth_effective_sample_tendsto
    filter_upwards [hA0, hAle, hres, hmass,
      logSquaredMemoryBandwidth_eventually_pos,
      logSquaredMemoryBandwidth_tendsto_zero.eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      logSquaredMemoryBandwidth_effective_sample_tendsto.eventually_ge_atTop
        (max N₀ Nb), eventually_ge_atTop 2] with
      n hAn hAL hnres hnmass hδ hδhalf hN hn2
    have hn0 : 0 < n := by omega
    have hnN₀ : N₀ ≤ (n : ℝ) * logSquaredMemoryBandwidth n :=
      (le_max_left _ _).trans hN
    have hnNb : Nb ≤ (n : ℝ) * logSquaredMemoryBandwidth n :=
      (le_max_right _ _).trans hN
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ n by omega))
    have hL0 : 0 ≤ L n := by
      dsimp only [L]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        linarith)
      linarith
    have hL1 : 1 ≤ L n := by
      dsimp only [L]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        linarith)
      linarith
    have hlogL : Real.log (n : ℝ) ≤ L n := by
      dsimp only [L]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
      have := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      linarith
    let w := localPolynomialWeights (Nat.ceil p - 1) n 1
      (logSquaredMemoryBandwidth n) t
    have hresn := hnres f hf hF (logSquaredMemoryBandwidth n) t hδ
      hδhalf.le ⟨ht.1.le, ht.2.le⟩ hnN₀
    have hbiasn : |smooth w (fun i => f (grid n i.val)) - f t| ≤
        Cb * (1 + M) * (logSquaredMemoryBandwidth n) ^ p := by
      simpa only [w, heq ht] using hgbias n hn0 (by omega)
        (logSquaredMemoryBandwidth n) hδ hδhalf.le hnNb t ⟨ht.1.le, ht.2.le⟩
    have hpδ : (logSquaredMemoryBandwidth n) ^ p ≤ logSquaredMemoryBandwidth n := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ
        (hδhalf.le.trans (by norm_num)) hp
    have hbias1 : |smooth w (fun i => f (grid n i.val)) - f t| ≤
        Cb * (1 + M) * logSquaredMemoryBandwidth n :=
      hbiasn.trans (mul_le_mul_of_nonneg_left hpδ (by positivity))
    have hsum : ∑ i, w i = 1 := by
      simpa only [w] using hnmass t ⟨ht.1.le, ht.2.le⟩
    have hcal : |smooth w (fun i =>
        -2 * Real.log n * f (grid n i.val) + gaussianLogSquareMean) -
        (-2 * Real.log n * f t + gaussianLogSquareMean)| ≤
        2 * Real.log n * (Cb * (1 + M) * logSquaredMemoryBandwidth n) := by
      have hdecomp := log_estimator_decomposition w
        (fun i => f (grid n i.val)) (fun _ => 0)
        (Real.log n) gaussianLogSquareMean hsum
      simp only [add_zero] at hdecomp
      have hz : smooth w (fun _ => (0 : ℝ)) = 0 := by simp [smooth]
      rw [hz, add_zero] at hdecomp
      rw [hdecomp]
      calc
        |(-2 * Real.log n * smooth w (fun i => f (grid n i.val)) +
              gaussianLogSquareMean) -
            (-2 * Real.log n * f t + gaussianLogSquareMean)| =
            2 * Real.log n *
              |smooth w (fun i => f (grid n i.val)) - f t| := by
              rw [show (-2 * Real.log n * smooth w (fun i => f (grid n i.val)) +
                    gaussianLogSquareMean) -
                  (-2 * Real.log n * f t + gaussianLogSquareMean) =
                  (-2 * Real.log n) *
                    (smooth w (fun i => f (grid n i.val)) - f t) by ring]
              rw [abs_mul, abs_of_nonpos (by nlinarith : -2 * Real.log n ≤ 0)]
              ring
        _ ≤ 2 * Real.log n *
            (Cb * (1 + M) * logSquaredMemoryBandwidth n) :=
          mul_le_mul_of_nonneg_left hbias1 (by positivity)
    have htot : |(∫ x, gaussianLogStatistic w (gridDifferenceCoefficients n) x
          ∂featureGaussian (gridObservationFeatures n
            (midpointSampleHurst f hf.1 n))) -
        calibrationOne (Real.log n) gaussianLogSquareMean (f t)| ≤
        C * gridCovarianceError b 1 n +
          2 * Real.log n * (Cb * (1 + M) * logSquaredMemoryBandwidth n) := by
      have htri := abs_sub_le
        (strideFirstGridLogExpectation (Nat.ceil p - 1) n 1
          (logSquaredMemoryBandwidth n) t (midpointSampleHurst f hf.1 n))
        (smooth w (fun i => -2 * Real.log n * f (grid n i.val) +
          gaussianLogSquareMean))
        (calibrationOne (Real.log n) gaussianLogSquareMean (f t))
      apply htri.trans
      apply add_le_add
      · norm_num at hresn
        have hfun : (fun i : Fin (n - 1) =>
            -(2 * Real.log n * f (grid n i.val)) + gaussianLogSquareMean) =
            (fun i => -2 * Real.log n * f (grid n i.val) +
              gaussianLogSquareMean) := by
          funext i
          ring
        rw [hfun] at hresn
        simpa only [w] using hresn
      · unfold calibrationOne
        rw [show gaussianLogSquareMean - 2 * Real.log n * f t =
          -2 * Real.log n * f t + gaussianLogSquareMean by ring]
        exact hcal
    rw [sub_zero, abs_mul, abs_of_nonneg hAn]
    apply (mul_le_mul_of_nonneg_left htot hAn).trans
    dsimp only [L] at hAL hL0 hL1 hlogL ⊢
    have herr0 : 0 ≤ gridCovarianceError b 1 n := by
      unfold gridCovarianceError
      positivity
    have hδ0 : 0 ≤ logSquaredMemoryBandwidth n := hδ.le
    have hAL2 : A n ≤ L n ^ 2 := by
      exact hAL.trans (by nlinarith)
    calc
      A n * (C * gridCovarianceError b 1 n +
          2 * Real.log n * (Cb * (1 + M) * logSquaredMemoryBandwidth n)) ≤
          L n ^ 2 * (C * gridCovarianceError b 1 n +
          2 * Real.log n * (Cb * (1 + M) * logSquaredMemoryBandwidth n)) :=
        mul_le_mul_of_nonneg_right hAL2 (by positivity)
      _ = C * (L n ^ 2 * gridCovarianceError b 1 n) +
          (2 * Cb * (1 + M)) *
            (L n ^ 2 * Real.log n * logSquaredMemoryBandwidth n) := by ring

end Hurst
