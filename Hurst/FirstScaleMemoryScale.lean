import Hurst.FirstScaleLongRates
import Hurst.ScaleBandwidth
import Hurst.ActualMemoryBranches

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

set_option maxHeartbeats 1500000

/-- The actual q=1 scale estimator, averaged at an independent pilot bandwidth,
is negligible after one logarithmic normalization throughout `b < 1`. -/
theorem hurstHolder_q1_scale_mesh_L1_negligible
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b)) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) *
        (∫ x, |q1LogScaleEstimator r n (scaleAverageResolution p n)
          (optimalLocalBandwidth p n) x|
          ∂featureGaussian
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))
      atTop (𝓝 0) := by
  obtain ⟨N₀, hN₀, A₁, hA₁, C₁, hC₁, D₁, hD₁,
      A₂, hA₂, C₂, hC₂, D₂, hD₂, E, hE, N, hN, hL1⟩ :=
    hurstHolder_q1_logScale_L1_lt_one p a b M r hp ha hb hab hM
  let L := fun n : ℕ => 1 + Real.log (2 * (n : ℝ))
  let R := fun n : ℕ =>
    D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
    D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n
  let K : ℝ := 4 + 4 / (Real.log 2) ^ 2
  have hrow1 :=
    (firstStrideLongRowBound_mesh_log_four_div_tendsto
      b C₁ A₁ 1 hb (by norm_num)).const_mul D₁
  have hrow2 :=
    (firstStrideLongRowBound_mesh_log_four_div_tendsto
      b C₂ A₂ 2 hb (by norm_num)).const_mul D₂
  have hrow : Tendsto (fun n : ℕ => L n ^ 4 * R n) atTop (𝓝 0) := by
    have h := hrow1.add hrow2
    have h' : Tendsto (fun x : ℕ =>
        D₁ * ((1 + Real.log (2 * (x : ℝ))) ^ 4 *
          (firstStrideLongRowBound b C₁ A₁ 1 x / (x : ℝ))) +
        D₂ * ((1 + Real.log (2 * (x : ℝ))) ^ 4 *
          (firstStrideLongRowBound b C₂ A₂ 2 x / (x : ℝ))))
        atTop (𝓝 0) := by simpa using h
    apply h'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    dsimp [L, R]
    field_simp
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have htop : Tendsto (fun n : ℕ => Real.sqrt (K * (L n ^ 4 * R n)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using (hrow.const_mul K).sqrt
  have hstoch : Tendsto (fun n : ℕ =>
      L n * Real.sqrt (K * (Real.log n) ^ 2 * R n)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ htop
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hLn : 0 ≤ L n := by
        dsimp [L]
        have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith)
        linarith
      exact mul_nonneg hLn (Real.sqrt_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hLn : 0 ≤ L n := by
        dsimp [L]
        have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith)
        linarith
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hlogL : Real.log (n : ℝ) ≤ L n := by
        dsimp [L]
        have h2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
        linarith
      have hR0 : 0 ≤ R n := by
        dsimp [R, firstStrideLongRowBound, gridCovarianceError]
        positivity
      have hins : L n ^ 2 * (K * (Real.log n) ^ 2 * R n) ≤
          K * (L n ^ 4 * R n) := by
        have hsq := pow_le_pow_left₀ hlog0 hlogL 2
        have hLR := mul_le_mul_of_nonneg_left hsq (sq_nonneg (L n))
        have hKR := mul_le_mul_of_nonneg_left hLR (mul_nonneg hK hR0)
        calc
          _ = (K * R n) * (L n ^ 2 * (Real.log n) ^ 2) := by ring
          _ ≤ (K * R n) * (L n ^ 2 * L n ^ 2) := hKR
          _ = _ := by ring
      have hs := Real.sqrt_le_sqrt hins
      have heq : L n * Real.sqrt (K * (Real.log n) ^ 2 * R n) =
          Real.sqrt (L n ^ 2 * (K * (Real.log n) ^ 2 * R n)) := by
        rw [Real.sqrt_mul (sq_nonneg (L n)), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hLn]
      rwa [heq]
  have hgrid := gridCovarianceError_mesh_log_sq_tendsto b E hb
  have hupper := hstoch.add hgrid
  simp only [add_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hLn : 0 ≤ L n := by
      dsimp [L]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      linarith
    exact mul_nonneg hLn (integral_nonneg (fun _ => abs_nonneg _))
  · filter_upwards [optimalLocalBandwidth_eventual_design p N₀ hp,
      eventually_ge_atTop N] with n hdesign hnN
    obtain ⟨hn1, hδ, hδhalf, hnd, hrate, hlog⟩ := hdesign
    obtain ⟨hm, hmd⟩ := scaleAverageResolution_design p n hδ
    have hfinite := hL1 n hnN hlog f hf hF _ hm _ hδ hδhalf hnd hmd
    have hLn : 0 ≤ L n := by
      dsimp [L]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1.le
        linarith)
      linarith
    have hlogL : Real.log (n : ℝ) ≤ L n := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn1)
      dsimp [L]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
      have := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      linarith
    have hm := mul_le_mul_of_nonneg_left hfinite.2 hLn
    apply hm.trans
    have he0 : 0 ≤ gridCovarianceError b E n := by
      unfold gridCovarianceError
      positivity
    have hbias := mul_le_mul_of_nonneg_right hlogL (mul_nonneg hLn he0)
    change L n *
        (Real.sqrt (K * (Real.log n) ^ 2 * R n) +
          Real.log n * gridCovarianceError b E n) ≤
      L n * Real.sqrt (K * (Real.log n) ^ 2 * R n) +
        L n ^ 2 * gridCovarianceError b E n
    calc
      _ = L n * Real.sqrt (K * (Real.log n) ^ 2 * R n) +
          Real.log n * (L n * gridCovarianceError b E n) := by ring
      _ ≤ L n * Real.sqrt (K * (Real.log n) ^ 2 * R n) +
          L n * (L n * gridCovarianceError b E n) := add_le_add le_rfl hbias
      _ = _ := by ring

def logSquaredMemoryBandwidth (n : ℕ) : ℝ := (Real.log n) ^ 2 / (n : ℝ)

theorem firstCriticalNormalization_logSquared_le_mesh :
    ∀ᶠ n : ℕ in atTop,
      firstCriticalNormalization n (logSquaredMemoryBandwidth n) ≤
        1 + Real.log (2 * (n : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => (Real.log n) ^ 2) atTop atTop :=
    tendsto_atTop_mono' atTop (by
      filter_upwards [hlog.eventually_ge_atTop 1] with n hn
      nlinarith [sq_nonneg (Real.log n)]) hlog
  have hloglog := Real.tendsto_log_atTop.comp hsq
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop 1,
      hloglog.eventually_ge_atTop 1] with n hn hln hll
  change 1 ≤ Real.log ((Real.log n) ^ 2) at hll
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : Real.log (n : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
    have := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    linarith
  have heff : (n : ℝ) * logSquaredMemoryBandwidth n = (Real.log n) ^ 2 := by
    unfold logSquaredMemoryBandwidth
    field_simp
  unfold firstCriticalNormalization
  rw [heff]
  have hden : 0 < Real.log ((Real.log n) ^ 2) := zero_lt_one.trans_le hll
  have hdiv : (Real.log n) ^ 2 / Real.log ((Real.log n) ^ 2) ≤
      (Real.log n) ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    calc
      (Real.log n) ^ 2 = (Real.log n) ^ 2 * 1 := by ring
      _ ≤ (Real.log n) ^ 2 * Real.log ((Real.log n) ^ 2) :=
        mul_le_mul_of_nonneg_left hll (sq_nonneg _)
  calc
    _ ≤ Real.sqrt ((Real.log n) ^ 2) := Real.sqrt_le_sqrt hdiv
    _ = Real.log n := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
    _ ≤ _ := hL

theorem firstLongNormalization_logSquared_le_mesh (h : ℝ)
    (hlong : 3 / 4 < h) (hh : h < 1) :
    ∀ᶠ n : ℕ in atTop,
      firstLongNormalization h n (logSquaredMemoryBandwidth n) ≤
        1 + Real.log (2 * (n : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop 1] with n hn hln
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : Real.log (n : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
    have := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    linarith
  have heff : (n : ℝ) * logSquaredMemoryBandwidth n = (Real.log n) ^ 2 := by
    unfold logSquaredMemoryBandwidth
    field_simp
  unfold firstLongNormalization
  rw [heff]
  have hbase : (1 : ℝ) ≤ (Real.log n) ^ 2 := by nlinarith
  have hexp : 2 - 2 * h ≤ (1 / 2 : ℝ) := by linarith
  calc
    ((Real.log n) ^ 2) ^ (2 - 2 * h) ≤
        ((Real.log n) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    _ = Real.log n := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by linarith)]
    _ ≤ _ := hL

theorem scale_L1_negligible_of_normalization_le_mesh
    (I A : ℕ → ℝ) (hI : ∀ n, 0 ≤ I n)
    (hA : ∀ᶠ n in atTop, 0 ≤ A n)
    (hAle : ∀ᶠ n in atTop, A n ≤ 1 + Real.log (2 * (n : ℝ)))
    (hmesh : Tendsto (fun n : ℕ =>
      (1 + Real.log (2 * (n : ℝ))) * I n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => A n * I n) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hmesh
  · filter_upwards [hA] with n hn
    exact mul_nonneg hn (hI n)
  · filter_upwards [hAle] with n hn
    exact mul_le_mul_of_nonneg_right hn (hI n)

theorem hurstHolder_q1_critical_scale_L1_negligible
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b)) :
    Tendsto (fun n : ℕ =>
      firstCriticalNormalization n (logSquaredMemoryBandwidth n) *
        (∫ x, |q1LogScaleEstimator r n (scaleAverageResolution p n)
          (optimalLocalBandwidth p n) x|
          ∂featureGaussian
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))
      atTop (𝓝 0) := by
  apply scale_L1_negligible_of_normalization_le_mesh
    (fun n => ∫ x, |q1LogScaleEstimator r n (scaleAverageResolution p n)
      (optimalLocalBandwidth p n) x|
      ∂featureGaussian
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
    (fun n => firstCriticalNormalization n (logSquaredMemoryBandwidth n))
    (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _))
    firstCriticalNormalization_logSquared_le_mesh
  exact hurstHolder_q1_scale_mesh_L1_negligible
    p a b M r hp ha hb hab hM f hf hF

theorem hurstHolder_q1_long_scale_L1_negligible
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t) :
    Tendsto (fun n : ℕ =>
      firstLongNormalization (f t) n (logSquaredMemoryBandwidth n) *
        (∫ x, |q1LogScaleEstimator r n (scaleAverageResolution p n)
          (optimalLocalBandwidth p n) x|
          ∂featureGaussian
            (gridObservationFeatures n (midpointSampleHurst f hf.1 n))))
      atTop (𝓝 0) := by
  have hft : f t < 1 := (hF ht).2.trans_lt hb
  apply scale_L1_negligible_of_normalization_le_mesh
    (fun n => ∫ x, |q1LogScaleEstimator r n (scaleAverageResolution p n)
      (optimalLocalBandwidth p n) x|
      ∂featureGaussian
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n)))
    (fun n => firstLongNormalization (f t) n (logSquaredMemoryBandwidth n))
    (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (Filter.Eventually.of_forall (fun n => Real.rpow_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (by
        unfold logSquaredMemoryBandwidth
        positivity)) _))
    (firstLongNormalization_logSquared_le_mesh (f t) hlong hft)
  exact hurstHolder_q1_scale_mesh_L1_negligible
    p a b M r hp ha hb hab hM f hf hF

end Hurst
