import Hurst.MemoryMeanLimit
import Hurst.WeightedRowEnergy

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem gaussianLogStatistic_variance_l1_bound
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) (L : ℝ) (hL : 0 ≤ L)
    (hw : ∑ i, |w i| ≤ L) :
    Var[gaussianLogStatistic w a; featureGaussian v] ≤
      4 * gaussianLogSquareVariance * L ^ 2 := by
  apply (gaussianLogStatistic_variance_correlation_bound v w a ha).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
  calc
    (∑ i, ∑ j, |w i| * |w j| *
        featureCorrelation v (a i) (a j) ^ 2) ≤
        ∑ i, ∑ j, |w i| * |w j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hc := featureCorrelation_abs_le_one v (a i) (a j) (ha i) (ha j)
      have hs := pow_le_pow_left₀ (abs_nonneg _) hc 2
      have hs' : featureCorrelation v (a i) (a j) ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using hs
      calc
        _ ≤ |w i| * |w j| * 1 :=
          mul_le_mul_of_nonneg_left hs'
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = _ := by ring
    _ = (∑ i, |w i|) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      congr 1
      funext i
      rw [Finset.mul_sum]
    _ ≤ L ^ 2 := pow_le_pow_left₀
      (Finset.sum_nonneg fun _ _ => abs_nonneg _) hw 2

theorem hurstHolder_q1_logSquared_variance_uniform
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ V ≥ 0, ∀ᶠ n : ℕ in atTop,
      Var[gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1
            (logSquaredMemoryBandwidth n) t)
          (gridDifferenceCoefficients n);
        featureGaussian (gridObservationFeatures n
          (midpointSampleHurst f hf.1 n))] ≤ V := by
  obtain ⟨N₀, hN₀, D, hD, hw⟩ :=
    localPolynomialWeights_uniform_stability (Nat.ceil p - 1) 1
  obtain ⟨C, hC, hmean⟩ :=
    hurstHolder_stride_first_log_mean p a b M hp ha hb hab hM 1 (by norm_num)
  refine ⟨4 * gaussianLogSquareVariance * D ^ 2,
    mul_nonneg (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
      (sq_nonneg D), ?_⟩
  filter_upwards [hmean, logSquaredMemoryBandwidth_eventually_pos,
      logSquaredMemoryBandwidth_tendsto_zero.eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      logSquaredMemoryBandwidth_effective_sample_tendsto.eventually_ge_atTop N₀,
      eventually_ge_atTop 2] with n hnmean hδ hδhalf hN hn2
  let H := midpointSampleHurst f hf.1 n
  have hn0 : 0 < n := by omega
  have hfeat : ∀ i, ∑ j, gridDifferenceCoefficients n i j •
      gridObservationFeatures n H j ≠ 0 := by
    intro i
    change ∑ j, gridStrideFirstCoefficients n 1 i j •
      gridObservationFeatures n H j ≠ 0
    exact (hnmean f hf hF i).1
  obtain ⟨_, _, hl1, _⟩ := hw n hn0 (by omega)
    (logSquaredMemoryBandwidth n) t hδ hδhalf.le
    ⟨ht.1.le, ht.2.le⟩ hN
  exact gaussianLogStatistic_variance_l1_bound
    (gridObservationFeatures n H)
    (localPolynomialWeights (Nat.ceil p - 1) n 1
      (logSquaredMemoryBandwidth n) t)
    (gridDifferenceCoefficients n) hfeat D hD.le hl1

theorem hurstHolder_q1_logSquared_mean_tendsto_zero
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ =>
      (∫ x, gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1
            (logSquaredMemoryBandwidth n) t)
          (gridDifferenceCoefficients n) x
        ∂featureGaussian (gridObservationFeatures n
          (midpointSampleHurst f hf.1 n))) -
        calibrationOne (Real.log n) gaussianLogSquareMean (f t))
      atTop (nhds 0) := by
  simpa only [one_mul] using
    (hurstHolder_q1_logSquared_mean_of_normalization_le_mesh
      p a b M hp ha hb hab hM f hf hF t ht (fun _ => 1)
      (Filter.Eventually.of_forall (fun _ => by norm_num)) (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith)
        linarith))

theorem firstCriticalNormalization_logSquared_div_log_tendsto_zero :
    Tendsto (fun n : ℕ =>
      firstCriticalNormalization n (logSquaredMemoryBandwidth n) /
        Real.log n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => (Real.log n) ^ 2) atTop atTop :=
    tendsto_atTop_mono' atTop (by
      filter_upwards [hlog.eventually_ge_atTop 1] with n hn
      nlinarith [sq_nonneg (Real.log n)]) hlog
  have hll : Tendsto (fun n : ℕ => Real.log ((Real.log n) ^ 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hsq
  have hzero := (Real.tendsto_sqrt_atTop.comp hll).inv_tendsto_atTop
  apply hzero.congr'
  filter_upwards [eventually_ge_atTop 2, hll.eventually_ge_atTop 1] with n hn hll1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have heff : (n : ℝ) * logSquaredMemoryBandwidth n = (Real.log n) ^ 2 := by
    unfold logSquaredMemoryBandwidth
    field_simp
  unfold firstCriticalNormalization
  rw [heff]
  have hllpos : 0 < Real.log ((Real.log n) ^ 2) := zero_lt_one.trans_le hll1
  change (Real.sqrt (Real.log ((Real.log n) ^ 2)))⁻¹ = _
  rw [inv_eq_one_div]
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos hlogpos]
  field_simp

theorem firstLongNormalization_logSquared_div_log_tendsto_zero
    (h : ℝ) (hlong : 3 / 4 < h) :
    Tendsto (fun n : ℕ =>
      firstLongNormalization h n (logSquaredMemoryBandwidth n) /
        Real.log n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : 0 < 4 * h - 3 := by linarith
  have hz := (tendsto_rpow_neg_atTop hp).comp hlog
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have heff : (n : ℝ) * logSquaredMemoryBandwidth n = (Real.log n) ^ 2 := by
    unfold logSquaredMemoryBandwidth
    field_simp
  unfold firstLongNormalization
  rw [heff, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hlogpos.le, div_eq_mul_inv,
    ← Real.rpow_neg_one, ← Real.rpow_add hlogpos]
  change (Real.log n) ^ (-(4 * h - 3)) =
    (Real.log n) ^ ((2 : ℝ) * (2 - 2 * h) + -1)
  rw [show (2 : ℝ) * (2 - 2 * h) + -1 = -(4 * h - 3) by ring]

theorem scaled_mse_div_log_tendsto_zero_of_uniform
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → ℝ) (c A : ℕ → ℝ)
    (hX : ∀ᶠ n in atTop, MemLp (X n) 2 (P n))
    (hvar : ∃ V ≥ 0, ∀ᶠ n in atTop, Var[X n; P n] ≤ V)
    (hmean : Tendsto (fun n => (∫ x, X n x ∂P n) - c n) atTop (nhds 0))
    (hscale0 : ∀ᶠ n in atTop, 0 ≤ A n / Real.log n)
    (hscale : Tendsto (fun n => A n / Real.log n) atTop (nhds 0)) :
    Tendsto (fun n => A n * (∫ x, (X n x - c n) ^ 2 ∂P n) /
      Real.log n) atTop (nhds 0) := by
  obtain ⟨V, hV, hv⟩ := hvar
  have hm1 : ∀ᶠ n in atTop, |(∫ x, X n x ∂P n) - c n| ≤ 1 :=
    hmean.abs.eventually_le_const (by norm_num)
  have hupp := hscale.const_mul (V + 1)
  simp only [mul_zero] at hupp
  apply squeeze_zero' _ _ hupp
  · filter_upwards [hscale0] with n hn
    rw [show A n * (∫ x, (X n x - c n) ^ 2 ∂P n) /
      Real.log n = (A n / Real.log n) *
        (∫ x, (X n x - c n) ^ 2 ∂P n) by ring]
    exact mul_nonneg hn (integral_nonneg fun _ => sq_nonneg _)
  · filter_upwards [hX, hv, hm1, hscale0] with n hXn hvn hmn hsn
    have hm2 : ((∫ x, X n x ∂P n) - c n) ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hmn 2
      simpa only [sq_abs, one_pow] using this
    have hMSE : (∫ x, (X n x - c n) ^ 2 ∂P n) ≤ V + 1 := by
      rw [mse_decomposition (X n) (c n) hXn]
      linarith
    rw [show A n * (∫ x, (X n x - c n) ^ 2 ∂P n) /
      Real.log n = (A n / Real.log n) *
        (∫ x, (X n x - c n) ^ 2 ∂P n) by ring]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hMSE hsn

theorem hurstHolder_q1_logSquared_memLp_two
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, MemLp
      (gaussianLogStatistic
        (localPolynomialWeights (Nat.ceil p - 1) n 1
          (logSquaredMemoryBandwidth n) t)
        (gridDifferenceCoefficients n)) 2
      (featureGaussian (gridObservationFeatures n
        (midpointSampleHurst f hf.1 n))) := by
  obtain ⟨C, hC, hmean⟩ :=
    hurstHolder_stride_first_log_mean p a b M hp ha hb hab hM 1 (by norm_num)
  filter_upwards [hmean] with n hn
  apply gaussianLogStatistic_memLp_two
  intro i
  change ∑ j, gridStrideFirstCoefficients n 1 i j •
    gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0
  exact (hn f hf hF i).1

theorem hurstHolder_q1_critical_logSquared_secondMoment_tendsto
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ =>
      firstCriticalNormalization n (logSquaredMemoryBandwidth n) *
        (∫ x, (gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1
            (logSquaredMemoryBandwidth n) t)
          (gridDifferenceCoefficients n) x -
            calibrationOne (Real.log n) gaussianLogSquareMean (f t)) ^ 2
          ∂featureGaussian (gridObservationFeatures n
            (midpointSampleHurst f hf.1 n))) / Real.log n)
      atTop (nhds 0) := by
  apply scaled_mse_div_log_tendsto_zero_of_uniform
    (fun n => featureGaussian (gridObservationFeatures n
      (midpointSampleHurst f hf.1 n)))
    (fun n => gaussianLogStatistic
      (localPolynomialWeights (Nat.ceil p - 1) n 1
        (logSquaredMemoryBandwidth n) t)
      (gridDifferenceCoefficients n))
    (fun n => calibrationOne (Real.log n) gaussianLogSquareMean (f t))
    (fun n => firstCriticalNormalization n (logSquaredMemoryBandwidth n))
  · exact hurstHolder_q1_logSquared_memLp_two
      p a b M hp ha hb hab hM f hf hF t
  · exact hurstHolder_q1_logSquared_variance_uniform
      p a b M hp ha hb hab hM f hf hF t ht
  · exact hurstHolder_q1_logSquared_mean_tendsto_zero
      p a b M hp ha hb hab hM f hf hF t ht
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (Real.sqrt_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · exact firstCriticalNormalization_logSquared_div_log_tendsto_zero

theorem hurstHolder_q1_long_logSquared_secondMoment_tendsto
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t) :
    Tendsto (fun n : ℕ =>
      firstLongNormalization (f t) n (logSquaredMemoryBandwidth n) *
        (∫ x, (gaussianLogStatistic
          (localPolynomialWeights (Nat.ceil p - 1) n 1
            (logSquaredMemoryBandwidth n) t)
          (gridDifferenceCoefficients n) x -
            calibrationOne (Real.log n) gaussianLogSquareMean (f t)) ^ 2
          ∂featureGaussian (gridObservationFeatures n
            (midpointSampleHurst f hf.1 n))) / Real.log n)
      atTop (nhds 0) := by
  apply scaled_mse_div_log_tendsto_zero_of_uniform
    (fun n => featureGaussian (gridObservationFeatures n
      (midpointSampleHurst f hf.1 n)))
    (fun n => gaussianLogStatistic
      (localPolynomialWeights (Nat.ceil p - 1) n 1
        (logSquaredMemoryBandwidth n) t)
      (gridDifferenceCoefficients n))
    (fun n => calibrationOne (Real.log n) gaussianLogSquareMean (f t))
    (fun n => firstLongNormalization (f t) n (logSquaredMemoryBandwidth n))
  · exact hurstHolder_q1_logSquared_memLp_two
      p a b M hp ha hb hab hM f hf hF t
  · exact hurstHolder_q1_logSquared_variance_uniform
      p a b M hp ha hb hab hM f hf hF t ht
  · exact hurstHolder_q1_logSquared_mean_tendsto_zero
      p a b M hp ha hb hab hM f hf hF t ht
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) (by
      unfold logSquaredMemoryBandwidth
      positivity)) _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · exact firstLongNormalization_logSquared_div_log_tendsto_zero (f t) hlong

end Hurst
