import Hurst.FirstStrideRows
import Hurst.FirstStrideActualRows
import Hurst.WeightedRowEnergy
import Hurst.ActualMemoryBranches

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem gridCovarianceError_fourth_row_tendsto (b C : ℝ) (hb : b < 7 / 8) :
    Tendsto (fun n : ℕ => (n : ℝ) * (gridCovarianceError b C n) ^ 4)
      atTop (𝓝 0) := by
  have h := (((mesh_log_rpow_tendsto (-3 / 4) (by norm_num)).add
    (mesh_log_rpow_tendsto (2 * b - 7 / 4) (by linarith))).const_mul C).pow 4
  simp only [add_zero, mul_zero, zero_pow (by norm_num : 4 ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : (n : ℝ) ^ (1 / 4 : ℝ) * gridCovarianceError b C n =
      C * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (-3 / 4 : ℝ) +
        (1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (2 * b - 7 / 4)) := by
    unfold gridCovarianceError
    have he1 : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-1 : ℝ) =
        (n : ℝ) ^ (-3 / 4 : ℝ) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have he2 : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (2 * b - 2) =
        (n : ℝ) ^ (2 * b - 7 / 4) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    calc
      _ = C * ((1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-1 : ℝ)) +
          (1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (2 * b - 2))) := by ring
      _ = _ := by rw [he1, he2]
  rw [← hs, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  norm_num

theorem strideFirstDecay_fourth_summable (b : ℝ) (hb : b < 7 / 8)
    (d : ℕ) (hd : 0 < d) :
    Summable (fun k => (strideFirstDecay b d k) ^ 4) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ (8 * b - 8)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs' := ((summable_nat_add_iff (d + 1)).mpr hs).div_const
    ((d : ℝ) ^ (8 * b - 8))
  apply (summable_nat_add_iff (2 * d + 1)).mp
  apply hs'.congr
  intro k
  have hk : ¬k + (2 * d + 1) ≤ 2 * d := by omega
  simp only [strideFirstDecay, hk, if_false,
    show k + (2 * d + 1) - d = k + (d + 1) by omega]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    Real.div_rpow (by positivity) (by positivity)]
  congr 2 <;> ring

theorem frozen_stride_first_grid_decay_lt_one
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (d : ℕ) (hd : 0 < d) :
    ∃ C ≥ 1, ∀ n m : ℕ, 0 < n → ∀ H : Fin m → Ioo (0 : ℝ) 1,
      (∀ i, (H i : ℝ) ∈ Icc a b) → ∀ i j : Fin m,
      |⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d : ℝ) / n),
        normalizedFrozenIncrement (H j) (grid n j.val) ((d : ℝ) / n)⟫| ≤
          C * strideFirstDecay b d (Nat.dist j.val i.val) := by
  obtain ⟨C, hC, hdec⟩ := normalizedFrozenIncrement_uniform_decay a b ha hb hab
  refine ⟨C + 1, by linarith, ?_⟩
  intro n m hn H hH
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hord : ∀ i j : Fin m, i.val ≤ j.val →
      |⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d : ℝ) / n),
        normalizedFrozenIncrement (H j) (grid n j.val) ((d : ℝ) / n)⟫| ≤
          (C + 1) * strideFirstDecay b d (Nat.dist j.val i.val) := by
    intro i j hij
    rw [Nat.dist_eq_sub_of_le_right hij]
    by_cases hnear : j.val - i.val ≤ 2 * d
    · have hcs := abs_real_inner_le_norm
        (normalizedFrozenIncrement (H i) (grid n i.val) ((d : ℝ) / n))
        (normalizedFrozenIncrement (H j) (grid n j.val) ((d : ℝ) / n))
      rw [normalizedFrozenIncrement_norm _ _ _ (by positivity),
        normalizedFrozenIncrement_norm _ _ _ (by positivity)] at hcs
      simp only [strideFirstDecay, hnear, if_true, mul_one]
      linarith
    · have hgap : i.val + d ≤ j.val := by omega
      have hg : (d : ℝ) ≤ (j.val - i.val - d : ℕ) := by
        exact_mod_cast (show d ≤ j.val - i.val - d by omega)
      have hrat : (1 : ℝ) ≤ (j.val - i.val - d : ℕ) / (d : ℝ) :=
        (le_div_iff₀ hdR).mpr (by simpa only [one_mul] using hg)
      have he := hdec (H i) (H j) (hH i) (hH j)
        (grid n i.val) (grid n j.val) ((d : ℝ) / n)
        ((j.val - i.val - d : ℕ) / (d : ℝ)) (by positivity) hrat
        (grid_stride_first_separated_gap n d i.val j.val hn hd hgap)
      simp only [strideFirstDecay, hnear, if_false]
      exact he.trans (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (by positivity) _))
  intro i j
  rcases le_total i.val j.val with hij | hji
  · exact hord i j hij
  · rw [real_inner_comm, Nat.dist_comm]
    exact hord j i hji

theorem stride_first_correlation_fourth_row_bound
    (b A e : ℝ) (d : ℕ) (hd : 0 < d) (hb : b < 7 / 8)
    (hA : 0 ≤ A) (he : 0 ≤ e) (n : ℕ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j,
      |r i j| ≤ A * strideFirstDecay b d (Nat.dist j.val i.val) + e)
    (i : Fin n) :
    (∑ j, |r i j| ^ 4) ≤
      16 * A ^ 4 * (∑' k, (strideFirstDecay b d k) ^ 4) + 8 * n * e ^ 4 := by
  have hsum : (∑ j, |r i j| ^ 4) ≤
      ∑ j : Fin n,
        (8 * A ^ 4 * (strideFirstDecay b d (Nat.dist j.val i.val)) ^ 4 +
          8 * e ^ 4) := by
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hr i j) 4
    nlinarith [sq_nonneg
      ((A * strideFirstDecay b d (Nat.dist j.val i.val)) ^ 2 - e ^ 2),
      sq_nonneg
      ((A * strideFirstDecay b d (Nat.dist j.val i.val)) - e)]
  have hdist := grid_distance_sum_le_tsum
    (fun k => (strideFirstDecay b d k) ^ 4)
    (strideFirstDecay_fourth_summable b hb d hd) (fun k => by positivity) n i
  have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 8 * A ^ 4 by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith

theorem first_stride_fourth_rows_of_covariance
    (a b C : ℝ) (d : ℕ) (hd : 0 < d)
    (ha : 0 < a) (hb : b < 7 / 8) (hab : a ≤ b) (hC : 0 ≤ C) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ n →
      ∀ H : Fin m → Ioo (0 : ℝ) 1, (∀ i, (H i : ℝ) ∈ Icc a b) →
      ∀ W : Fin m → Lp ℂ 2 (volume : Measure ℝ),
      (∀ i j, |⟪W i, W j⟫ -
        ⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d : ℝ) / n),
          normalizedFrozenIncrement (H j) (grid n j.val) ((d : ℝ) / n)⟫| ≤
            gridCovarianceError b C n) →
      (∀ i, W i ≠ 0) ∧
        ∀ i, (∑ j, |vectorCorrelation (W i) (W j)| ^ 4) ≤ R := by
  obtain ⟨A, hA, hdec⟩ :=
    frozen_stride_first_grid_decay_lt_one a b ha (by linarith) hab d hd
  let S := ∑' k, strideFirstDecay b d k ^ 4
  refine ⟨4096 * A ^ 4 * S + 2048, by dsimp [S]; positivity, ?_⟩
  have he := (gridCovarianceError_tendsto b C (by linarith)).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he4 := (gridCovarianceError_fourth_row_tendsto b C hb).eventually_le_const
    zero_lt_one
  filter_upwards [eventually_ge_atTop 1, he, he4] with n hn hsmall hfourth
  intro m hmn H hH W hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let e := gridCovarianceError b C n
  have he0 : 0 ≤ e := by
    dsimp [e, gridCovarianceError]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  have hfloor : ∀ i, (1 / 2 : ℝ) ≤ ‖W i‖ := by
    intro i
    have hh := hp i i
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hh
    have hlow := (abs_le.mp hh).1
    nlinarith [norm_nonneg (W i)]
  refine ⟨?_, ?_⟩
  · intro i hz
    have hi := hfloor i
    rw [hz, norm_zero] at hi
    norm_num at hi
  · intro i
    have hcorr : ∀ i j,
        |vectorCorrelation (W i) (W j)| ≤
          4 * A * strideFirstDecay b d (Nat.dist j.val i.val) + 4 * e := by
      intro i j
      have hf := hdec n m (by omega) H hH i j
      have hpij := hp i j
      have ht := abs_add_le
        (⟪W i, W j⟫ -
          ⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d : ℝ) / n),
            normalizedFrozenIncrement (H j) (grid n j.val) ((d : ℝ) / n)⟫)
        ⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d : ℝ) / n),
          normalizedFrozenIncrement (H j) (grid n j.val) ((d : ℝ) / n)⟫
      rw [sub_add_cancel] at ht
      have hc := vectorCorrelation_bound_of_norm_floor
        (W i) (W j) (hfloor i) (hfloor j)
      dsimp only [e]
      linarith
    have hs := stride_first_correlation_fourth_row_bound b (4 * A) (4 * e)
      d hd hb (by positivity) (by positivity) m
      (fun i j => vectorCorrelation (W i) (W j)) hcorr i
    have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hm4 := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ e ^ 4)
    change (n : ℝ) * e ^ 4 ≤ 1 at hfourth
    dsimp only [S]
    nlinarith

theorem hurstHolder_stride_first_correlation_fourth_rows
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 7 / 8)
    (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ,
      ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      (∀ i, gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i ≠ 0) ∧
        ∀ i : Fin (n - d),
          (∑ j, |vectorCorrelation
            (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i)
            (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) j)| ^ 4) ≤ R := by
  obtain ⟨C, hC, hcov⟩ :=
    hurstHolder_stride_first_covariance p a b M hp ha (by linarith) hab hM d hd
  obtain ⟨R, hR, hrows⟩ :=
    first_stride_fourth_rows_of_covariance a b C d hd ha hb hab hC
  refine ⟨R, hR, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop 1] with n hn hn1
  intro f hf hF
  exact hn (n - d) (Nat.sub_le _ _)
    (fun i => midpointSampleHurst f hf.1 n (strideFirstLeft n d i))
    (fun i => hF (grid_mem n _ (by omega) (strideFirstLeft n d i).isLt))
    (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n))
    (hcov n (by omega) f hf hF)

theorem hurstHolder_stride_first_weighted_fourth_small
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 7 / 8)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (δ c : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hscale : Tendsto (fun n : ℕ => c n ^ 2 / ((n : ℝ) * δ n))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => c n ^ 2 *
      (∑ i, ∑ j,
        |localPolynomialWeights r n 1 (δ n) t i| *
        |localPolynomialWeights r n 1 (δ n) t j| *
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridStrideFirstCoefficients n 1 i)
          (gridStrideFirstCoefficients n 1 j)| ^ 4)) atTop (𝓝 0) := by
  obtain ⟨R, hR, hrows⟩ :=
    hurstHolder_stride_first_correlation_fourth_rows p a b M hp ha hb hab hM
      1 (by norm_num)
  obtain ⟨N₀, hN₀, D, hD, hw⟩ := localPolynomialWeights_uniform_stability r 1
  apply squeeze_zero'
  · filter_upwards [] with n
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => by positivity)))
  · filter_upwards [hrows,
      hδ, hδ0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop N₀, eventually_ge_atTop 2] with
      n hnrows hnδ hnδhalf hnN hn2
    have hn0 : 0 < n := by omega
    obtain ⟨hnonzero, hrow⟩ := hnrows f hf hF
    obtain ⟨_, hmax, hl1, _⟩ :=
      hw n hn0 (by omega) (δ n) t hnδ hnδhalf.le ht hnN
    let corr := fun i j : Fin (n - 1) =>
      featureCorrelation
        (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
        (gridStrideFirstCoefficients n 1 i) (gridStrideFirstCoefficients n 1 j)
    have hcorr : ∀ i j, abs (corr i j) ≤ 1 := by
      intro i j
      apply featureCorrelation_abs_le_one
      · rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
          (midpointSampleHurst f hf.1 n) i]
        exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hnonzero i)
      · rw [gridStrideFirst_feature_identity n 1 hn0 (by norm_num)
          (midpointSampleHurst f hf.1 n) j]
        exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' (hnonzero j)
    have hcorrrow : ∀ i, ∑ j, |corr i j| ^ 4 ≤ R := by
      intro i
      simpa only [corr, gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
        (midpointSampleHurst f hf.1 n)] using hrow i
    have hbound := weighted_double_sum_le_max_l1_row
      (localPolynomialWeights r n 1 (δ n) t)
      (fun i j => |corr i j| ^ 4)
      (D / ((n : ℝ) * δ n)) D R
      (by positivity) hD.le hR hmax hl1 (fun _ _ => by positivity) hcorrrow
    exact mul_le_mul_of_nonneg_left hbound (sq_nonneg (c n))
  · have h := hscale.const_mul (D ^ 2 * R)
    simp only [mul_zero] at h
    convert h using 1
    funext n
    ring

theorem firstLongNormalization_squared_over_effective_sample_tendsto
    (h : ℝ) (hh : 3 / 4 < h) (δ : ℕ → ℝ)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ =>
      firstLongNormalization h n (δ n) ^ 2 / ((n : ℝ) * δ n))
      atTop (𝓝 0) := by
  have hp : 0 < 4 * h - 3 := by linarith
  have ht := (tendsto_rpow_neg_atTop hp).comp hN
  apply ht.congr'
  filter_upwards [hN.eventually_gt_atTop 0] with n hn
  have he : (2 - 2 * h) * (2 : ℝ) - 1 = -(4 * h - 3) := by ring
  unfold firstLongNormalization
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le,
    ← Real.rpow_sub_one hn.ne']
  simp only [Function.comp_apply]
  congr 1
  simpa using he.symm

theorem firstCriticalNormalization_squared_over_effective_sample_tendsto
    (δ : ℕ → ℝ)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ =>
      firstCriticalNormalization n (δ n) ^ 2 / ((n : ℝ) * δ n))
      atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp hN
  have ht := tendsto_inv_atTop_zero.comp hlog
  apply ht.congr'
  filter_upwards [hN.eventually_gt_atTop 1] with n hn
  have hx : 0 < (n : ℝ) * δ n := zero_lt_one.trans hn
  have hl : 0 < Real.log ((n : ℝ) * δ n) := Real.log_pos hn
  unfold firstCriticalNormalization
  rw [Real.sq_sqrt (div_nonneg hx.le hl.le)]
  simp only [Function.comp_apply]
  field_simp
  rw [div_self hx.ne']

theorem hurstHolder_stride_first_long_weighted_fourth_small
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 7 / 8)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hft : 3 / 4 < f t)
    (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => firstLongNormalization (f t) n (δ n) ^ 2 *
      (∑ i, ∑ j,
        |localPolynomialWeights r n 1 (δ n) t i| *
        |localPolynomialWeights r n 1 (δ n) t j| *
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridStrideFirstCoefficients n 1 i)
          (gridStrideFirstCoefficients n 1 j)| ^ 4)) atTop (𝓝 0) :=
  hurstHolder_stride_first_weighted_fourth_small p a b M r hp ha hb hab hM
    f hf hF t ht δ (fun n => firstLongNormalization (f t) n (δ n))
    hδ hδ0 hN
    (firstLongNormalization_squared_over_effective_sample_tendsto
      (f t) hft δ hN)

theorem hurstHolder_stride_first_critical_weighted_fourth_small
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 7 / 8)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => firstCriticalNormalization n (δ n) ^ 2 *
      (∑ i, ∑ j,
        |localPolynomialWeights r n 1 (δ n) t i| *
        |localPolynomialWeights r n 1 (δ n) t j| *
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridStrideFirstCoefficients n 1 i)
          (gridStrideFirstCoefficients n 1 j)| ^ 4)) atTop (𝓝 0) :=
  hurstHolder_stride_first_weighted_fourth_small p a b M r hp ha hb hab hM
    f hf hF t ht δ (fun n => firstCriticalNormalization n (δ n))
    hδ hδ0 hN
    (firstCriticalNormalization_squared_over_effective_sample_tendsto δ hN)

theorem hurstHolder_q1_critical_weighted_fourth_small
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 7 / 8)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => firstCriticalNormalization n (δ n) ^ 2 *
      (∑ i, ∑ j,
        |localPolynomialWeights r n 1 (δ n) t i| *
        |localPolynomialWeights r n 1 (δ n) t j| *
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridDifferenceCoefficients n i)
          (gridDifferenceCoefficients n j)| ^ 4)) atTop (𝓝 0) := by
  simpa only [show ∀ n, gridDifferenceCoefficients n =
      gridStrideFirstCoefficients n 1 from fun _ => rfl] using
    hurstHolder_stride_first_critical_weighted_fourth_small p a b M r
      hp ha hb hab hM f hf hF t ht δ hδ hδ0 hN

theorem hurstHolder_q1_long_weighted_fourth_small
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 7 / 8)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hft : 3 / 4 < f t)
    (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => firstLongNormalization (f t) n (δ n) ^ 2 *
      (∑ i, ∑ j,
        |localPolynomialWeights r n 1 (δ n) t i| *
        |localPolynomialWeights r n 1 (δ n) t j| *
        |featureCorrelation
          (gridObservationFeatures n (midpointSampleHurst f hf.1 n))
          (gridDifferenceCoefficients n i)
          (gridDifferenceCoefficients n j)| ^ 4)) atTop (𝓝 0) := by
  simpa only [show ∀ n, gridDifferenceCoefficients n =
      gridStrideFirstCoefficients n 1 from fun _ => rfl] using
    hurstHolder_stride_first_long_weighted_fourth_small p a b M r
      hp ha hb hab hM f hf hF t ht hft δ hδ hδ0 hN

end Hurst
