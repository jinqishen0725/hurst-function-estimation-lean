import Hurst.FourthCorrelationRows
import Hurst.LatticeCount

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem strideFirstDecay_le_one (b : ℝ) (hb : b < 1) (d k : ℕ) (hd : 0 < d) :
    strideFirstDecay b d k ≤ 1 := by
  unfold strideFirstDecay
  split_ifs with hk
  · exact le_rfl
  · have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hbase : (1 : ℝ) ≤ ((k - d : ℕ) : ℝ) / d := by
      apply (le_div_iff₀ hdR).mpr
      norm_num only [one_mul]
      exact_mod_cast (show d ≤ k - d by omega)
    simpa using Real.rpow_le_rpow_of_exponent_le hbase (show 2 * b - 2 ≤ 0 by linarith)

theorem strideFirstDecay_square_row_bound_lt_one
    (b : ℝ) (hb : b < 1) (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (i : Fin n) :
    (∑ j : Fin n, strideFirstDecay b d (Nat.dist j.val i.val) ^ 2) ≤
      2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1 +
        (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
  classical
  let K : ℕ := Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d
  let S : Finset (Fin n) := Finset.univ.filter (fun j => Nat.dist j.val i.val ≤ K)
  let T : Finset (Fin n) := Finset.univ.filter (fun j => ¬ Nat.dist j.val i.val ≤ K)
  have hcard : (S.card : ℝ) ≤ 2 * (K : ℝ) + 1 := by
    have hc := finite_lattice_interval_card S ((i.val : ℝ) - K) ((i.val : ℝ) + K)
      (by linarith) (by
        intro j hj
        have hjdist : Nat.dist j.val i.val ≤ K := (Finset.mem_filter.mp hj).2
        have hleft : j.val ≤ i.val + K := by
          rcases le_total i.val j.val with hij | hji
          · rw [Nat.dist_eq_sub_of_le_right hij] at hjdist
            omega
          · omega
        have hright : i.val ≤ j.val + K := by
          rcases le_total j.val i.val with hji | hij
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right hji] at hjdist
            omega
          · omega
        have hleftR : (j.val : ℝ) ≤ i.val + K := by exact_mod_cast hleft
        have hrightR : (i.val : ℝ) ≤ j.val + K := by exact_mod_cast hright
        constructor <;> linarith)
    convert hc using 1 <;> ring
  have hnear : (∑ j ∈ S, strideFirstDecay b d (Nat.dist j.val i.val) ^ 2) ≤
      2 * (K : ℝ) + 1 := by
    calc
      _ ≤ ∑ _j ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_one₀ (strideFirstDecay_nonneg _ _ _) (strideFirstDecay_le_one b hb d _ hd)
      _ = (S.card : ℝ) := by simp
      _ ≤ _ := hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnR _
  have hfarpoint : ∀ j ∈ T,
      strideFirstDecay b d (Nat.dist j.val i.val) ≤
        (((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2) := by
    intro j hj
    have hjnot : ¬ Nat.dist j.val i.val ≤ K := (Finset.mem_filter.mp hj).2
    have hdist : 2 * d < Nat.dist j.val i.val := by
      dsimp [K] at hjnot
      omega
    simp only [strideFirstDecay, show ¬ Nat.dist j.val i.val ≤ 2 * d by omega, if_false]
    have hnum : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (Nat.dist j.val i.val - d : ℕ) := by
      have hceil := Nat.le_ceil ((n : ℝ) ^ (1 / 2 : ℝ))
      have hnat : Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) ≤ Nat.dist j.val i.val - d := by
        dsimp [K] at hjnot
        omega
      exact hceil.trans (by exact_mod_cast hnat)
    have hbase : ((n : ℝ) ^ (1 / 2 : ℝ)) / d ≤
        ((Nat.dist j.val i.val - d : ℕ) : ℝ) / d :=
      (div_le_div_iff_of_pos_right hdR).mpr hnum
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  have hfar : (∑ j ∈ T, strideFirstDecay b d (Nat.dist j.val i.val) ^ 2) ≤
      (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ T, ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_left₀ (strideFirstDecay_nonneg _ _ _) (hfarpoint j hj) 2
      _ = (T.card : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by simp
      _ ≤ (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hc : T.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
        exact_mod_cast hc
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin n => Nat.dist j.val i.val ≤ K)]
  simpa only [S, T, not_le] using add_le_add hnear hfar

theorem stride_first_correlation_square_row_bound_lt_one
    (b A e : ℝ) (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (hb : b < 1)
    (hA : 0 ≤ A) (he : 0 ≤ e) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, |r i j| ≤ A * strideFirstDecay b d (Nat.dist j.val i.val) + e)
    (i : Fin n) :
    (∑ j, r i j ^ 2) ≤
      2 * A ^ 2 *
        (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1 +
          (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2) +
        2 * (n : ℝ) * e ^ 2 := by
  have hsum : (∑ j, r i j ^ 2) ≤ ∑ j : Fin n,
      (2 * A ^ 2 * strideFirstDecay b d (Nat.dist j.val i.val) ^ 2 + 2 * e ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hr i j) 2
    rw [sq_abs] at h
    nlinarith [sq_nonneg (A * strideFirstDecay b d (Nat.dist j.val i.val) - e)]
  have hrow := strideFirstDecay_square_row_bound_lt_one b hb d n hd hn i
  have hmul := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 2 * A ^ 2 by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact hsum.trans (by nlinarith)

theorem strideFirstDecay_square_row_bound_ambient
    (b : ℝ) (hb : b < 1) (d m n : ℕ) (hd : 0 < d)
    (hm : 0 < m) (hmn : m ≤ n) (i : Fin m) :
    (∑ j : Fin m, strideFirstDecay b d (Nat.dist j.val i.val) ^ 2) ≤
      2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1 +
        (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
  classical
  let K : ℕ := Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d
  let S : Finset (Fin m) := Finset.univ.filter (fun j => Nat.dist j.val i.val ≤ K)
  let T : Finset (Fin m) := Finset.univ.filter (fun j => ¬ Nat.dist j.val i.val ≤ K)
  have hcard : (S.card : ℝ) ≤ 2 * (K : ℝ) + 1 := by
    have hc := finite_lattice_interval_card S ((i.val : ℝ) - K) ((i.val : ℝ) + K)
      (by linarith) (by
        intro j hj
        have hjdist : Nat.dist j.val i.val ≤ K := (Finset.mem_filter.mp hj).2
        have hleft : j.val ≤ i.val + K := by
          rcases le_total i.val j.val with hij | hji
          · rw [Nat.dist_eq_sub_of_le_right hij] at hjdist
            omega
          · omega
        have hright : i.val ≤ j.val + K := by
          rcases le_total j.val i.val with hji | hij
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right hji] at hjdist
            omega
          · omega
        have hleftR : (j.val : ℝ) ≤ i.val + K := by exact_mod_cast hleft
        have hrightR : (i.val : ℝ) ≤ j.val + K := by exact_mod_cast hright
        constructor <;> linarith)
    convert hc using 1 <;> ring
  have hnear : (∑ j ∈ S, strideFirstDecay b d (Nat.dist j.val i.val) ^ 2) ≤
      2 * (K : ℝ) + 1 := by
    calc
      _ ≤ ∑ _j ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_one₀ (strideFirstDecay_nonneg _ _ _)
          (strideFirstDecay_le_one b hb d _ hd)
      _ = (S.card : ℝ) := by simp
      _ ≤ _ := hcard
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfarpoint : ∀ j ∈ T,
      strideFirstDecay b d (Nat.dist j.val i.val) ≤
        (((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2) := by
    intro j hj
    have hjnot : ¬ Nat.dist j.val i.val ≤ K := (Finset.mem_filter.mp hj).2
    have hdist : 2 * d < Nat.dist j.val i.val := by
      dsimp [K] at hjnot
      omega
    simp only [strideFirstDecay,
      show ¬ Nat.dist j.val i.val ≤ 2 * d by omega, if_false]
    have hnum : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (Nat.dist j.val i.val - d : ℕ) := by
      have hceil := Nat.le_ceil ((n : ℝ) ^ (1 / 2 : ℝ))
      have hnat : Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) ≤
          Nat.dist j.val i.val - d := by
        dsimp [K] at hjnot
        omega
      exact hceil.trans (by exact_mod_cast hnat)
    have hbase : ((n : ℝ) ^ (1 / 2 : ℝ)) / d ≤
        ((Nat.dist j.val i.val - d : ℕ) : ℝ) / d :=
      (div_le_div_iff_of_pos_right hdR).mpr hnum
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  have hfar : (∑ j ∈ T, strideFirstDecay b d (Nat.dist j.val i.val) ^ 2) ≤
      (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ T,
          ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_left₀ (strideFirstDecay_nonneg _ _ _)
          (hfarpoint j hj) 2
      _ = (T.card : ℝ) *
          ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by simp
      _ ≤ (n : ℝ) *
          ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hc : T.card ≤ m := by
          simpa only [Fintype.card_fin] using Finset.card_le_univ T
        exact_mod_cast hc.trans hmn
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin m => Nat.dist j.val i.val ≤ K)]
  simpa only [S, T, not_le] using add_le_add hnear hfar

theorem stride_first_correlation_square_row_bound_ambient
    (b A e : ℝ) (d m n : ℕ) (hd : 0 < d) (hm : 0 < m) (hmn : m ≤ n)
    (hb : b < 1) (r : Fin m → Fin m → ℝ)
    (hr : ∀ i j, |r i j| ≤ A * strideFirstDecay b d (Nat.dist j.val i.val) + e)
    (i : Fin m) :
    (∑ j, r i j ^ 2) ≤
      2 * A ^ 2 *
        (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1 +
          (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2) +
        2 * (n : ℝ) * e ^ 2 := by
  have hsum : (∑ j, r i j ^ 2) ≤ ∑ j : Fin m,
      (2 * A ^ 2 * strideFirstDecay b d (Nat.dist j.val i.val) ^ 2 + 2 * e ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hr i j) 2
    rw [sq_abs] at h
    nlinarith [sq_nonneg (A * strideFirstDecay b d (Nat.dist j.val i.val) - e)]
  have hrow := strideFirstDecay_square_row_bound_ambient b hb d m n hd hm hmn i
  have hmul := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 2 * A ^ 2 by positivity)
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have herr := mul_le_mul_of_nonneg_right hmR (show 0 ≤ 2 * e ^ 2 by positivity)
  exact hsum.trans (by nlinarith)

/-- First-increment correlation rows for every upper Hurst bound `b < 1`.
The row bound is allowed to grow; after multiplication by the averaged weight
maximum `O(1/n)`, it still gives a polynomially vanishing variance. -/
theorem first_stride_rows_of_covariance_lt_one
    (a b C : ℝ) (d : ℕ) (hd : 0 < d)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hC : 0 ≤ C) :
    ∃ A ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ n →
      ∀ H : Fin m → Ioo (0 : ℝ) 1, (∀ i, (H i : ℝ) ∈ Icc a b) →
      ∀ W : Fin m → Lp ℂ 2 (volume : Measure ℝ),
      (∀ i j, |⟪W i, W j⟫ -
        ⟪normalizedFrozenIncrement (H i) (grid n i.val) ((d : ℝ) / n),
          normalizedFrozenIncrement (H j) (grid n j.val) ((d : ℝ) / n)⟫| ≤
            gridCovarianceError b C n) →
      (∀ i, W i ≠ 0) ∧ ∀ i,
        (∑ j, vectorCorrelation (W i) (W j) ^ 2) ≤
          2 * (4 * A) ^ 2 *
            (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1 +
              (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2) +
            2 * (n : ℝ) * (4 * gridCovarianceError b C n) ^ 2 := by
  obtain ⟨A, hA, hdec⟩ :=
    frozen_stride_first_grid_decay_lt_one a b ha hb hab d hd
  refine ⟨A, hA, ?_⟩
  have he := (gridCovarianceError_tendsto b C hb).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [eventually_ge_atTop 1, he] with n hn hsmall
  intro m hm hmn H hH W hp
  have he0 : 0 ≤ gridCovarianceError b C n := by
    unfold gridCovarianceError
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    positivity
  have hfloor : ∀ i, (1 / 2 : ℝ) ≤ ‖W i‖ := by
    intro i
    have hh := hp i i
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      normalizedFrozenIncrement_norm_sq _ _ _ (by
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
        positivity)] at hh
    have hlow := (abs_le.mp hh).1
    nlinarith [norm_nonneg (W i)]
  refine ⟨?_, ?_⟩
  · intro i hzero
    have hi := hfloor i
    rw [hzero, norm_zero] at hi
    norm_num at hi
  · intro i
    have hcorr : ∀ i j,
        |vectorCorrelation (W i) (W j)| ≤
          4 * A * strideFirstDecay b d (Nat.dist j.val i.val) +
            4 * gridCovarianceError b C n := by
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
      linarith
    exact stride_first_correlation_square_row_bound_ambient b (4 * A)
      (4 * gridCovarianceError b C n) d m n hd hm hmn hb
      (fun i j => vectorCorrelation (W i) (W j)) hcorr i

theorem hurstHolder_stride_first_correlation_rows_lt_one
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ A ≥ 1, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      (∀ i, gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i ≠ 0) ∧
      ∀ i : Fin (n - d),
        (∑ j, vectorCorrelation
          (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i)
          (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) j) ^ 2) ≤
          2 * (4 * A) ^ 2 *
            (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1 +
              (n : ℝ) * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2) +
            2 * (n : ℝ) * (4 * gridCovarianceError b C n) ^ 2 := by
  obtain ⟨C, hC, hcov⟩ :=
    hurstHolder_stride_first_covariance p a b M hp ha hb hab hM d hd
  obtain ⟨A, hA, hrows⟩ :=
    first_stride_rows_of_covariance_lt_one a b C d hd ha hb hab hC
  refine ⟨A, hA, C, hC, ?_⟩
  filter_upwards [hrows, eventually_ge_atTop (d + 1)] with n hn hnlarge
  intro f hf hF
  exact hn (n - d) (by omega) (Nat.sub_le _ _)
    (fun i => midpointSampleHurst f hf.1 n (strideFirstLeft n d i))
    (fun i => hF (grid_mem n _ (by omega) (strideFirstLeft n d i).isLt))
    (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n))
    (hcov n (by omega) f hf hF)

end Hurst
