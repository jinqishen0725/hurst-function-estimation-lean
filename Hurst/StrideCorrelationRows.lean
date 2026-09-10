import Hurst.StrideDecay
import Hurst.HilbertPerturbation

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology ENNReal
namespace Hurst

/-- Uniform correlation rows for actual vectors close to the frozen second-difference features. -/
theorem stride_second_grid_correlation_rows_of_perturbation (a b C : ℝ) (d : ℕ) (hd : 0 < d)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hC : 0 ≤ C) :
    ∃ R ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ n →
      ∀ H : Fin m → Ioo (0 : ℝ) 1, (∀ i, (H i : ℝ) ∈ Icc a b) →
      ∀ W : Fin m → Lp ℂ 2 (volume : Measure ℝ),
      (∀ i, ‖W i - normalizedFrozenSecondIncrement (H i) (grid n i.val) ((d : ℝ) / n)‖ ≤
        gridCovarianceError (1 / 2) C n) →
      (∀ i, W i ≠ 0) ∧ ∀ i : Fin m, (∑ j, vectorCorrelation (W i) (W j) ^ 2) ≤ R := by
  obtain ⟨A, hA, hdec⟩ := frozen_stride_second_grid_decay a b ha hb hab d hd
  obtain ⟨c, hc, hfloor⟩ := normalizedFrozenSecondIncrement_uniform_norm_floor b hb
  let K : ℝ := ((c / 2) ^ 2)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let S : ℝ := ∑' k, strideSecondDecay b d k ^ 2
  refine ⟨4 * (K * A) ^ 2 * S + 50 * K ^ 2, by dsimp [S]; positivity, ?_⟩
  have he1 := (gridCovarianceError_tendsto (1 / 2) C (by norm_num)).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hec := (gridCovarianceError_tendsto (1 / 2) C (by norm_num)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < c / 2 by positivity))
  have hes := (gridCovarianceError_square_row_tendsto (1 / 2) C (by norm_num)).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1, he1, hec, hes] with n hn he1 hec hes
  intro m hmn H hH W hW
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let e := gridCovarianceError (1 / 2) C n
  have he0 : 0 ≤ e := by
    dsimp [e, gridCovarianceError]
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  let V := fun i : Fin m => normalizedFrozenSecondIncrement (H i) (grid n i.val) ((d : ℝ) / n)
  have hnorm : ∀ i, c / 2 ≤ ‖W i‖ := by
    intro i
    have he := norm_floor_of_perturbation (W i) (V i) c e
      (hfloor (H i) (hH i).2 _ _ (by positivity)) (hW i)
    change c - gridCovarianceError (1 / 2) C n ≤ ‖W i‖ at he
    linarith
  refine ⟨?_, ?_⟩
  · intro i hz
    have hi := hnorm i
    rw [hz, norm_zero] at hi
    linarith
  · intro i
    have hpert : ∀ i j, |⟪W i, W j⟫ - ⟪V i, V j⟫| ≤ 5 * e := by
      intro i j
      have he := inner_perturbation_norm_bound (W i) (W j) (V i) (V j) 2 e (by norm_num) he0
        (normalizedFrozenSecondIncrement_norm_le _ _ _ (by positivity))
        (normalizedFrozenSecondIncrement_norm_le _ _ _ (by positivity)) (hW i) (hW j)
      have hesq : e ^ 2 ≤ e := by dsimp [e]; nlinarith
      nlinarith
    have hcorr : ∀ i j, |vectorCorrelation (W i) (W j)| ≤
        (K * A) * strideSecondDecay b d (Nat.dist j.val i.val) + 5 * K * e := by
      intro i j
      have hd := hdec n m (by omega) H hH i j
      have hp := hpert i j
      have ht := abs_add_le (⟪W i, W j⟫ - ⟪V i, V j⟫) ⟪V i, V j⟫
      rw [sub_add_cancel] at ht
      have hu := vectorCorrelation_bound_of_positive_floor (W i) (W j) (c / 2) (by positivity) (hnorm i) (hnorm j)
      have hh : |⟪W i, W j⟫| ≤ A * strideSecondDecay b d (Nat.dist j.val i.val) + 5 * e := by
        change |⟪V i, V j⟫| ≤ _ at hd
        linarith
      have hm := mul_le_mul_of_nonneg_left hh hK.le
      change |vectorCorrelation (W i) (W j)| ≤ K * |⟪W i, W j⟫| at hu
      exact (hu.trans hm).trans_eq (by ring)
    have hs := stride_second_correlation_square_row_bound b (K * A) (5 * K * e) d hd hb (by positivity) (by positivity)
      m (fun i j => vectorCorrelation (W i) (W j)) hcorr i
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have he2 := mul_le_mul_of_nonneg_right hmnR (sq_nonneg e)
    have hne : (n : ℝ) * e ^ 2 ≤ 1 := hes.le
    have hsmall := mul_le_mul_of_nonneg_left (he2.trans hne) (show 0 ≤ 50 * K ^ 2 by positivity)
    dsimp only [S]
    nlinarith

end Hurst
