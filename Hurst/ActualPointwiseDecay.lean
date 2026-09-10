import Hurst.FirstStrideActualRows
import Hurst.StrideLogVariance

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem hurstHolder_stride_first_correlation_decay
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 3 / 4)
    (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ A ≥ 1, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      (∀ i, gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i ≠ 0) ∧
      ∀ i j : Fin (n - d),
        |vectorCorrelation
          (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i)
          (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) j)| ≤
          4 * A * strideFirstDecay b d (Nat.dist j.val i.val) +
            4 * gridCovarianceError b C n := by
  obtain ⟨C, hC, hcov⟩ :=
    hurstHolder_stride_first_covariance p a b M hp ha (by linarith) hab hM d hd
  obtain ⟨A, hA, hdec⟩ := frozen_stride_first_grid_decay a b ha hb hab d hd
  refine ⟨A, hA, C, hC, ?_⟩
  have hsmall := (gridCovarianceError_tendsto b C (by linarith)).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hsmall hn
  intro f hf hF
  let H := midpointSampleHurst f hf.1 n
  let W := gridStrideFirstActual n d H
  have hn0 : 0 < n := by omega
  have hH : ∀ i : Fin (n - d),
      (H (strideFirstLeft n d i) : ℝ) ∈ Icc a b := by
    intro i
    exact hF (grid_mem n _ hn0 (strideFirstLeft n d i).isLt)
  have hp := hcov n hn0 f hf hF
  have hfloor : ∀ i, (1 / 2 : ℝ) ≤ ‖W i‖ := by
    intro i
    have hi := hp i i
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      normalizedFrozenIncrement_norm_sq _ _ _ (by positivity)] at hi
    have hlo := (abs_le.mp hi).1
    change gridCovarianceError b C n ≤ 1 / 2 at hsmall
    nlinarith [norm_nonneg (W i)]
  refine ⟨?_, ?_⟩
  · intro i hi
    have hflo := hfloor i
    change (1 / 2 : ℝ) ≤
      ‖gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i‖ at hflo
    rw [hi, norm_zero] at hflo
    norm_num at hflo
  · intro i j
    have hfr := hdec n (n - d) hn0
      (fun k => H (strideFirstLeft n d k)) hH i j
    have hpert := hp i j
    have htri := abs_add_le
      (⟪W i, W j⟫ -
        ⟪normalizedFrozenIncrement (H (strideFirstLeft n d i))
            (grid n i.val) ((d : ℝ) / n),
          normalizedFrozenIncrement (H (strideFirstLeft n d j))
            (grid n j.val) ((d : ℝ) / n)⟫)
      ⟪normalizedFrozenIncrement (H (strideFirstLeft n d i))
          (grid n i.val) ((d : ℝ) / n),
        normalizedFrozenIncrement (H (strideFirstLeft n d j))
          (grid n j.val) ((d : ℝ) / n)⟫
    rw [sub_add_cancel] at htri
    have hc := vectorCorrelation_bound_of_norm_floor (W i) (W j)
      (hfloor i) (hfloor j)
    change |vectorCorrelation (W i) (W j)| ≤
      4 * A * strideFirstDecay b d (Nat.dist j.val i.val) +
        4 * gridCovarianceError b C n
    exact hc.trans (by linarith)

theorem hurstHolder_stride_second_correlation_decay
    (p a b M : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ A ≥ 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      (∀ i, gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) i ≠ 0) ∧
      ∀ i j : Fin (n - 2 * d),
        |vectorCorrelation
          (gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) i)
          (gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) j)| ≤
          A * strideSecondDecay b d (Nat.dist j.val i.val) +
            A * gridCovarianceError (1 / 2) C n := by
  obtain ⟨C, hC, hrem⟩ :=
    hurstHolder_grid_stride_second_remainder p a b M hp ha hb hab hM d hd
  obtain ⟨B, hB, hdec⟩ := frozen_stride_second_grid_decay a b ha hb hab d hd
  obtain ⟨c, hc, hfloor⟩ := normalizedFrozenSecondIncrement_uniform_norm_floor b hb
  let K : ℝ := ((c / 2) ^ 2)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let A := K * (B + 5)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, C, hC, ?_⟩
  have hsmall := (gridCovarianceError_tendsto (1 / 2) C (by norm_num)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < min 1 (c / 2) by positivity))
  filter_upwards [hsmall, eventually_ge_atTop d] with n hsmall hn
  intro f hf hF
  let H := midpointSampleHurst f hf.1 n
  let W := gridStrideSecondActual n d H
  let V := fun i : Fin (n - 2 * d) =>
    normalizedFrozenSecondIncrement (H (strideSecondLeft n d i))
      (grid n i.val) ((d : ℝ) / n)
  have hn0 : 0 < n := lt_of_lt_of_le hd hn
  have he0 : 0 ≤ gridCovarianceError (1 / 2) C n := by
    unfold gridCovarianceError
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  have hH : ∀ i : Fin (n - 2 * d),
      (H (strideSecondLeft n d i) : ℝ) ∈ Icc a b := by
    intro i
    exact hF (grid_mem n _ hn0 (strideSecondLeft n d i).isLt)
  have hW : ∀ i, ‖W i - V i‖ ≤ gridCovarianceError (1 / 2) C n := by
    intro i
    exact hrem f hf hF n hn i
  have hnorm : ∀ i, c / 2 ≤ ‖W i‖ := by
    intro i
    have hi := norm_floor_of_perturbation (W i) (V i) c
      (gridCovarianceError (1 / 2) C n)
      (hfloor (H (strideSecondLeft n d i)) (hH i).2 _ _ (by positivity)) (hW i)
    have hs : gridCovarianceError (1 / 2) C n < c / 2 :=
      hsmall.trans_le (min_le_right _ _)
    linarith
  refine ⟨?_, ?_⟩
  · intro i hi
    have hflo := hnorm i
    change c / 2 ≤
      ‖gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) i‖ at hflo
    rw [hi, norm_zero] at hflo
    linarith
  · intro i j
    have hpert : |⟪W i, W j⟫ - ⟪V i, V j⟫| ≤
        5 * gridCovarianceError (1 / 2) C n := by
      have hi := inner_perturbation_norm_bound (W i) (W j) (V i) (V j) 2
        (gridCovarianceError (1 / 2) C n) (by norm_num) he0
        (normalizedFrozenSecondIncrement_norm_le _ _ _ (by positivity))
        (normalizedFrozenSecondIncrement_norm_le _ _ _ (by positivity)) (hW i) (hW j)
      have hs : gridCovarianceError (1 / 2) C n < 1 :=
        hsmall.trans_le (min_le_left _ _)
      have he2 : gridCovarianceError (1 / 2) C n ^ 2 ≤
          gridCovarianceError (1 / 2) C n := by nlinarith
      nlinarith
    have hfr := hdec n (n - 2 * d) hn0
      (fun k => H (strideSecondLeft n d k)) hH i j
    have htri := abs_add_le (⟪W i, W j⟫ - ⟪V i, V j⟫) ⟪V i, V j⟫
    rw [sub_add_cancel] at htri
    have hi : |⟪W i, W j⟫| ≤
        B * strideSecondDecay b d (Nat.dist j.val i.val) +
          5 * gridCovarianceError (1 / 2) C n := by linarith
    have hcorr := vectorCorrelation_bound_of_positive_floor
      (W i) (W j) (c / 2) (by positivity) (hnorm i) (hnorm j)
    have hscaled := mul_le_mul_of_nonneg_left hi hK.le
    have hpre : |vectorCorrelation (W i) (W j)| ≤
        K * (B * strideSecondDecay b d (Nat.dist j.val i.val) +
          5 * gridCovarianceError (1 / 2) C n) := by
      exact hcorr.trans hscaled
    change |vectorCorrelation (W i) (W j)| ≤
      A * strideSecondDecay b d (Nat.dist j.val i.val) +
        A * gridCovarianceError (1 / 2) C n
    apply hpre.trans
    dsimp only [A]
    have hdcy := strideSecondDecay_nonneg b d (Nat.dist j.val i.val)
    rw [show K * (B + 5) * strideSecondDecay b d (Nat.dist j.val i.val) +
        K * (B + 5) * gridCovarianceError (1 / 2) C n =
      K * ((B + 5) * strideSecondDecay b d (Nat.dist j.val i.val) +
        (B + 5) * gridCovarianceError (1 / 2) C n) by ring]
    apply mul_le_mul_of_nonneg_left _ hK.le
    calc
      B * strideSecondDecay b d (Nat.dist j.val i.val) +
          5 * gridCovarianceError (1 / 2) C n ≤
          (B + 5) * strideSecondDecay b d (Nat.dist j.val i.val) +
            5 * gridCovarianceError (1 / 2) C n := by
        gcongr
        linarith
      _ ≤ (B + 5) * strideSecondDecay b d (Nat.dist j.val i.val) +
          (B + 5) * gridCovarianceError (1 / 2) C n := by
        gcongr
        linarith

end Hurst
