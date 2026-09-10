import Hurst.ActualFirstLongKernelTransfer

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- Quantitative normalization lemma.  If a Gram matrix is within `e` of a
unit-diagonal reference Gram matrix, normalization changes every entry by at
most `4e`. -/
theorem vectorCorrelation_sub_unitGram_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v a b : E) (e : ℝ) (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (haa : ‖a‖ ^ 2 = 1) (hbb : ‖b‖ ^ 2 = 1)
    (huu : |‖u‖ ^ 2 - ‖a‖ ^ 2| ≤ e)
    (hvv : |‖v‖ ^ 2 - ‖b‖ ^ 2| ≤ e)
    (huv : |⟪u, v⟫ - ⟪a, b⟫| ≤ e) :
    |vectorCorrelation u v - ⟪a, b⟫| ≤ 4 * e := by
  have hu2 : |‖u‖ ^ 2 - 1| ≤ e := by simpa only [haa] using huu
  have hv2 : |‖v‖ ^ 2 - 1| ≤ e := by simpa only [hbb] using hvv
  have hulow : (1 / 2 : ℝ) ≤ ‖u‖ := by
    have h := (abs_le.mp hu2).1
    nlinarith [norm_nonneg u]
  have hvlow : (1 / 2 : ℝ) ≤ ‖v‖ := by
    have h := (abs_le.mp hv2).1
    nlinarith [norm_nonneg v]
  have huup : ‖u‖ ≤ 2 := by
    have h := (abs_le.mp hu2).2
    nlinarith [norm_nonneg u]
  have hvup : ‖v‖ ≤ 2 := by
    have h := (abs_le.mp hv2).2
    nlinarith [norm_nonneg v]
  have hu1 : |‖u‖ - 1| ≤ e := by
    have hid : |‖u‖ ^ 2 - 1| = |‖u‖ - 1| * (‖u‖ + 1) := by
      rw [show ‖u‖ ^ 2 - 1 = (‖u‖ - 1) * (‖u‖ + 1) by ring,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖ + 1)]
    rw [hid] at hu2
    exact (le_mul_of_one_le_right (abs_nonneg _) (by linarith [norm_nonneg u])).trans hu2
  have hv1 : |‖v‖ - 1| ≤ e := by
    have hid : |‖v‖ ^ 2 - 1| = |‖v‖ - 1| * (‖v‖ + 1) := by
      rw [show ‖v‖ ^ 2 - 1 = (‖v‖ - 1) * (‖v‖ + 1) by ring,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖v‖ + 1)]
    rw [hid] at hv2
    exact (le_mul_of_one_le_right (abs_nonneg _) (by linarith [norm_nonneg v])).trans hv2
  have hprod : |‖u‖ * ‖v‖ - 1| ≤ 3 * e := by
    have hid : ‖u‖ * ‖v‖ - 1 = (‖u‖ - 1) * ‖v‖ + (‖v‖ - 1) := by ring
    rw [hid]
    calc
      _ ≤ |(‖u‖ - 1) * ‖v‖| + |‖v‖ - 1| := abs_add_le _ _
      _ = |‖u‖ - 1| * ‖v‖ + |‖v‖ - 1| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
      _ ≤ e * 2 + e := add_le_add (mul_le_mul hu1 hvup (norm_nonneg v) he) hv1
      _ = 3 * e := by ring
  have hden : 0 < ‖u‖ * ‖v‖ := mul_pos (lt_of_lt_of_le (by norm_num) hulow)
    (lt_of_lt_of_le (by norm_num) hvlow)
  have hinner : |⟪u, v⟫| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
  have hnormchange :
      |⟪u, v⟫ / (‖u‖ * ‖v‖) - ⟪u, v⟫| ≤ 3 * e := by
    rw [show ⟪u, v⟫ / (‖u‖ * ‖v‖) - ⟪u, v⟫ =
      ⟪u, v⟫ / (‖u‖ * ‖v‖) * (1 - ‖u‖ * ‖v‖) by
        field_simp [hden.ne'],
      abs_mul, abs_div, abs_of_pos hden,
      abs_sub_comm (1 : ℝ) (‖u‖ * ‖v‖)]
    have hratio : |⟪u, v⟫| / (‖u‖ * ‖v‖) ≤ 1 :=
      (div_le_one hden).2 hinner
    exact (mul_le_mul hratio hprod (abs_nonneg _) (by norm_num)).trans_eq
      (one_mul _)
  unfold vectorCorrelation
  calc
    |⟪u, v⟫ / (‖u‖ * ‖v‖) - ⟪a, b⟫| ≤
        |⟪u, v⟫ / (‖u‖ * ‖v‖) - ⟪u, v⟫| +
          |⟪u, v⟫ - ⟪a, b⟫| := by
      rw [show ⟪u, v⟫ / (‖u‖ * ‖v‖) - ⟪a, b⟫ =
        (⟪u, v⟫ / (‖u‖ * ‖v‖) - ⟪u, v⟫) +
          (⟪u, v⟫ - ⟪a, b⟫) by ring]
      exact abs_add_le _ _
    _ ≤ 3 * e + e := add_le_add hnormchange huv
    _ = 4 * e := by ring

/-- Uniform actual-to-frozen correlation perturbation for all q=1 stride
increments.  This is the quantitative input needed by the off-diagonal mesh
argument. -/
theorem hurstHolder_stride_first_correlation_perturbation
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (d : ℕ) (hd : 0 < d) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → gridCovarianceError b C n ≤ 1 / 2 →
      ∀ i j : Fin (n - d),
      |vectorCorrelation
          (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i)
          (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) j) -
        ⟪normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n d i))
            (grid n i.val) ((d : ℝ) / n),
          normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n d j))
            (grid n j.val) ((d : ℝ) / n)⟫| ≤
        4 * gridCovarianceError b C n := by
  obtain ⟨C, hC, hcov⟩ :=
    hurstHolder_stride_first_covariance p a b M hp ha hb hab hM d hd
  refine ⟨C, hC, ?_⟩
  intro n hn hsmall i j
  let H := midpointSampleHurst f hf.1 n
  let U := gridStrideFirstActual n d H i
  let V := gridStrideFirstActual n d H j
  let A := normalizedFrozenIncrement (H (strideFirstLeft n d i))
    (grid n i.val) ((d : ℝ) / n)
  let B := normalizedFrozenIncrement (H (strideFirstLeft n d j))
    (grid n j.val) ((d : ℝ) / n)
  have hstep : 0 < (d : ℝ) / n := by positivity
  have hAA : ‖A‖ ^ 2 = 1 := by
    exact normalizedFrozenIncrement_norm_sq _ _ _ hstep
  have hBB : ‖B‖ ^ 2 = 1 := by
    exact normalizedFrozenIncrement_norm_sq _ _ _ hstep
  have hii := hcov n hn f hf hF i i
  have hjj := hcov n hn f hf hF j j
  have hij := hcov n hn f hf hF i j
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hii hjj
  exact vectorCorrelation_sub_unitGram_le U V A B
    (gridCovarianceError b C n)
    (by
      unfold gridCovarianceError
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
      positivity)
    hsmall hAA hBB (by simpa only [U, A, H] using hii)
    (by simpa only [V, B, H] using hjj)
    (by simpa only [U, V, A, B, H] using hij)

end Hurst
