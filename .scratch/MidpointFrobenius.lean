import Hurst.MatrixEstimates
import Hurst.MixedKernel

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem matrix_frobenius_bound_of_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (K : ℝ) (_hK : 0 ≤ K) (hA : ∀ i j, |A i j| ≤ K / n) :
    (∑ i, ∑ j, (A i j) ^ 2) ≤ K ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (K / n) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have he := pow_le_pow_left₀ (abs_nonneg (A i j)) (hA i j) 2
      simpa only [sq_abs] using he
    _ = K ^ 2 := by simp [div_pow, hnR]; field_simp

theorem gram_frobenius_bound_of_energy {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Fin n → E) (R : ℝ)
    (hR : ∑ i, ‖v i‖ ^ 2 ≤ R) :
    (∑ i, ∑ j, (Matrix.gram ℝ v i j) ^ 2) ≤ R ^ 2 := by
  have he : (∑ i, ∑ j, (Matrix.gram ℝ v i j) ^ 2) ≤ (∑ i, ‖v i‖ ^ 2) ^ 2 := by
    calc
      _ ≤ ∑ i, ∑ j, ‖v i‖ ^ 2 * ‖v j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have hb := pow_le_pow_left₀ (abs_nonneg ⟪v j, v i⟫) (abs_real_inner_le_norm (v j) (v i)) 2
        simpa only [Matrix.gram_apply, sq_abs, mul_pow, mul_comm, real_inner_comm] using hb
      _ = _ := by rw [pow_two, Finset.sum_mul_sum]
  exact he.trans (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hR 2)

theorem sq_add_four_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

theorem gram_sum_frobenius_bound {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U V : Fin n → E) (A Q R : ℝ)
    (hA : (∑ i, ∑ j, ((Matrix.gram ℝ U - 1) i j) ^ 2) ≤ A)
    (hQ : (∑ i, ∑ j, ⟪U i, V j⟫ ^ 2) ≤ Q)
    (hR : (∑ i, ∑ j, (Matrix.gram ℝ V i j) ^ 2) ≤ R) :
    (∑ i, ∑ j, ((Matrix.gram ℝ (fun i => U i + V i) - 1) i j) ^ 2) ≤ 4 * A + 8 * Q + 4 * R := by
  have hpoint : ∀ i j, ((Matrix.gram ℝ (fun i => U i + V i) - 1) i j) ^ 2 ≤
      4 * (((Matrix.gram ℝ U - 1) i j) ^ 2 + ⟪U j, V i⟫ ^ 2 + ⟪V j, U i⟫ ^ 2 + (Matrix.gram ℝ V i j) ^ 2) := by
    intro i j
    have he : (Matrix.gram ℝ (fun i => U i + V i) - 1) i j =
        (Matrix.gram ℝ U - 1) i j + ⟪U j, V i⟫ + ⟪V j, U i⟫ + Matrix.gram ℝ V i j := by
      simp only [Matrix.sub_apply, Matrix.gram_apply, inner_add_left, inner_add_right]
      rw [real_inner_comm (U j) (V i), real_inner_comm (V j) (U i)]
      ring
    rw [he]
    exact sq_add_four_le _ _ _ _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint i j))
  have hQ' : (∑ i, ∑ j, ⟪U j, V i⟫ ^ 2) ≤ Q := by rw [Finset.sum_comm]; exact hQ
  have hQ'' : (∑ i, ∑ j, ⟪V j, U i⟫ ^ 2) ≤ Q := by simpa only [real_inner_comm] using hQ
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  linarith

/-- The sum of squared variation-column norms is independent of the grid size. -/
theorem midpoint_variation_uniform_energy_bound :
    ∃ D ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ B : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ B →
      (∀ i, i.val ≠ 0 → |(h i : ℝ) - h (previousGridIndex i)| ≤ B * midpointStep n i) →
      (∑ i, ‖hurstVariationFeature (h i) (previousGridHurst h i) (midpointLeft n i) (midpointStep n i)‖ ^ 2) ≤ (D * B) ^ 2 := by
  obtain ⟨D, hD, hd⟩ := hurstVariationFeature_uniform_bound (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro n h B hh hB hstep
  have hp : ∀ i, ‖hurstVariationFeature (h i) (previousGridHurst h i)
      (midpointLeft n i) (midpointStep n i)‖ ^ 2 ≤ (D * B) ^ 2 * midpointStep n i := by
    intro i
    have hprev : (previousGridHurst h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
      unfold previousGridHurst
      split_ifs <;> exact hh _
    have hdiff : |(h i : ℝ) - previousGridHurst h i| ≤ B * midpointStep n i := by
      by_cases hi : i.val = 0
      · simp only [previousGridHurst, if_pos hi, sub_self, abs_zero]
        exact mul_nonneg hB (midpointStep_pos n i).le
      · simpa only [previousGridHurst, if_neg hi] using hstep i hi
    have he := hd (h i) (previousGridHurst h i) (hh i) hprev (midpointLeft n i) (midpointStep n i) B
      (by rw [abs_of_nonneg (midpointLeft_bounds n i).1]; exact (midpointLeft_bounds n i).2.le)
      (midpointStep_pos n i) hB hdiff
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simpa only [mul_pow, Real.sq_sqrt (midpointStep_pos n i).le] using hs
  calc
    _ ≤ ∑ i, (D * B) ^ 2 * midpointStep n i := Finset.sum_le_sum (fun i _ => hp i)
    _ = (D * B) ^ 2 * ∑ i, midpointStep n i := (Finset.mul_sum _ _ _).symm
    _ ≤ (D * B) ^ 2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (midpointStep_sum_le_one n) (sq_nonneg (D * B))

/-- The total error bound is on the actual covariance, including both mixed terms. -/
theorem midpoint_whitened_frobenius_components :
    ∃ C ≥ 0, ∃ K ≥ 0, ∃ D ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ a B : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ a → 0 ≤ B →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) →
      (∀ i, i.val ≠ 0 → |(h i : ℝ) - h (previousGridIndex i)| ≤ B * midpointStep n i) →
      a * Real.log (2 * (n : ℝ)) ≤ 1 →
      let L := 1 + Real.log (2 * (n : ℝ))
      let v := fun i => whitenedIncrementFeature (h i) (previousGridHurst h i)
        (midpointLeft n i) (midpointStep n i)
      (∑ i, ∑ j, ((Matrix.gram ℝ v - 1) i j) ^ 2) ≤
        4 * n * (C * a * L) ^ 2 + 8 * (K * B * L) ^ 2 + 4 * (D * B) ^ 4 := by
  obtain ⟨C, hC, hc⟩ := midpointFrozen_matrix_uniform_bounds
  obtain ⟨K, hK, hk⟩ := midpoint_mixed_uniform_bound
  obtain ⟨D, hD, hd⟩ := midpoint_variation_uniform_energy_bound
  refine ⟨C, hC, K, hK, D, hD, ?_⟩
  intro n h a B hh ha hB hha hstep hsmall
  let U := fun i => frozenIncrementFeature (h i) (midpointLeft n i) (midpointStep n i)
  let V := fun i => hurstVariationFeature (h i) (previousGridHurst h i) (midpointLeft n i) (midpointStep n i)
  have hA := (hc n h a hh ha hha hsmall).1
  have hR := gram_frobenius_bound_of_energy V ((D * B) ^ 2) (hd n h B hh hB hstep)
  have hL : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have he := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
      linarith
  have hQ := matrix_frobenius_bound_of_entries (fun i j => ⟪U i, V j⟫)
    (K * B * (1 + Real.log (2 * (n : ℝ)))) (by positivity) (hk n h a B hh ha hB hha hstep hsmall)
  have he := gram_sum_frobenius_bound U V _ _ _ hA hQ hR
  dsimp only
  simp only [whitenedIncrementFeature_decomposition]
  convert! he using 1 <;> ring

theorem frobenius_components_rate (n a B L C K D : ℝ) (hn : 0 ≤ n) (hB : 0 ≤ B)
    (hB1 : B ≤ 1) (hL : 1 ≤ L) :
    4 * n * (C * a * L) ^ 2 + 8 * (K * B * L) ^ 2 + 4 * (D * B) ^ 4 ≤
      (4 * C ^ 2 + 8 * K ^ 2 + 4 * D ^ 4) * (n * a ^ 2 + B ^ 2) * L ^ 2 := by
  have hB2 : B ^ 2 ≤ 1 := by nlinarith
  have hB4 : B ^ 4 ≤ B ^ 2 := by nlinarith [sq_nonneg (B ^ 2), mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hB2)]
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hmass : 0 ≤ n * a ^ 2 := mul_nonneg hn (sq_nonneg _)
  have h1 : 4 * n * (C * a * L) ^ 2 ≤ 4 * C ^ 2 * (n * a ^ 2 + B ^ 2) * L ^ 2 := by
    have he := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4 * C ^ 2) (sq_nonneg B)) (sq_nonneg L)
    nlinarith
  have h2 : 8 * (K * B * L) ^ 2 ≤ 8 * K ^ 2 * (n * a ^ 2 + B ^ 2) * L ^ 2 := by
    have he := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 8 * K ^ 2) hmass) (sq_nonneg L)
    nlinarith
  have h3 : 4 * (D * B) ^ 4 ≤ 4 * D ^ 4 * (n * a ^ 2 + B ^ 2) * L ^ 2 := by
    have hb := mul_le_mul_of_nonneg_left hB4 (by positivity : 0 ≤ 4 * D ^ 4)
    have hl := mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ 4 * D ^ 4 * B ^ 2)
    have he := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4 * D ^ 4) hmass) (sq_nonneg L)
    nlinarith
  calc
    _ ≤ (4 * C ^ 2 * (n * a ^ 2 + B ^ 2) * L ^ 2 +
        8 * K ^ 2 * (n * a ^ 2 + B ^ 2) * L ^ 2) + 4 * D ^ 4 * (n * a ^ 2 + B ^ 2) * L ^ 2 :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- This is the actual-model Frobenius rate required by the p=1 repair. -/
theorem midpoint_whitened_frobenius_rate :
    ∃ C > 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ a B : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ a → 0 ≤ B → B ≤ 1 →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) →
      (∀ i, i.val ≠ 0 → |(h i : ℝ) - h (previousGridIndex i)| ≤ B * midpointStep n i) →
      a * Real.log (2 * (n : ℝ)) ≤ 1 →
      (∑ i, ∑ j, ((Matrix.gram ℝ (fun i => whitenedIncrementFeature (h i) (previousGridHurst h i)
        (midpointLeft n i) (midpointStep n i)) - 1) i j) ^ 2) ≤
        C * ((n : ℝ) * a ^ 2 + B ^ 2) * (1 + Real.log (2 * (n : ℝ))) ^ 2 := by
  obtain ⟨C, hC, K, hK, D, hD, hc⟩ := midpoint_whitened_frobenius_components
  refine ⟨4 * C ^ 2 + 8 * K ^ 2 + 4 * D ^ 4 + 1, by positivity, ?_⟩
  intro n h a B hh ha hB hB1 hha hstep hsmall
  have hL : 1 ≤ 1 + Real.log (2 * (n : ℝ)) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have he := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
      linarith
  have hb := hc n h a B hh ha hB hha hstep hsmall
  have hr := frobenius_components_rate n a B (1 + Real.log (2 * (n : ℝ))) C K D (Nat.cast_nonneg _) hB hB1 hL
  exact (hb.trans hr).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 4 * C ^ 2 + 8 * K ^ 2 + 4 * D ^ 4 ≤
      4 * C ^ 2 + 8 * K ^ 2 + 4 * D ^ 4 + 1) (by positivity)) (sq_nonneg _))

end Hurst
