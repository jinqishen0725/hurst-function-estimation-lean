import Hurst.FrozenEstimates
import Hurst.GaussianKLBound
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem reciprocal_range_sum_eq_harmonic (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (k : ℝ)⁻¹) = (harmonic n : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, inv_zero, add_zero, harmonic, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one]

theorem reciprocal_grid_distance_sum_bound (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, |(j.val : ℝ) - i.val|⁻¹) ≤ 2 * (1 + Real.log n) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≤ i)
  let T : Finset (Fin n) := Finset.univ.filter (fun j => ¬j ≤ i)
  have hl : (∑ j ∈ S, |(j.val : ℝ) - i.val|⁻¹) ≤ (harmonic n : ℝ) := by
    have he : (∑ j ∈ S, |(j.val : ℝ) - i.val|⁻¹) =
        ∑ k ∈ S.image (fun j => i.val - j.val), (k : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        have hj' : j.val ≤ i.val := (Finset.mem_filter.mp hj).2
        rw [Nat.cast_sub hj', abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hj'))]
      · intro j hj k hk he
        apply Fin.ext
        dsimp only at he
        have hj' : j.val ≤ i.val := (Finset.mem_filter.mp hj).2
        have hk' : k.val ≤ i.val := (Finset.mem_filter.mp hk).2
        omega
    rw [he, ← reciprocal_range_sum_eq_harmonic]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro k _ _
      positivity
  have hr : (∑ j ∈ T, |(j.val : ℝ) - i.val|⁻¹) ≤ (harmonic n : ℝ) := by
    have he : (∑ j ∈ T, |(j.val : ℝ) - i.val|⁻¹) =
        ∑ k ∈ T.image (fun j => j.val - i.val), (k : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        have hj' : i.val ≤ j.val := by have hh := (Finset.mem_filter.mp hj).2; exact le_of_lt (lt_of_not_ge hh)
        rw [Nat.cast_sub hj', abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hj'))]
      · intro j hj k hk he
        apply Fin.ext
        dsimp only at he
        have hj' : i.val < j.val := lt_of_not_ge (Finset.mem_filter.mp hj).2
        have hk' : i.val < k.val := lt_of_not_ge (Finset.mem_filter.mp hk).2
        omega
    rw [he, ← reciprocal_range_sum_eq_harmonic]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro k _ _
      positivity
  have he : (∑ j : Fin n, |(j.val : ℝ) - i.val|⁻¹) =
      (∑ j ∈ S, |(j.val : ℝ) - i.val|⁻¹) + (∑ j ∈ T, |(j.val : ℝ) - i.val|⁻¹) := by
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [he]
  have hh := harmonic_le_one_add_log n
  linarith

theorem matrix_frobenius_bound_of_row_bound {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (R : ℝ) (_hR : 0 ≤ R) (hrow : ∀ i, (∑ j, |E i j|) ≤ R) :
    (∑ i, ∑ j, (E i j) ^ 2) ≤ n * R ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin n, R ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun j => |E i j|) (fun j _ => abs_nonneg (E i j))
      simp only [sq_abs] at hs
      exact hs.trans (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => abs_nonneg _)) (hrow i) 2)
    _ = _ := by simp

theorem matrix_quadratic_bound_of_row_bound {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ i j, E i j = E j i) (R : ℝ) (hrow : ∀ i, (∑ j, |E i j|) ≤ R)
    (w : Fin n → ℝ) :
    |∑ i, ∑ j, E i j * w i * w j| ≤ R * ∑ i, (w i) ^ 2 := by
  have htri : |∑ i, ∑ j, E i j * w i * w j| ≤ ∑ i, ∑ j, |E i j * w i * w j| := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  have hterm : ∀ i j, 2 * |E i j * w i * w j| ≤ |E i j| * ((w i) ^ 2 + (w j) ^ 2) := by
    intro i j
    rw [abs_mul, abs_mul]
    have hsq := sq_nonneg (|w i| - |w j|)
    rw [sub_sq, sq_abs, sq_abs] at hsq
    have hm := mul_le_mul_of_nonneg_left (show 2 * |w i| * |w j| ≤ (w i) ^ 2 + (w j) ^ 2 by linarith)
      (abs_nonneg (E i j))
    nlinarith
  have hsum : 2 * (∑ i, ∑ j, |E i j * w i * w j|) ≤
      ∑ i, ∑ j, |E i j| * ((w i) ^ 2 + (w j) ^ 2) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
  have hleft : (∑ i, ∑ j, |E i j| * (w i) ^ 2) ≤ R * ∑ i, (w i) ^ 2 := by
    simp only [← Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  have hright : (∑ i, ∑ j, |E i j| * (w j) ^ 2) ≤ R * ∑ i, (w i) ^ 2 := by
    rw [Finset.sum_comm]
    simpa only [hE] using hleft
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  linarith

/-- Summing the actual frozen-covariance entries, with a constant independent of n and H. -/
theorem midpointFrozen_row_uniform_bound :
    ∃ C ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ a : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ a →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) → a * Real.log (2 * (n : ℝ)) ≤ 1 →
      ∀ i, (∑ j, |(Matrix.gram ℝ (fun k => frozenIncrementFeature (h k)
        (midpointLeft n k) (midpointStep n k)) - 1) i j|) ≤
        C * a * (1 + Real.log (2 * (n : ℝ))) := by
  classical
  obtain ⟨K, hK, hoff⟩ := midpointFrozen_offdiagonal_uniform_bound
  refine ⟨2 * Real.exp 2 + 2 * K, by positivity, ?_⟩
  intro n h a hh ha hha hsmall i
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  let E := Matrix.gram ℝ (fun k => frozenIncrementFeature (h k) (midpointLeft n k) (midpointStep n k)) - 1
  have he : ∀ j, |E i j| ≤ (if i = j then (2 * Real.exp 2) * a * Real.log (2 * n) else 0) +
      K * a * |(j.val : ℝ) - i.val|⁻¹ := by
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [E, Matrix.sub_apply, Matrix.gram_apply, Matrix.one_apply_eq,
        real_inner_self_eq_norm_sq, if_true, sub_self, abs_zero, inv_zero, mul_zero, add_zero] using
        midpointFrozen_diagonal_bound n i (h i) a ha (hha i) hsmall
    · simpa only [E, Matrix.sub_apply, Matrix.gram_apply, Matrix.one_apply_ne hij,
        sub_zero, if_neg hij, zero_add, div_eq_mul_inv] using
        hoff n i j (h i) (h j) a hij (hh i) (hh j) ha (hha i) (hha j) hsmall
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he j)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.mul_sum] at hs
  have hr := mul_le_mul_of_nonneg_left (reciprocal_grid_distance_sum_bound n i)
    (show 0 ≤ K * a by positivity)
  have hl : Real.log n ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hn (by linarith)
  have hl' := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * K * a by positivity)
  have hda : 0 ≤ 2 * Real.exp 2 * a := by positivity
  change (∑ j, |E i j|) ≤ _
  nlinarith

theorem gram_quadratic_error {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Fin n → E) (w : Fin n → ℝ) :
    (∑ i, ∑ j, (Matrix.gram ℝ v - 1) i j * w i * w j) =
      ‖∑ i, w i • v i‖ ^ 2 - ∑ i, (w i) ^ 2 := by
  have hgram : (∑ i, ∑ j, Matrix.gram ℝ v i j * w i * w j) = ‖∑ i, w i • v i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Matrix.gram_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (v j) (v i)]
    ring
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hgram]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.one_apply, ite_mul, pow_two]

theorem featureCombination_energy_bound_of_gram_rows {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin n → E) (R : ℝ)
    (hrow : ∀ i, (∑ j, |(Matrix.gram ℝ v - 1) i j|) ≤ R)
    (w : EuclideanSpace ℝ (Fin n)) :
    |‖∑ i, w i • v i‖ ^ 2 - ‖w‖ ^ 2| ≤ R * ‖w‖ ^ 2 := by
  have hsym : ∀ i j, (Matrix.gram ℝ v - 1) i j = (Matrix.gram ℝ v - 1) j i := by
    intro i j
    have he := ((Matrix.isHermitian_gram ℝ v).sub Matrix.isHermitian_one).apply j i
    simpa using he
  have he := matrix_quadratic_bound_of_row_bound (Matrix.gram ℝ v - 1) hsym R hrow w
  rw [gram_quadratic_error, ← EuclideanSpace.real_norm_sq_eq] at he
  exact he

/-- Both matrix estimates now apply to the actual frozen midpoint features. -/
theorem midpointFrozen_matrix_uniform_bounds :
    ∃ C ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ a : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ a →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) → a * Real.log (2 * (n : ℝ)) ≤ 1 →
      let R := C * a * (1 + Real.log (2 * (n : ℝ)))
      let v := fun i => frozenIncrementFeature (h i) (midpointLeft n i) (midpointStep n i)
      (∑ i, ∑ j, ((Matrix.gram ℝ v - 1) i j) ^ 2) ≤ n * R ^ 2 ∧
        ∀ w : EuclideanSpace ℝ (Fin n), |‖∑ i, w i • v i‖ ^ 2 - ‖w‖ ^ 2| ≤ R * ‖w‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := midpointFrozen_row_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro n h a hh ha hha hsmall
  have hL : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have he := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
      linarith
  constructor
  · exact matrix_frobenius_bound_of_row_bound _ _ (by positivity) (hc n h a hh ha hha hsmall)
  · exact featureCombination_energy_bound_of_gram_rows _ _ (hc n h a hh ha hha hsmall)

/-- A quantitative lower bound on frozen linear combinations, ready for the variation perturbation. -/
theorem midpointFrozen_uniform_lower_bound :
    ∃ C ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ a : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ a →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) → a * Real.log (2 * (n : ℝ)) ≤ 1 →
      C * a * (1 + Real.log (2 * (n : ℝ))) ≤ 7 / 16 →
      ∀ w : EuclideanSpace ℝ (Fin n), (3 / 4 : ℝ) * ‖w‖ ≤
        ‖∑ i, w i • frozenIncrementFeature (h i) (midpointLeft n i) (midpointStep n i)‖ := by
  obtain ⟨C, hC, hc⟩ := midpointFrozen_matrix_uniform_bounds
  refine ⟨C, hC, ?_⟩
  intro n h a hh ha hha hsmall hR w
  have he := (hc n h a hh ha hha hsmall).2 w
  have hb := (abs_le.mp he).1
  have hm := mul_le_mul_of_nonneg_right hR (sq_nonneg ‖w‖)
  have hv := norm_nonneg (∑ i, w i • frozenIncrementFeature (h i) (midpointLeft n i) (midpointStep n i))
  have hw := norm_nonneg w
  dsimp only at hb
  nlinarith

theorem gram_posDef_of_energy_floor {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Fin n → E) (m : ℝ) (hm : 0 < m)
    (hfloor : ∀ w : EuclideanSpace ℝ (Fin n), m * ‖w‖ ^ 2 ≤ ‖∑ i, w i • v i‖ ^ 2) :
    (Matrix.gram ℝ v).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_gram ℝ v)
  intro x hx
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hw : w ≠ 0 := by
    intro he
    apply hx
    exact congrArg WithLp.ofLp he
  rw [Matrix.star_dotProduct_gram_mulVec, real_inner_self_eq_norm_sq]
  exact (mul_pos hm (sq_pos_of_pos (norm_pos_iff.mpr hw))).trans_le (hfloor w)

theorem gram_eigenvalue_floor_of_energy_floor {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Fin n → E) (m : ℝ)
    (hfloor : ∀ w : EuclideanSpace ℝ (Fin n), m * ‖w‖ ^ 2 ≤ ‖∑ i, w i • v i‖ ^ 2) :
    ∀ i, m ≤ (Matrix.isHermitian_gram ℝ v).eigenvalues i := by
  intro i
  let hA := Matrix.isHermitian_gram ℝ v
  let w := hA.eigenvectorBasis i
  have hw : ‖w‖ = 1 := hA.eigenvectorBasis.orthonormal.norm_eq_one i
  have hdot : star (fun j => w j) ⬝ᵥ (fun j => w j) = 1 := by
    change star (WithLp.ofLp w) ⬝ᵥ WithLp.ofLp w = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, real_inner_self_eq_norm_sq, hw]
    norm_num
  have he : ‖∑ j, w j • v j‖ ^ 2 = hA.eigenvalues i := by
    rw [← real_inner_self_eq_norm_sq, ← Matrix.star_dotProduct_gram_mulVec]
    change star (fun j => w j) ⬝ᵥ (Matrix.mulVec (Matrix.gram ℝ v) (fun j => w j)) = _
    rw [hA.mulVec_eigenvectorBasis, dotProduct_smul, hdot]
    simp
  have hf := hfloor w
  rw [hw, he] at hf
  simpa using hf

/-- The actual full whitened covariance is uniformly positive once the proved U and V bounds are small. -/
theorem midpoint_whitened_gram_uniform_floor :
    ∃ C ≥ 0, ∃ D ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ a B : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ a → 0 ≤ B →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) →
      (∀ i, i.val ≠ 0 → |(h i : ℝ) - h (previousGridIndex i)| ≤ B * midpointStep n i) →
      a * Real.log (2 * (n : ℝ)) ≤ 1 →
      C * a * (1 + Real.log (2 * (n : ℝ))) ≤ 7 / 16 → D * B ≤ 1 / 4 →
      let v := fun i => whitenedIncrementFeature (h i) (previousGridHurst h i)
        (midpointLeft n i) (midpointStep n i)
      (Matrix.gram ℝ v).PosDef ∧ ∀ i, (1 / 4 : ℝ) ≤ (Matrix.isHermitian_gram ℝ v).eigenvalues i := by
  obtain ⟨C, hC, hU⟩ := midpointFrozen_uniform_lower_bound
  obtain ⟨D, hD, hV⟩ := midpoint_variation_uniform_operator_bound (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, D, hD, ?_⟩
  intro n h a B hh ha hB hha hstep hsmall hCa hDB
  have hfloor : ∀ w : EuclideanSpace ℝ (Fin n), (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤
      ‖∑ i, w i • whitenedIncrementFeature (h i) (previousGridHurst h i)
        (midpointLeft n i) (midpointStep n i)‖ ^ 2 := by
    intro w
    have hu := hU n h a hh ha hha hsmall hCa w
    have hv := (hV n h B hB hh hstep w).trans (mul_le_mul_of_nonneg_right hDB (norm_nonneg _))
    have he := featureGaussian_perturb_variance_lower
      (fun i => frozenIncrementFeature (h i) (midpointLeft n i) (midpointStep n i))
      (fun i => hurstVariationFeature (h i) (previousGridHurst h i) (midpointLeft n i) (midpointStep n i)) w hu hv
    rw [featureGaussian_linear_variance] at he
    simpa only [whitenedIncrementFeature_decomposition] using he
  exact ⟨gram_posDef_of_energy_floor _ (1 / 4) (by norm_num) hfloor,
    gram_eigenvalue_floor_of_energy_floor _ (1 / 4) hfloor⟩

end Hurst
