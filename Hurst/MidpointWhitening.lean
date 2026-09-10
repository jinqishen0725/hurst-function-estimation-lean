import Hurst.GridWhitening
import Hurst.Basic

/-! The actual midpoint grid and its correctly normalized Brownian reference law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set InformationTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def midpointStep (n : ℕ) (i : Fin n) : ℝ := if i.val = 0 then 1 / (2 * n) else 1 / n

def midpointLeft (n : ℕ) (i : Fin n) : ℝ :=
  if i.val = 0 then 0 else grid n (previousGridIndex i).val

theorem midpointStep_pos (n : ℕ) (i : Fin n) : 0 < midpointStep n i := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  unfold midpointStep
  split_ifs <;> positivity

theorem midpointStep_le (n : ℕ) (i : Fin n) : midpointStep n i ≤ 1 / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  unfold midpointStep
  split_ifs
  · exact div_le_div_of_nonneg_left (by norm_num) hn (by linarith)
  · exact le_rfl

theorem midpointStep_sum_le_one (n : ℕ) : (∑ i : Fin n, midpointStep n i) ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  calc
    _ ≤ ∑ _i : Fin n, (1 / (n : ℝ)) := Finset.sum_le_sum fun i _ => midpointStep_le n i
    _ = 1 := by simp [hnR]

theorem midpoint_grid_eq_left_add_step (n : ℕ) (i : Fin n) :
    grid n i.val = midpointLeft n i + midpointStep n i := by
  by_cases hi : i.val = 0
  · simp [midpointLeft, midpointStep, grid, hi]
    ring
  · have hc : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ i.val), Nat.cast_one]
    simp only [midpointLeft, midpointStep, if_neg hi, grid, previousGridIndex, hc]
    ring

theorem midpointLeft_bounds (n : ℕ) (i : Fin n) : 0 ≤ midpointLeft n i ∧ midpointLeft n i < 1 := by
  by_cases hi : i.val = 0
  · simp [midpointLeft, hi]
  · have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    have hg := grid_mem n (previousGridIndex i).val hn (previousGridIndex i).isLt
    simpa only [midpointLeft, if_neg hi] using And.intro hg.1.le hg.2

theorem midpoint_intervals_ordered (n : ℕ) (i j : Fin n) (hij : i < j) :
    grid n i.val ≤ midpointLeft n j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hj : j.val ≠ 0 := by have hi' : i.val < j.val := hij; omega
  have hi' : i.val ≤ j.val - 1 := by have h : i.val < j.val := hij; omega
  have hiR : (i.val : ℝ) ≤ ((j.val - 1 : ℕ) : ℝ) := by exact_mod_cast hi'
  simp only [midpointLeft, if_neg hj, grid, previousGridIndex]
  exact div_le_div_of_nonneg_right (by linarith) hn.le

def brownianHurst : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

theorem harmonizableFeature_zero (h : Ioo (0 : ℝ) 1) : harmonizableFeature h 0 = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [harmonizableFeature_norm_sq]
  simp only [abs_zero, Real.zero_rpow (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) h.property.1))]

theorem frozenBrownian_disjoint_inner (s t ℓ m : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hl : 0 < ℓ) (hm : 0 < m) (hst : s + ℓ ≤ t) :
    ⟪frozenIncrementFeature brownianHurst s ℓ, frozenIncrementFeature brownianHurst t m⟫ = 0 := by
  have hsl : 0 ≤ s + ℓ := by linarith
  have htm : 0 ≤ t + m := by linarith
  simp only [frozenIncrementFeature, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right]
  dsimp only [brownianHurst]
  rw [harmonizableFeature_brownian_inner _ _ hsl htm,
    harmonizableFeature_brownian_inner _ _ hsl ht,
    harmonizableFeature_brownian_inner _ _ hs htm,
    harmonizableFeature_brownian_inner _ _ hs ht]
  rw [min_eq_left (by linarith : s + ℓ ≤ t + m), min_eq_left hst,
    min_eq_left (by linarith : s ≤ t + m), min_eq_left (by linarith : s ≤ t)]
  ring

theorem midpointBrownian_gram (n : ℕ) :
    Matrix.gram ℝ (fun i : Fin n => frozenIncrementFeature brownianHurst (midpointLeft n i) (midpointStep n i)) = 1 := by
  ext i j
  change ⟪frozenIncrementFeature brownianHurst (midpointLeft n i) (midpointStep n i),
    frozenIncrementFeature brownianHurst (midpointLeft n j) (midpointStep n j)⟫ = _
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [frozenBrownian_disjoint_inner _ _ _ _ (midpointLeft_bounds n i).1 (midpointLeft_bounds n j).1
      (midpointStep_pos n i) (midpointStep_pos n j)
      (by rw [← midpoint_grid_eq_left_add_step]; exact midpoint_intervals_ordered n i j hij)]
    simp [ne_of_lt hij]
  · subst j
    rw [real_inner_self_eq_norm_sq, frozenIncrementFeature_norm_sq _ _ _ (midpointStep_pos n i)]
    norm_num [brownianHurst]
  · rw [real_inner_comm, frozenBrownian_disjoint_inner _ _ _ _ (midpointLeft_bounds n j).1
      (midpointLeft_bounds n i).1 (midpointStep_pos n j) (midpointStep_pos n i)
      (by rw [← midpoint_grid_eq_left_add_step]; exact midpoint_intervals_ordered n j i hij)]
    simp [ne_of_gt hij]

theorem midpointBrownian_transformed_feature (n : ℕ) (i : Fin n) :
    (Real.sqrt (midpointStep n i))⁻¹ •
      (harmonizableFeature brownianHurst (grid n i.val) - if i.val = 0 then 0 else
        harmonizableFeature brownianHurst (grid n (previousGridIndex i).val)) =
      frozenIncrementFeature brownianHurst (midpointLeft n i) (midpointStep n i) := by
  unfold frozenIncrementFeature
  rw [← midpoint_grid_eq_left_add_step]
  by_cases hi : i.val = 0
  · simp [midpointLeft, hi, harmonizableFeature_zero]
  · simp [midpointLeft, hi]

/-- The KL comparison is now on the actual midpoint observations and the unit Gaussian reference. -/
theorem harmonizableGaussian_midpoint_klDiv_whitening (n : ℕ) (h : Fin n → Ioo (0 : ℝ) 1) :
    klDiv (harmonizableGaussian h (fun i => grid n i.val))
      (harmonizableGaussian (fun _ => brownianHurst) (fun i => grid n i.val)) =
      klDiv (featureGaussian (fun i => (Real.sqrt (midpointStep n i))⁻¹ •
        (harmonizableFeature (h i) (grid n i.val) - if i.val = 0 then 0 else
          harmonizableFeature (h (previousGridIndex i)) (grid n (previousGridIndex i).val))))
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have he := featureGaussian_klDiv_differenceWhitening
    (fun i : Fin n => harmonizableFeature (h i) (grid n i.val))
    (fun i : Fin n => harmonizableFeature brownianHurst (grid n i.val))
    (midpointStep n) (midpointStep_pos n)
  simp_rw [midpointBrownian_transformed_feature] at he
  dsimp only [featureGaussian] at he
  rw [midpointBrownian_gram] at he
  exact he.symm

def previousGridHurst {n : ℕ} (h : Fin n → Ioo (0 : ℝ) 1) (i : Fin n) : Ioo (0 : ℝ) 1 :=
  if i.val = 0 then h i else h (previousGridIndex i)

theorem midpoint_whitened_feature_eq (n : ℕ) (h : Fin n → Ioo (0 : ℝ) 1) (i : Fin n) :
    (Real.sqrt (midpointStep n i))⁻¹ •
      (harmonizableFeature (h i) (grid n i.val) - if i.val = 0 then 0 else
        harmonizableFeature (h (previousGridIndex i)) (grid n (previousGridIndex i).val)) =
      whitenedIncrementFeature (h i) (previousGridHurst h i) (midpointLeft n i) (midpointStep n i) := by
  unfold whitenedIncrementFeature
  rw [← midpoint_grid_eq_left_add_step]
  by_cases hi : i.val = 0
  · simp [previousGridHurst, midpointLeft, hi, harmonizableFeature_zero]
  · simp [previousGridHurst, midpointLeft, hi]

theorem harmonizableGaussian_midpoint_klDiv_decomposition (n : ℕ) (h : Fin n → Ioo (0 : ℝ) 1) :
    klDiv (harmonizableGaussian h (fun i => grid n i.val))
      (harmonizableGaussian (fun _ => brownianHurst) (fun i => grid n i.val)) =
      klDiv (featureGaussian (fun i =>
        frozenIncrementFeature (h i) (midpointLeft n i) (midpointStep n i) +
        hurstVariationFeature (h i) (previousGridHurst h i) (midpointLeft n i) (midpointStep n i)))
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  rw [harmonizableGaussian_midpoint_klDiv_whitening]
  simp_rw [midpoint_whitened_feature_eq, whitenedIncrementFeature_decomposition]

/-- Uniform actual midpoint-grid control with no evaluation of H at the unobserved origin. -/
theorem midpoint_variation_uniform_operator_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ B : ℝ, 0 ≤ B →
      (∀ i, (h i : ℝ) ∈ Icc a b) →
      (∀ i, i.val ≠ 0 → |(h i : ℝ) - h (previousGridIndex i)| ≤ B * midpointStep n i) →
      ∀ w : EuclideanSpace ℝ (Fin n),
        ‖∑ i, w i • hurstVariationFeature (h i) (previousGridHurst h i)
          (midpointLeft n i) (midpointStep n i)‖ ≤ (C * B) * ‖w‖ := by
  obtain ⟨C, hC, hOp⟩ := hurstVariationFeature_uniform_operator_bound a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro n h B hB hh hstep w
  apply hOp n h (previousGridHurst h) (midpointLeft n) (midpointStep n) B hB hh
  · intro i
    unfold previousGridHurst
    split_ifs <;> apply hh
  · intro i
    rw [abs_of_nonneg (midpointLeft_bounds n i).1]
    exact (midpointLeft_bounds n i).2.le
  · exact midpointStep_pos n
  · exact midpointStep_sum_le_one n
  · intro i
    by_cases hi : i.val = 0
    · simp only [previousGridHurst, if_pos hi, sub_self, abs_zero]
      exact mul_nonneg hB (midpointStep_pos n i).le
    · simpa only [previousGridHurst, if_neg hi] using hstep i hi

end Hurst
