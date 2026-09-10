import Hurst.FiniteLagReindex

noncomputable section
namespace Hurst

/-- Symmetric contribution of a nonnegative lag to a finite matrix indexed by
`Fin m`.  The shifted row is indexed by `Fin (m-k)`, so out-of-range terms are
absent by construction. -/
def finSymmetricLagTerm (m : ℕ) (F : Fin m → Fin m → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then ∑ i, F i i
  else 2 * ∑ i : Fin (m - k),
    F ⟨i.val, i.isLt.trans_le (Nat.sub_le m k)⟩
      ⟨i.val + k, Nat.lt_sub_iff_add_lt.mp i.isLt⟩

@[simp]
theorem finSymmetricLagTerm_eq_zero_of_le
    (m : ℕ) (F : Fin m → Fin m → ℝ) (k : ℕ) (hk : m ≤ k) :
    finSymmetricLagTerm m F k = 0 := by
  by_cases hk0 : k = 0
  · subst k
    have hm : m = 0 := by omega
    subst m
    unfold finSymmetricLagTerm
    simp only [if_pos]
    apply Finset.sum_eq_zero
    intro i _
    exact Fin.elim0 i
  · have hmk : m - k = 0 := Nat.sub_eq_zero_of_le hk
    unfold finSymmetricLagTerm
    simp only [hk0, if_false, mul_eq_zero]
    right
    apply Finset.sum_eq_zero
    intro i _
    exact Fin.elim0 (hmk ▸ i)

/-- Reindex a symmetric finite matrix exactly by its nonnegative lags. -/
theorem fin_symmetric_double_sum_eq_lags
    (m : ℕ) (F : Fin m → Fin m → ℝ)
    (hsym : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) =
      ∑ k ∈ Finset.range m, finSymmetricLagTerm m F k := by
  let G : ℕ → ℕ → ℝ := fun i j =>
    if hi : i < m then if hj : j < m then F ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0
  have hGsym : ∀ i j, i < m → j < m → G i j = G j i := by
    intro i j hi hj
    simp only [G, hi, hj, dite_true]
    exact hsym _ _
  have hdouble : (∑ i, ∑ j, F i j) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, G i j := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => ∑ j ∈ Finset.range m, G i j) m]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Fin.sum_univ_eq_sum_range (fun j => G i.val j) m]
    apply Finset.sum_congr rfl
    intro j _
    simp [G, i.isLt, j.isLt]
  rw [hdouble, finite_symmetric_double_sum_eq_lags m G hGsym]
  apply Finset.sum_congr rfl
  intro k _
  unfold finSymmetricLagTerm symmetricLagTerm
  by_cases hk0 : k = 0
  · subst k
    simp only [if_pos, G]
    rw [← Fin.sum_univ_eq_sum_range (fun i => G i i) m]
    apply Finset.sum_congr rfl
    intro i _
    simp [G, i.isLt]
  · simp only [hk0, if_false]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => G i (i + k)) (m - k)]
    apply Finset.sum_congr rfl
    intro i _
    have him : i.val < m := i.isLt.trans_le (Nat.sub_le m k)
    have hik : i.val + k < m := Nat.lt_sub_iff_add_lt.mp i.isLt
    simp [G, him, hik]

/-- The sum of finite lag contributions below a cutoff is exactly the matrix
sum over pairs whose index distance is below that cutoff. -/
theorem fin_symmetric_distance_lt_sum_eq_lags
    (m R : ℕ) (F : Fin m → Fin m → ℝ)
    (hsym : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, if Nat.dist i.val j.val < R then F i j else 0) =
      ∑ k ∈ Finset.range R, finSymmetricLagTerm m F k := by
  let G : Fin m → Fin m → ℝ := fun i j =>
    if Nat.dist i.val j.val < R then F i j else 0
  have hGsym : ∀ i j, G i j = G j i := by
    intro i j
    dsimp only [G]
    rw [Nat.dist_comm]
    by_cases h : Nat.dist j.val i.val < R <;> simp [h, hsym]
  rw [fin_symmetric_double_sum_eq_lags m G hGsym]
  have hterm (k : ℕ) : finSymmetricLagTerm m G k =
      if k < R then finSymmetricLagTerm m F k else 0 := by
    unfold finSymmetricLagTerm
    by_cases hk0 : k = 0
    · subst k
      by_cases hR : 0 < R
      · simp [G, hR]
      · have : R = 0 := by omega
        simp only [if_neg hR, G]
        apply Finset.sum_eq_zero
        intro i _
        simp [this]
    · simp only [hk0, if_false]
      by_cases hkR : k < R
      · simp only [hkR, if_true]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have hd : Nat.dist i.val (i.val + k) = k := by
          rw [Nat.dist_eq_sub_of_le (Nat.le_add_right i.val k)]
          exact Nat.add_sub_cancel_left i.val k
        simp [G, hd, hkR]
      · simp only [hkR, if_false, mul_eq_zero]
        right
        apply Finset.sum_eq_zero
        intro i _
        have hd : Nat.dist i.val (i.val + k) = k := by
          rw [Nat.dist_eq_sub_of_le (Nat.le_add_right i.val k)]
          exact Nat.add_sub_cancel_left i.val k
        simp [G, hd, hkR]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range m).filter (fun k => k < R) =
      Finset.range (min R m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hkR hkmin
    simp only [Finset.mem_range] at hkR hkmin
    apply finSymmetricLagTerm_eq_zero_of_le
    omega

/-- A correlation matrix evaluated at a nonnegative lag and extended by zero
when the shifted index leaves the finite row. -/
def finZeroExtendedLagCorrelation
    (m k : ℕ) (corr : Fin m → Fin m → ℝ) (i : Fin m) : ℝ :=
  if h : i.val + k < m then corr i ⟨i.val + k, h⟩ else 0

/-- The zero-extended weighted lag sum is the upper-triangular part of the
corresponding finite matrix. -/
theorem fin_weighted_zeroExtended_lag_sum_eq_range
    (m k : ℕ) (w : Fin m → ℝ) (corr : Fin m → Fin m → ℝ)
    (C : ℝ → ℝ) :
    (∑ i, w i * finZeroExtendedShift k w i *
      C (finZeroExtendedLagCorrelation m k corr i)) =
      ∑ i : Fin (m - k),
        w ⟨i.val, i.isLt.trans_le (Nat.sub_le m k)⟩ *
          w ⟨i.val + k, Nat.lt_sub_iff_add_lt.mp i.isLt⟩ *
          C (corr ⟨i.val, i.isLt.trans_le (Nat.sub_le m k)⟩
            ⟨i.val + k, Nat.lt_sub_iff_add_lt.mp i.isLt⟩) := by
  let F : Fin m → Fin m → ℝ := fun i j => w i * w j * C (corr i j)
  rw [← fin_zeroExtended_lag_sum_eq_range m k F]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hik : i.val + k < m
  · simp [finZeroExtendedShift, finZeroExtendedLagCorrelation, hik, F]
  · simp [finZeroExtendedShift, finZeroExtendedLagCorrelation, hik]

/-- Exact finite-cutoff junction between the distance-filtered covariance
matrix and the zero-extended lag sums used by the fixed-lag limit theorems. -/
theorem fin_weighted_distance_lt_sum_eq_zeroExtended_lags
    (m R : ℕ) (w : Fin m → ℝ) (corr : Fin m → Fin m → ℝ)
    (C : ℝ → ℝ) (hsym : ∀ i j, C (corr i j) = C (corr j i)) :
    (∑ i, ∑ j, if Nat.dist i.val j.val < R then
      w i * w j * C (corr i j) else 0) =
      ∑ k ∈ Finset.range R, (if k = 0 then 1 else 2) *
        (∑ i, w i * finZeroExtendedShift k w i *
          C (finZeroExtendedLagCorrelation m k corr i)) := by
  let F : Fin m → Fin m → ℝ := fun i j => w i * w j * C (corr i j)
  have hFsym : ∀ i j, F i j = F j i := by
    intro i j
    dsimp only [F]
    rw [hsym]
    ring
  rw [fin_symmetric_distance_lt_sum_eq_lags m R F hFsym]
  apply Finset.sum_congr rfl
  intro k _
  rw [fin_weighted_zeroExtended_lag_sum_eq_range m k w corr C]
  unfold finSymmetricLagTerm
  by_cases hk : k = 0
  · subst k
    simp only [if_pos, Nat.sub_zero, one_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [F]
    congr 3 <;> apply Fin.ext <;> simp
  · simp only [hk, if_false]
    congr 1

end Hurst
