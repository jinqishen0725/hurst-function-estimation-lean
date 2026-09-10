import Hurst.TruncatedVarianceTail
import Hurst.LagVarianceLimit

noncomputable section
namespace Hurst

theorem fin_zeroExtended_lag_sum_eq_range
    (m k : ℕ) (F : Fin m → Fin m → ℝ) :
    (∑ i : Fin m, if h : i.val + k < m then
      F i ⟨i.val + k, h⟩ else 0) =
      ∑ i : Fin (m - k),
        F ⟨i.val, (i.isLt.trans_le (Nat.sub_le m k))⟩
          ⟨i.val + k, Nat.lt_sub_iff_add_lt.mp i.isLt⟩ := by
  let G : ℕ → ℝ := fun i => if hi : i < m then
    if hik : i + k < m then F ⟨i, hi⟩ ⟨i + k, hik⟩ else 0 else 0
  have hleft : (∑ i : Fin m, if h : i.val + k < m then
      F i ⟨i.val + k, h⟩ else 0) = ∑ i ∈ Finset.range m, G i := by
    rw [← Fin.sum_univ_eq_sum_range G m]
    apply Finset.sum_congr rfl
    intro i _
    simp only [G, i.isLt, dite_true]
  have hright : (∑ i : Fin (m - k),
      F ⟨i.val, (i.isLt.trans_le (Nat.sub_le m k))⟩
        ⟨i.val + k, Nat.lt_sub_iff_add_lt.mp i.isLt⟩) =
      ∑ i ∈ Finset.range (m - k), G i := by
    rw [← Fin.sum_univ_eq_sum_range G (m - k)]
    apply Finset.sum_congr rfl
    intro i _
    have him : i.val < m := i.isLt.trans_le (Nat.sub_le m k)
    have hik : i.val + k < m := Nat.lt_sub_iff_add_lt.mp i.isLt
    simp only [G, him, hik, dite_true]
  rw [hleft, hright]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i him hi
    simp only [Finset.mem_range] at him hi
    have hik : ¬ i + k < m := by omega
    simp [G, him, hik]

theorem symmetricLagTerm_distance_lt
    (m R : ℕ) (F : ℕ → ℕ → ℝ) (k : ℕ) :
    symmetricLagTerm m
      (fun i j => if Nat.dist i j < R then F i j else 0) k =
      if k < R then symmetricLagTerm m F k else 0 := by
  by_cases hk0 : k = 0
  · subst k
    simp [symmetricLagTerm]
  · simp only [symmetricLagTerm, hk0, if_false]
    by_cases hkR : k < R
    · simp only [hkR, if_true]
      apply congrArg (fun x : ℝ => 2 * x)
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i + k < m := by
        simp only [Finset.mem_range] at hi
        omega
      rw [Nat.dist_eq_sub_of_le (Nat.le_add_right i k)]
      simp only [Nat.add_sub_cancel_left, hkR, if_true]
    · simp only [hkR, if_false, mul_eq_zero]
      right
      apply Finset.sum_eq_zero
      intro i hi
      rw [Nat.dist_eq_sub_of_le (Nat.le_add_right i k)]
      simp [hkR]

theorem finite_symmetric_distance_lt_sum_eq_lags
    (m R : ℕ) (F : ℕ → ℕ → ℝ)
    (hsym : ∀ i j, i < m → j < m → F i j = F j i) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      if Nat.dist i j < R then F i j else 0) =
      ∑ k ∈ Finset.range (min R m), symmetricLagTerm m F k := by
  have hsym' : ∀ i j, i < m → j < m →
      (if Nat.dist i j < R then F i j else 0) =
      (if Nat.dist j i < R then F j i else 0) := by
    intro i j hi hj
    rw [Nat.dist_comm]
    by_cases h : Nat.dist j i < R <;> simp [h, hsym i j hi hj]
  rw [finite_symmetric_double_sum_eq_lags m
    (fun i j => if Nat.dist i j < R then F i j else 0) hsym']
  simp_rw [symmetricLagTerm_distance_lt]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

end Hurst
