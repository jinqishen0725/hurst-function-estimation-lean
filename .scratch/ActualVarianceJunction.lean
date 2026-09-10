import Hurst.FiniteLagReindex
import Hurst.ActualFirstTruncatedVarianceLimit
import Hurst.ActualSecondTruncatedVarianceLimit

noncomputable section
namespace Hurst

def finSymmetricLagTerm (m : ℕ) (F : Fin m → Fin m → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then ∑ i, F i i
  else 2 * ∑ i : Fin (m - k),
    F ⟨i.val, i.isLt.trans_le (Nat.sub_le m k)⟩
      ⟨i.val + k, Nat.lt_sub_iff_add_lt.mp i.isLt⟩

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
    intro i hi
    rw [← Fin.sum_univ_eq_sum_range (fun j => G i.val j) m]
    apply Finset.sum_congr rfl
    intro j hj
    simp [G, i.isLt, j.isLt]
  rw [hdouble, finite_symmetric_double_sum_eq_lags m G hGsym]
  apply Finset.sum_congr rfl
  intro k hk
  unfold finSymmetricLagTerm symmetricLagTerm
  by_cases hk0 : k = 0
  · subst k
    simp only [if_pos, G]
    rw [← Fin.sum_univ_eq_sum_range (fun i => G i i) m]
    apply Finset.sum_congr rfl
    intro i hi
    simp [G, i.isLt]
  · simp only [hk0, if_false]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => G i (i + k)) (m - k)]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i.val < m := i.isLt.trans_le (Nat.sub_le m k)
    have hik : i.val + k < m := Nat.lt_sub_iff_add_lt.mp i.isLt
    simp [G, him, hik]

end Hurst
