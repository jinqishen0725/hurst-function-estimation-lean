import Mathlib.Data.Nat.Dist
import Mathlib.Topology.Algebra.Order.LiminfLimsup

noncomputable section
open Filter
namespace Hurst

/-- An eventual uniform bound on finite rows can be enlarged to cover the
finitely many initial rows. -/
theorem exists_uniform_finrow_bound_of_eventually
    (B : ∀ n, Fin n → ℝ) (hB0 : ∀ n i, 0 ≤ B n i)
    (hB : ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ i, B n i ≤ C) :
    ∃ D ≥ 0, ∀ n i, B n i ≤ D := by
  obtain ⟨C, hC, hCev⟩ := hB
  obtain ⟨N, hN⟩ := eventually_atTop.1 hCev
  let S : ℝ := ∑ n ∈ Finset.range N, ∑ i : Fin n, B n i
  refine ⟨C + S, add_nonneg hC ?_, ?_⟩
  · dsimp only [S]
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro i _
    exact hB0 k i
  · intro n i
    by_cases hn : N ≤ n
    · exact (hN n hn i).trans (le_add_of_nonneg_right (by
        dsimp only [S]
        apply Finset.sum_nonneg
        intro k _
        apply Finset.sum_nonneg
        intro j _
        exact hB0 k j))
    · have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
      have hi : B n i ≤ ∑ j : Fin n, B n j := by
        exact Finset.single_le_sum (fun j _ => hB0 n j) (Finset.mem_univ i)
      have hrow : (∑ j : Fin n, B n j) ≤ S := by
        dsimp only [S]
        exact Finset.single_le_sum
          (f := fun k : ℕ => ∑ j : Fin k, B k j)
          (fun k _ => Finset.sum_nonneg fun j _ => hB0 k j) hnmem
      exact (hi.trans hrow).trans (le_add_of_nonneg_left hC)

theorem cutoff_double_sum_mono
    (a : ∀ n, Fin n → Fin n → ℝ) (ha : ∀ n i j, 0 ≤ a n i j)
    {K L n : ℕ} (hKL : K ≤ L) :
    (∑ i : Fin n, ∑ j : Fin n,
      if L < Nat.dist i.val j.val then a n i j else 0) ≤
    ∑ i : Fin n, ∑ j : Fin n,
      if K < Nat.dist i.val j.val then a n i j else 0 := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hL : L < Nat.dist i.val j.val
  · rw [if_pos hL, if_pos (hKL.trans_lt hL)]
  · rw [if_neg hL]
    split_ifs
    · exact ha n i j
    · exact le_rfl

theorem cutoff_double_sum_eq_zero_of_row_le
    (a : ∀ n, Fin n → Fin n → ℝ) {K n : ℕ} (hnK : n ≤ K) :
    (∑ i : Fin n, ∑ j : Fin n,
      if K < Nat.dist i.val j.val then a n i j else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  apply Nat.not_lt_of_ge
  apply (show Nat.dist i.val j.val ≤ n by
    unfold Nat.dist
    omega).trans hnK

/-- The eventual epsilon-tail formulation implies the literal supremum over
all rows in B&S (3.2): enlarge the lag cutoff past the finite initial prefix. -/
theorem cutoff_average_tail_all_rows_of_eventually
    (p : ℕ) (r : ∀ n, Fin n → Fin n → ℝ)
    (htail : ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist i.val j.val then |r n i j| ^ p else 0) ≤ ε) :
    ∀ ε > 0, ∃ K : ℕ, ∀ n : ℕ,
      (n : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist i.val j.val then |r n i j| ^ p else 0) ≤ ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := htail ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hK
  refine ⟨max K N, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hsum := cutoff_double_sum_mono
      (fun n (i j : Fin n) => |r n i j| ^ p)
      (fun _ _ _ => pow_nonneg (abs_nonneg _) _)
      (K := K) (L := max K N) (n := n)
      (Nat.le_max_left K N : K ≤ max K N)
    have hmul := mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr (Nat.cast_nonneg n))
    exact hmul.trans (hN n hn)
  · have hnmax : n ≤ max K N := (Nat.le_of_lt (lt_of_not_ge hn)).trans
        (Nat.le_max_right K N)
    rw [cutoff_double_sum_eq_zero_of_row_le
      (fun n (i j : Fin n) => |r n i j| ^ p) hnmax, mul_zero]
    exact hε.le

end Hurst
