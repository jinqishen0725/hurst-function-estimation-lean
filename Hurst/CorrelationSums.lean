import Hurst.MatrixEstimates
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Dist

noncomputable section
open Set
namespace Hurst

theorem grid_distance_sum_le_tsum (f : ℕ → ℝ) (hf : Summable f) (hf0 : ∀ k, 0 ≤ f k)
    (n : ℕ) (i : Fin n) : (∑ j : Fin n, f (Nat.dist j.val i.val)) ≤ 2 * ∑' k, f k := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≤ i)
  let T : Finset (Fin n) := Finset.univ.filter (fun j => ¬j ≤ i)
  have hl : (∑ j ∈ S, f (Nat.dist j.val i.val)) ≤ ∑' k, f k := by
    have he : (∑ j ∈ S, f (Nat.dist j.val i.val)) = ∑ k ∈ S.image (fun j => i.val - j.val), f k := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.dist_eq_sub_of_le (show j.val ≤ i.val from (Finset.mem_filter.mp hj).2)]
      · intro j hj k hk he
        apply Fin.ext
        have hj' : j.val ≤ i.val := (Finset.mem_filter.mp hj).2
        have hk' : k.val ≤ i.val := (Finset.mem_filter.mp hk).2
        dsimp only at he
        omega
    rw [he]
    exact hf.sum_le_tsum _ (fun k _ => hf0 k)
  have hr : (∑ j ∈ T, f (Nat.dist j.val i.val)) ≤ ∑' k, f k := by
    have he : (∑ j ∈ T, f (Nat.dist j.val i.val)) = ∑ k ∈ T.image (fun j => j.val - i.val), f k := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        have hj' : i.val ≤ j.val := le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hj).2)
        rw [Nat.dist_eq_sub_of_le_right hj']
      · intro j hj k hk he
        apply Fin.ext
        have hj' : i.val < j.val := lt_of_not_ge (Finset.mem_filter.mp hj).2
        have hk' : i.val < k.val := lt_of_not_ge (Finset.mem_filter.mp hk).2
        dsimp only at he
        omega
    rw [he]
    exact hf.sum_le_tsum _ (fun k _ => hf0 k)
  have he : (∑ j : Fin n, f (Nat.dist j.val i.val)) =
      (∑ j ∈ S, f (Nat.dist j.val i.val)) + (∑ j ∈ T, f (Nat.dist j.val i.val)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [he]
  linarith

def firstIncrementDecay (b : ℝ) (k : ℕ) : ℝ := if k ≤ 1 then 1 else ((k - 1 : ℕ) : ℝ) ^ (2 * b - 2)

theorem firstIncrementDecay_nonneg (b : ℝ) (k : ℕ) : 0 ≤ firstIncrementDecay b k := by
  unfold firstIncrementDecay
  split_ifs <;> positivity

theorem firstIncrementDecay_square_summable (b : ℝ) (hb : b < 3 / 4) :
    Summable (fun k => (firstIncrementDecay b k) ^ 2) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ (4 * b - 4)) := Real.summable_nat_rpow.mpr (by linarith)
  have hs' : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (4 * b - 4)) := (summable_nat_add_iff 1).mpr hs
  apply (summable_nat_add_iff 2).mp
  apply hs'.congr
  intro k
  have hk : ¬k + 2 ≤ 1 := by omega
  simp only [firstIncrementDecay, hk, if_false, show k + 2 - 1 = k + 1 by omega]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem correlation_square_row_bound (b A e : ℝ) (hb : b < 3 / 4) (hA : 0 ≤ A) (he : 0 ≤ e)
    (n : ℕ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, |r i j| ≤ A * firstIncrementDecay b (Nat.dist j.val i.val) + e) (i : Fin n) :
    (∑ j, (r i j) ^ 2) ≤ 4 * A ^ 2 * (∑' k, (firstIncrementDecay b k) ^ 2) + 2 * n * e ^ 2 := by
  have hsum : (∑ j, (r i j) ^ 2) ≤ ∑ j : Fin n, (2 * A ^ 2 * (firstIncrementDecay b (Nat.dist j.val i.val)) ^ 2 + 2 * e ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hr i j) 2
    rw [sq_abs] at h
    nlinarith [sq_nonneg (A * firstIncrementDecay b (Nat.dist j.val i.val) - e)]
  have hdist := grid_distance_sum_le_tsum (fun k => (firstIncrementDecay b k) ^ 2)
    (firstIncrementDecay_square_summable b hb) (fun k => sq_nonneg _) n i
  have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2 * A ^ 2 by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith

end Hurst
