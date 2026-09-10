import Hurst.CorrelationSums

noncomputable section
open Set
namespace Hurst

def secondIncrementDecay (b : ℝ) (k : ℕ) : ℝ := if k ≤ 2 then 1 else ((k - 2 : ℕ) : ℝ) ^ (2 * b - 4)

theorem secondIncrementDecay_nonneg (b : ℝ) (k : ℕ) : 0 ≤ secondIncrementDecay b k := by
  unfold secondIncrementDecay
  split_ifs <;> positivity

theorem secondIncrementDecay_square_summable (b : ℝ) (hb : b < 1) :
    Summable (fun k => (secondIncrementDecay b k) ^ 2) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ (4 * b - 8)) := Real.summable_nat_rpow.mpr (by linarith)
  have hs' : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (4 * b - 8)) := (summable_nat_add_iff 1).mpr hs
  apply (summable_nat_add_iff 3).mp
  apply hs'.congr
  intro k
  have hk : ¬k + 3 ≤ 2 := by omega
  simp only [secondIncrementDecay, hk, if_false, show k + 3 - 2 = k + 1 by omega]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem second_correlation_square_row_bound (b A e : ℝ) (hb : b < 1) (hA : 0 ≤ A) (he : 0 ≤ e)
    (n : ℕ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, |r i j| ≤ A * secondIncrementDecay b (Nat.dist j.val i.val) + e) (i : Fin n) :
    (∑ j, (r i j) ^ 2) ≤ 4 * A ^ 2 * (∑' k, (secondIncrementDecay b k) ^ 2) + 2 * n * e ^ 2 := by
  have hsum : (∑ j, (r i j) ^ 2) ≤ ∑ j : Fin n, (2 * A ^ 2 * (secondIncrementDecay b (Nat.dist j.val i.val)) ^ 2 + 2 * e ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hr i j) 2
    rw [sq_abs] at h
    nlinarith [sq_nonneg (A * secondIncrementDecay b (Nat.dist j.val i.val) - e)]
  have hdist := grid_distance_sum_le_tsum (fun k => (secondIncrementDecay b k) ^ 2)
    (secondIncrementDecay_square_summable b hb) (fun k => sq_nonneg _) n i
  have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2 * A ^ 2 by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith

end Hurst
