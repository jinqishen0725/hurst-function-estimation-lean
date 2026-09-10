import Hurst.BumpPacking
import Hurst.Basic
import Mathlib.Order.Interval.Finset.Nat

noncomputable section
open Set
namespace Hurst

theorem finite_lattice_interval_card {m : ℕ} (S : Finset (Fin m)) (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ i ∈ S, a ≤ (i.val : ℝ) ∧ (i.val : ℝ) ≤ b) : (S.card : ℝ) ≤ b - a + 1 := by
  classical
  by_cases hne : S.Nonempty
  · let lo := S.min' hne
    let hi := S.max' hne
    have hlo : lo ∈ S := S.min'_mem hne
    have hhi : hi ∈ S := S.max'_mem hne
    have hlohi : lo.val ≤ hi.val := (S.min'_le _ hhi)
    have hcard : S.card ≤ (Finset.Icc lo.val hi.val).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin m => i.val)
      · intro i hiS
        exact Finset.mem_Icc.mpr ⟨S.min'_le _ hiS, S.le_max' _ hiS⟩
      · intro i hiS j hjS hij
        exact Fin.ext hij
    rw [Nat.card_Icc] at hcard
    have he : (S.card : ℝ) ≤ (hi.val : ℝ) + 1 - lo.val := by
      have he := (Nat.cast_le (α := ℝ)).mpr hcard
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at he
      exact he
    have helo := (hS lo hlo).1
    have hehi := (hS hi hhi).2
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

theorem midpoint_active_card_bound (n m : ℕ) (hn : 0 < n) (b t : ℝ) (hb : 0 < b)
    (S : Finset (Fin m)) (hS : ∀ i ∈ S, |(grid n i.val - t) / b| < 1) :
    (S.card : ℝ) ≤ 2 * ((n : ℝ) * b) + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he := finite_lattice_interval_card S ((n : ℝ) * (t - b) - 1 / 2)
    ((n : ℝ) * (t + b) - 1 / 2) (by nlinarith) (fun i hi => by
      have hx := abs_lt.mp (hS i hi)
      have h1 := (lt_div_iff₀ hb).mp hx.1
      have h2 := (div_lt_iff₀ hb).mp hx.2
      have hg1 : t - b < grid n i.val := by linarith
      have hg2 : grid n i.val < t + b := by linarith
      unfold grid at hg1 hg2
      have he1 := (lt_div_iff₀ hnR).mp hg1
      have he2 := (div_lt_iff₀ hnR).mp hg2
      constructor <;> nlinarith)
  exact he.trans_eq (by ring)

end Hurst
