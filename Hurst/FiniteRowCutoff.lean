import Hurst.LatticeCount
import Mathlib.Data.Nat.Dist

noncomputable section
open scoped BigOperators
namespace Hurst

private theorem finite_row_band_card {m : ℕ} (R : ℕ) (i : Fin m) :
    (Finset.univ.filter
      (fun j : Fin m => Nat.dist j.val i.val ≤ R)).card ≤ 2 * R + 1 := by
  let T : Finset (Fin m) := Finset.univ.filter
    (fun j => Nat.dist j.val i.val ≤ R)
  have hc := finite_lattice_interval_card T
    ((i.val : ℝ) - R) ((i.val : ℝ) + R) (by linarith) (by
      intro j hj
      have hd : Nat.dist j.val i.val ≤ R := (Finset.mem_filter.mp hj).2
      have hleft : j.val ≤ i.val + R := by
        rcases le_total i.val j.val with hij | hji
        · rw [Nat.dist_eq_sub_of_le_right hij] at hd
          omega
        · omega
      have hright : i.val ≤ j.val + R := by
        rcases le_total j.val i.val with hji | hij
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right hji] at hd
          omega
        · omega
      have hleftR : (j.val : ℝ) ≤ (i.val : ℝ) + R := by exact_mod_cast hleft
      have hrightR : (i.val : ℝ) ≤ (j.val : ℝ) + R := by exact_mod_cast hright
      constructor
      · linarith
      · linarith)
  have hcR : (T.card : ℝ) ≤ (2 * R + 1 : ℕ) := by
    convert hc using 1 <;> push_cast <;> ring
  exact_mod_cast hcR

/-- A finite row is controlled by the width of a near-diagonal band and a
uniform bound outside that band.  This is the deterministic row estimate
used for local long-memory variances. -/
theorem finite_correlation_square_row_le_cutoff
    {m : ℕ} (R : ℕ) (e : ℝ) (he : 0 ≤ e)
    (r : Fin m → Fin m → ℝ) (i : Fin m)
    (hone : ∀ j, |r i j| ≤ 1)
    (hfar : ∀ j, R < Nat.dist j.val i.val → |r i j| ≤ e) :
    (∑ j : Fin m, r i j ^ 2) ≤
      (2 * (R : ℝ) + 1) + (m : ℝ) * e ^ 2 := by
  let S : Finset (Fin m) := Finset.univ.filter
    (fun j => Nat.dist j.val i.val ≤ R)
  let T : Finset (Fin m) := Finset.univ.filter
    (fun j => ¬ Nat.dist j.val i.val ≤ R)
  have hnear : (∑ j ∈ S, r i j ^ 2) ≤ 2 * (R : ℝ) + 1 := by
    calc
      _ ≤ ∑ _j ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hp := pow_le_pow_left₀ (abs_nonneg (r i j)) (hone j) 2
        simpa only [sq_abs, one_pow] using hp
      _ = (S.card : ℝ) := by simp
      _ ≤ (2 * R + 1 : ℕ) := by
        exact_mod_cast finite_row_band_card R i
      _ = 2 * (R : ℝ) + 1 := by push_cast; ring
  have hfarSum : (∑ j ∈ T, r i j ^ 2) ≤ (m : ℝ) * e ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ T, e ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjfar : R < Nat.dist j.val i.val :=
          lt_of_not_ge (Finset.mem_filter.mp hj).2
        have hp := pow_le_pow_left₀ (abs_nonneg (r i j)) (hfar j hjfar) 2
        simpa only [sq_abs] using hp
      _ = (T.card : ℝ) * e ^ 2 := by simp
      _ ≤ (m : ℝ) * e ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg e)
        have hc : T.card ≤ m := by
          simpa only [Fintype.card_fin] using Finset.card_le_univ T
        exact_mod_cast hc
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin m => Nat.dist j.val i.val ≤ R)]
  simpa only [S, T] using add_le_add hnear hfarSum

end Hurst
