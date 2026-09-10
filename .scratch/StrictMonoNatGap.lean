import Hurst.ActiveSetReindex
import Mathlib.Data.Nat.Dist

namespace Hurst

/-- A strictly increasing map between finite initial segments cannot contract
integer distance. -/
theorem fin_natDist_le_natDist_of_strictMono
    {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (i j : Fin m) :
    Nat.dist i.val j.val ≤ Nat.dist (f i).val (f j).val := by
  wlog hij : i ≤ j generalizing i j
  · rw [Nat.dist_comm i.val j.val, Nat.dist_comm (f i).val (f j).val]
    exact this f hf j i (le_of_not_ge hij)
  let e : Fin m ↪ Fin n := ⟨f, hf.injective⟩
  have hsub : Finset.map e (Finset.Icc i j) ⊆ Finset.Icc (f i) (f j) := by
    intro x hx
    simp only [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [Finset.mem_Icc] at hy ⊢
    exact ⟨hf.monotone hy.1, hf.monotone hy.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_map, Fin.card_Icc, Fin.card_Icc] at hc
  have hijv : i.val ≤ j.val := hij
  have hfijv : (f i).val ≤ (f j).val := hf.monotone hij
  rw [Nat.dist_eq_sub_of_le hijv, Nat.dist_eq_sub_of_le hfijv]
  omega

/-- The active-window increasing enumeration cannot contract grid-index distance. -/
theorem localWeightActiveIndex_rank_dist_le_physical_dist
    (n q : ℕ) (δ t : ℝ)
    (i j : Fin (localWeightActiveSet n q δ t).card) :
    Nat.dist i.val j.val ≤
      Nat.dist (localWeightActiveIndex n q δ t i).val
        (localWeightActiveIndex n q δ t j).val := by
  exact fin_natDist_le_natDist_of_strictMono
    (localWeightActiveIndex n q δ t)
    (localWeightActiveIndex_strictMono n q δ t) i j

end Hurst
