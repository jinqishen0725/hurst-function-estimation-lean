import Hurst.ActiveWindowCoordinates
import Mathlib.Data.Nat.Dist

noncomputable section
namespace Hurst

/-- Consecutiveness of the active-window enumeration makes rank distance and
physical grid-index distance exactly equal. -/
theorem localWeightActiveIndex_physical_dist_eq_rank_dist
    (n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (i j : Fin (localWeightActiveSet n q δ t).card) :
    Nat.dist (localWeightActiveIndex n q δ t i).val
        (localWeightActiveIndex n q δ t j).val =
      Nat.dist i.val j.val := by
  rw [localWeightActiveIndex_eq_first_add_rank n q hn δ t hδ hcard i,
    localWeightActiveIndex_eq_first_add_rank n q hn δ t hδ hcard j]
  exact Nat.dist_add_add_left _ _ _

/-- The orientation used by row-sum and off-diagonal estimates. -/
theorem localWeightActiveIndex_rank_dist_eq_physical_dist
    (n q : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (hcard : 0 < (localWeightActiveSet n q δ t).card)
    (i j : Fin (localWeightActiveSet n q δ t).card) :
    Nat.dist i.val j.val =
      Nat.dist (localWeightActiveIndex n q δ t i).val
        (localWeightActiveIndex n q δ t j).val :=
  (localWeightActiveIndex_physical_dist_eq_rank_dist
    n q hn δ t hδ hcard i j).symm

end Hurst
