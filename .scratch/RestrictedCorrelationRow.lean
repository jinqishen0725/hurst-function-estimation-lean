import Hurst.FeatureColoredEvenMoment

noncomputable section
open Set
namespace Hurst

theorem restricted_square_row_le_full
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : κ → κ → ℝ) (p : κ → Prop) [DecidablePred p]
    (i : {j : κ // p j}) :
    (∑ j ∈ Finset.univ.erase i, |r i.val j.val| ^ 2) ≤
      ∑ j : κ, |r i.val j| ^ 2 := by
  calc
    (∑ j ∈ Finset.univ.erase i, |r i.val j.val| ^ 2) ≤
        ∑ j : {j : κ // p j}, |r i.val j.val| ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun _ _ _ => sq_nonneg _)
    _ = ∑ j ∈ Finset.univ.filter p, |r i.val j| ^ 2 := by
      symm
      exact Finset.sum_subtype (Finset.univ.filter p) (by simp) _
    _ ≤ ∑ j : κ, |r i.val j| ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)

end Hurst
