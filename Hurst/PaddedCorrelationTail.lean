import Hurst.PaddedFeatureRow
import Mathlib.Data.Nat.Dist

noncomputable section
namespace Hurst

/-- Independent right padding contributes no off-diagonal covariance-square
tail, and the initial-segment embedding preserves every target rank distance
exactly. -/
theorem paddedFeatureRow_correlation_square_tail_sum_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (d K : ℕ) :
    (∑ i : Fin (m + d), ∑ j : Fin (m + d),
      if K < Nat.dist i.val j.val then
        |featureCorrelation (paddedFeatureRow u d)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ i)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ j)| ^ 2 else 0) =
    ∑ i : Fin m, ∑ j : Fin m,
      if K < Nat.dist i.val j.val then
        |featureCorrelation u
          (EuclideanSpace.basisFun (Fin m) ℝ i)
          (EuclideanSpace.basisFun (Fin m) ℝ j)| ^ 2 else 0 := by
  rw [Fin.sum_univ_add]
  have htarget : (∑ i : Fin m, ∑ j : Fin (m + d),
      if K < Nat.dist (Fin.castAdd d i).val j.val then
        |featureCorrelation (paddedFeatureRow u d)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d i))
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ j)| ^ 2 else 0) =
      ∑ i : Fin m, ∑ j : Fin m,
        if K < Nat.dist i.val j.val then
          |featureCorrelation u
            (EuclideanSpace.basisFun (Fin m) ℝ i)
            (EuclideanSpace.basisFun (Fin m) ℝ j)| ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_add]
    have hmain : (∑ j : Fin m,
        if K < Nat.dist (Fin.castAdd d i).val (Fin.castAdd d j).val then
          |featureCorrelation (paddedFeatureRow u d)
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d i))
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d j))| ^ 2 else 0) =
        ∑ j : Fin m, if K < Nat.dist i.val j.val then
          |featureCorrelation u
            (EuclideanSpace.basisFun (Fin m) ℝ i)
            (EuclideanSpace.basisFun (Fin m) ℝ j)| ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [paddedFeatureRow_correlation_castAdd u hu]
      rfl
    rw [hmain]
    have hcross : (∑ j : Fin d,
        if K < Nat.dist (Fin.castAdd d i).val (Fin.natAdd m j).val then
          |featureCorrelation (paddedFeatureRow u d)
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d i))
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m j))| ^ 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [paddedFeatureRow_correlation_cross u hu]
      split_ifs <;> norm_num
    rw [hcross, add_zero]
  rw [htarget]
  have hfiller : (∑ i : Fin d, ∑ j : Fin (m + d),
      if K < Nat.dist (Fin.natAdd m i).val j.val then
        |featureCorrelation (paddedFeatureRow u d)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m i))
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ j)| ^ 2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [Fin.sum_univ_add]
    have hcross : (∑ j : Fin m,
        if K < Nat.dist (Fin.natAdd m i).val (Fin.castAdd d j).val then
          |featureCorrelation (paddedFeatureRow u d)
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m i))
            (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d j))| ^ 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [paddedFeatureRow_correlation_cross_rev u hu]
      split_ifs <;> norm_num
    rw [hcross, zero_add]
    apply Finset.sum_eq_zero
    intro j _
    rw [paddedFeatureRow_correlation_natAdd u hu]
    by_cases hij : i = j
    · subst j
      simp
    · rw [if_neg hij]
      split_ifs <;> norm_num
  rw [hfiller, add_zero]

end Hurst
