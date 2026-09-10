import Hurst.LebesgueIntervalFeatures
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem featureCorrelation_basis_eq_inner_of_norm_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) (i j : Fin n) :
    featureCorrelation v (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) = ⟪v i, v j⟫ := by
  unfold featureCorrelation
  simp [EuclideanSpace.basisFun_apply, hv]

/-- Add `d` explicit independent unit Gaussian directions after a row of `m`
features.  `WithLp 2` supplies the Hilbert direct-sum norm, so the new
directions are exactly orthogonal to every original feature. -/
def paddedFeatureRow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (d : ℕ) (i : Fin (m + d)) :
    WithLp 2 (E × Lp ℝ 2 (volume : Measure ℝ)) :=
  if hi : i.val < m then
    WithLp.toLp 2 (u ⟨i.val, hi⟩, 0)
  else
    WithLp.toLp 2 (0, lebesgueUnitIntervalFeature (i.val - m))

@[simp] theorem paddedFeatureRow_castAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (d : ℕ) (i : Fin m) :
    paddedFeatureRow u d (Fin.castAdd d i) = WithLp.toLp 2 (u i, 0) := by
  simp [paddedFeatureRow]

@[simp] theorem paddedFeatureRow_natAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (d : ℕ) (i : Fin d) :
    paddedFeatureRow u d (Fin.natAdd m i) =
      WithLp.toLp 2 (0, lebesgueUnitIntervalFeature i.val) := by
  simp [paddedFeatureRow]

theorem paddedFeatureRow_inner_castAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (d : ℕ) (i j : Fin m) :
    ⟪paddedFeatureRow u d (Fin.castAdd d i),
      paddedFeatureRow u d (Fin.castAdd d j)⟫ = ⟪u i, u j⟫ := by
  simp [WithLp.prod_inner_apply]

theorem paddedFeatureRow_inner_cross
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (d : ℕ) (i : Fin m) (j : Fin d) :
    ⟪paddedFeatureRow u d (Fin.castAdd d i),
      paddedFeatureRow u d (Fin.natAdd m j)⟫ = 0 := by
  simp [WithLp.prod_inner_apply]

theorem paddedFeatureRow_inner_natAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (d : ℕ) (i j : Fin d) :
    ⟪paddedFeatureRow u d (Fin.natAdd m i),
      paddedFeatureRow u d (Fin.natAdd m j)⟫ =
        if i = j then 1 else 0 := by
  simp only [paddedFeatureRow_natAdd, WithLp.prod_inner_apply,
    inner_zero_left, zero_add, lebesgueUnitIntervalFeature_inner]
  by_cases hij : i = j
  · simp [hij]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, hv]

theorem paddedFeatureRow_norm_castAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (d : ℕ) (i : Fin m) :
    ‖paddedFeatureRow u d (Fin.castAdd d i)‖ = 1 := by
  have hinner := paddedFeatureRow_inner_castAdd u d i i
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu i] at hinner
  norm_num only [one_pow] at hinner
  nlinarith [norm_nonneg (paddedFeatureRow u d (Fin.castAdd d i))]

theorem paddedFeatureRow_norm_natAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (d : ℕ) (i : Fin d) :
    ‖paddedFeatureRow u d (Fin.natAdd m i)‖ = 1 := by
  have hinner := paddedFeatureRow_inner_natAdd u d i i
  simp only [if_pos, real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (paddedFeatureRow u d (Fin.natAdd m i))]

theorem paddedFeatureRow_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1) (d : ℕ) :
    ∀ i, ‖paddedFeatureRow u d i‖ = 1 := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · exact paddedFeatureRow_norm_castAdd u hu d
  · exact paddedFeatureRow_norm_natAdd u d

theorem paddedFeatureRow_correlation_castAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (d : ℕ) (i j : Fin m) :
    featureCorrelation (paddedFeatureRow u d)
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d i))
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d j)) =
    featureCorrelation u (EuclideanSpace.basisFun (Fin m) ℝ i)
      (EuclideanSpace.basisFun (Fin m) ℝ j) := by
  rw [featureCorrelation_basis_eq_inner_of_norm_one _
      (paddedFeatureRow_norm u hu d),
    featureCorrelation_basis_eq_inner_of_norm_one u hu,
    paddedFeatureRow_inner_castAdd]

theorem paddedFeatureRow_correlation_cross
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (d : ℕ) (i : Fin m) (j : Fin d) :
    featureCorrelation (paddedFeatureRow u d)
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d i))
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m j)) = 0 := by
  rw [featureCorrelation_basis_eq_inner_of_norm_one _
      (paddedFeatureRow_norm u hu d),
    paddedFeatureRow_inner_cross]

theorem paddedFeatureRow_correlation_cross_rev
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (d : ℕ) (i : Fin d) (j : Fin m) :
    featureCorrelation (paddedFeatureRow u d)
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m i))
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d j)) = 0 := by
  rw [featureCorrelation_basis_eq_inner_of_norm_one _
      (paddedFeatureRow_norm u hu d),
    real_inner_comm, paddedFeatureRow_inner_cross]

theorem paddedFeatureRow_correlation_natAdd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (d : ℕ) (i j : Fin d) :
    featureCorrelation (paddedFeatureRow u d)
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m i))
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m j)) =
      if i = j then 1 else 0 := by
  rw [featureCorrelation_basis_eq_inner_of_norm_one _
      (paddedFeatureRow_norm u hu d),
    paddedFeatureRow_inner_natAdd]

/-- Padding preserves a uniform covariance-square row bound, up to adjoining
the harmless diagonal bound `1` for a filler coordinate. -/
theorem paddedFeatureRow_correlation_square_row_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : Fin m → E) (hu : ∀ i, ‖u i‖ = 1)
    (d : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hrow : ∀ i, ∑ j, featureCorrelation u
      (EuclideanSpace.basisFun (Fin m) ℝ i)
      (EuclideanSpace.basisFun (Fin m) ℝ j) ^ 2 ≤ R) :
    ∀ i, ∑ j, featureCorrelation (paddedFeatureRow u d)
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ i)
      (EuclideanSpace.basisFun (Fin (m + d)) ℝ j) ^ 2 ≤ R := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro k
    rw [Fin.sum_univ_add]
    have htarget : (∑ j : Fin m,
        featureCorrelation (paddedFeatureRow u d)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d k))
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d j)) ^ 2) =
        ∑ j : Fin m, featureCorrelation u
          (EuclideanSpace.basisFun (Fin m) ℝ k)
          (EuclideanSpace.basisFun (Fin m) ℝ j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [paddedFeatureRow_correlation_castAdd u hu]
    rw [htarget]
    have hfill : (∑ j : Fin d,
        featureCorrelation (paddedFeatureRow u d)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d k))
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m j)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [paddedFeatureRow_correlation_cross u hu, zero_pow (by norm_num)]
    rw [hfill, add_zero]
    exact hrow k
  · intro k
    rw [Fin.sum_univ_add]
    have htarget : (∑ j : Fin m,
        featureCorrelation (paddedFeatureRow u d)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m k))
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.castAdd d j)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [paddedFeatureRow_correlation_cross_rev u hu, zero_pow (by norm_num)]
    rw [htarget, zero_add]
    classical
    calc
      (∑ j : Fin d,
        featureCorrelation (paddedFeatureRow u d)
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m k))
          (EuclideanSpace.basisFun (Fin (m + d)) ℝ (Fin.natAdd m j)) ^ 2) = 1 := by
            rw [Finset.sum_eq_single k]
            · rw [paddedFeatureRow_correlation_natAdd u hu, if_pos rfl]
              norm_num
            · intro j _ hj
              rw [paddedFeatureRow_correlation_natAdd u hu, if_neg (Ne.symm hj)]
              norm_num
            · simp
      _ ≤ R := hR

end Hurst
