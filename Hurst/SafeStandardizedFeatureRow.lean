import Hurst.ExactPaddedHitLaw
import Hurst.ActiveFeatureRows

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A normalized observation feature with an independent unit fallback for
the finitely many rows where nondegeneracy has not yet been established. -/
def safeStandardizedFeatureRow
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι) (k : κ) :
    WithLp 2 (E × Lp ℝ 2 (volume : Measure ℝ)) :=
  if hk : ∑ i, a k i • v i ≠ 0 then
    WithLp.toLp 2 (standardizedFeatureVector v (a k), 0)
  else
    WithLp.toLp 2 (0, lebesgueUnitIntervalFeature (Fintype.equivFin κ k).val)

theorem safeStandardizedFeatureRow_norm
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι) :
    ∀ k, ‖safeStandardizedFeatureRow v a k‖ = 1 := by
  intro k
  unfold safeStandardizedFeatureRow
  split_ifs with hk
  · rw [← sq_eq_sq₀ (by positivity) (by positivity),
      WithLp.prod_norm_sq_eq_of_L2]
    simp [norm_standardizedFeatureVector v (a k) hk]
  · rw [← sq_eq_sq₀ (by positivity) (by positivity),
      WithLp.prod_norm_sq_eq_of_L2]
    simp [lebesgueUnitIntervalFeature_norm]

theorem safeStandardizedFeatureRow_of_nonzero
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ k, ∑ i, a k i • v i ≠ 0) (k : κ) :
    safeStandardizedFeatureRow v a k =
      WithLp.toLp 2 (standardizedFeatureVector v (a k), 0) := by
  simp [safeStandardizedFeatureRow, ha k]

theorem safeStandardizedFeatureRow_correlation_of_nonzero
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ k, ∑ i, a k i • v i ≠ 0) (i j : κ) :
    featureCorrelation (safeStandardizedFeatureRow v a)
      (EuclideanSpace.basisFun κ ℝ i) (EuclideanSpace.basisFun κ ℝ j) =
      featureCorrelation v (a i) (a j) := by
  unfold featureCorrelation
  have hi : (∑ k, (EuclideanSpace.basisFun κ ℝ i) k •
      safeStandardizedFeatureRow v a k) = safeStandardizedFeatureRow v a i := by
    simp [EuclideanSpace.basisFun_apply]
  have hj : (∑ k, (EuclideanSpace.basisFun κ ℝ j) k •
      safeStandardizedFeatureRow v a k) = safeStandardizedFeatureRow v a j := by
    simp [EuclideanSpace.basisFun_apply]
  rw [hi, hj, safeStandardizedFeatureRow_norm v a i,
    safeStandardizedFeatureRow_norm v a j]
  simp only [one_mul, div_one]
  rw [safeStandardizedFeatureRow_of_nonzero v a ha,
    safeStandardizedFeatureRow_of_nonzero v a ha]
  simpa only [WithLp.prod_inner_apply, inner_zero_right, add_zero,
    featureCorrelation] using
    standardizedFeatureVector_inner v (a i) (a j)

theorem safeStandardizedFeatureRow_gaussian_eq_of_nonzero
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ k, ∑ i, a k i • v i ≠ 0) :
    featureGaussian (safeStandardizedFeatureRow v a) =
      featureGaussian (fun k => standardizedFeatureVector v (a k)) := by
  have hrow : safeStandardizedFeatureRow v a = fun k =>
      WithLp.toLp 2 (standardizedFeatureVector v (a k),
        (0 : Lp ℝ 2 (volume : Measure ℝ))) := by
    funext k
    exact safeStandardizedFeatureRow_of_nonzero v a ha k
  rw [hrow]
  exact featureGaussian_withLp_zero_eq (E := E) (ι := κ)
    (fun k => standardizedFeatureVector v (a k))

end Hurst
