import Hurst.ActiveCorrelationTail
import Hurst.FeatureObservationMap

noncomputable section
open Set MeasureTheory Filter Matrix
open scoped RealInnerProductSpace Topology
namespace Hurst

variable {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coordinate correlation of normalized selected feature vectors is the
original standardized-feature correlation. -/
theorem featureCorrelation_standardizedFeatureVector_basis
    (v : ι → E) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ k, ∑ i, a k i • v i ≠ 0) (i j : κ) :
    featureCorrelation (fun k => standardizedFeatureVector v (a k))
      (EuclideanSpace.basisFun κ ℝ i) (EuclideanSpace.basisFun κ ℝ j) =
      featureCorrelation v (a i) (a j) := by
  unfold featureCorrelation
  have hi : (∑ k, (EuclideanSpace.basisFun κ ℝ i) k •
      standardizedFeatureVector v (a k)) = standardizedFeatureVector v (a i) := by
    simp [EuclideanSpace.basisFun_apply]
  have hj : (∑ k, (EuclideanSpace.basisFun κ ℝ j) k •
      standardizedFeatureVector v (a k)) = standardizedFeatureVector v (a j) := by
    simp [EuclideanSpace.basisFun_apply]
  rw [hi, hj, norm_standardizedFeatureVector v (a i) (ha i),
    norm_standardizedFeatureVector v (a j) (ha j)]
  simp only [one_mul, div_one]
  exact standardizedFeatureVector_inner v (a i) (a j)

/-- Restricting a nonnegative full correlation row to the injectively indexed
active window cannot increase its square mass. -/
theorem active_correlation_square_row_le_full
    (n q : ℕ) (δ t : ℝ)
    (r : Fin (n - q) → Fin (n - q) → ℝ)
    (i : Fin (localWeightActiveSet n q δ t).card) :
    (∑ j : Fin (localWeightActiveSet n q δ t).card,
      r (localWeightActiveIndex n q δ t i)
        (localWeightActiveIndex n q δ t j) ^ 2) ≤
      ∑ j : Fin (n - q), r (localWeightActiveIndex n q δ t i) j ^ 2 := by
  classical
  let emb : Fin (localWeightActiveSet n q δ t).card ↪ Fin (n - q) :=
    ⟨localWeightActiveIndex n q δ t,
      localWeightActiveIndex_injective n q δ t⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (s := Finset.univ.map emb) (t := Finset.univ)
    (Finset.subset_univ _) (fun j _ _ => sq_nonneg
      (r (localWeightActiveIndex n q δ t i) j))
  rw [Finset.sum_map] at hle
  exact hle

/-- Full-row square summability gives the exact active normalized-feature row
condition appearing in B&S (3.1). -/
theorem active_standardizedFeatureVector_correlation_square_row_le
    (n q : ℕ) (δ t : ℝ)
    (v : Fin n → E) (a : Fin (n - q) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, ∑ j, a i j • v j ≠ 0) (R : ℝ)
    (hrow : ∀ i, ∑ j, featureCorrelation v (a i) (a j) ^ 2 ≤ R) :
    ∀ i : Fin (localWeightActiveSet n q δ t).card,
      ∑ j, featureCorrelation
        (fun k => standardizedFeatureVector v
          (a (localWeightActiveIndex n q δ t k)))
        (EuclideanSpace.basisFun
          (Fin (localWeightActiveSet n q δ t).card) ℝ i)
        (EuclideanSpace.basisFun
          (Fin (localWeightActiveSet n q δ t).card) ℝ j) ^ 2 ≤ R := by
  intro i
  rw [show (∑ j, featureCorrelation
      (fun k => standardizedFeatureVector v
        (a (localWeightActiveIndex n q δ t k)))
      (EuclideanSpace.basisFun
        (Fin (localWeightActiveSet n q δ t).card) ℝ i)
      (EuclideanSpace.basisFun
        (Fin (localWeightActiveSet n q δ t).card) ℝ j) ^ 2) =
    ∑ j, featureCorrelation v
      (a (localWeightActiveIndex n q δ t i))
      (a (localWeightActiveIndex n q δ t j)) ^ 2 by
      apply Finset.sum_congr rfl
      intro j hj
      rw [featureCorrelation_standardizedFeatureVector_basis]
      intro k
      exact ha (localWeightActiveIndex n q δ t k)]
  exact (active_correlation_square_row_le_full n q δ t
    (fun i j => featureCorrelation v (a i) (a j)) i).trans
      (hrow (localWeightActiveIndex n q δ t i))

end Hurst
