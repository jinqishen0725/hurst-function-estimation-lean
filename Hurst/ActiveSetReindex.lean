import Hurst.LocalWeightSupport
import Hurst.FeatureHermiteApproximation
import Mathlib.Data.Finset.Sort

noncomputable section
open Set
namespace Hurst

/-- The increasing enumeration of the actual local-weight support. -/
def localWeightActiveEquiv (n q : ℕ) (δ t : ℝ) :
    Fin (localWeightActiveSet n q δ t).card ≃ {i // i ∈ localWeightActiveSet n q δ t} :=
  (localWeightActiveSet n q δ t).orderIsoOfFin rfl

/-- An active-window coordinate viewed as an index in the original grid row. -/
def localWeightActiveIndex (n q : ℕ) (δ t : ℝ)
    (j : Fin (localWeightActiveSet n q δ t).card) : Fin (n - q) :=
  (localWeightActiveEquiv n q δ t j).val

theorem localWeightActiveIndex_mem (n q : ℕ) (δ t : ℝ)
    (j : Fin (localWeightActiveSet n q δ t).card) :
    localWeightActiveIndex n q δ t j ∈ localWeightActiveSet n q δ t :=
  (localWeightActiveEquiv n q δ t j).property

/-- Because the local-polynomial weights vanish outside their support, any
weighted full-row sum is exactly its increasing active-window reindexing. -/
theorem localPolynomialWeights_sum_active
    (r n q : ℕ) (δ t : ℝ) (F : Fin (n - q) → ℝ) :
    ∑ i, localPolynomialWeights r n q δ t i * F i =
      ∑ j, localPolynomialWeights r n q δ t
        (localWeightActiveIndex n q δ t j) * F (localWeightActiveIndex n q δ t j) := by
  classical
  let S := localWeightActiveSet n q δ t
  calc
    ∑ i, localPolynomialWeights r n q δ t i * F i =
        ∑ i ∈ S, localPolynomialWeights r n q δ t i * F i := by
      apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro i _ hi
      rw [localPolynomialWeights_zero_outside_activeSet r n q δ t i hi, zero_mul]
    _ = ∑ x : {i // i ∈ S}, localPolynomialWeights r n q δ t x.val * F x.val := by
      exact (Finset.sum_attach S (fun i => localPolynomialWeights r n q δ t i * F i)).symm
    _ = ∑ j, localPolynomialWeights r n q δ t
        (localWeightActiveIndex n q δ t j) * F (localWeightActiveIndex n q δ t j) := by
      simpa only [localWeightActiveIndex] using
        ((localWeightActiveEquiv n q δ t).sum_comp
          (fun x => localPolynomialWeights r n q δ t x.val * F x.val)).symm

/-- The actual finite-Hermite statistic is unchanged by deleting all zero
weights and enumerating the remaining local window. -/
theorem gaussianLogTruncationStatistic_local_active
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n q : ℕ) (δ t : ℝ) (v : Fin n → E)
    (a : Fin (n - q) → EuclideanSpace ℝ (Fin n)) (M : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianLogTruncationStatistic v (localPolynomialWeights r n q δ t) a M x =
      ∑ j, localPolynomialWeights r n q δ t (localWeightActiveIndex n q δ t j) *
        (hermiteTruncationPolynomial gaussianLogLp M).eval
          (standardizedFeatureObservation v (a (localWeightActiveIndex n q δ t j)) x) := by
  exact localPolynomialWeights_sum_active r n q δ t
    (fun i => (hermiteTruncationPolynomial gaussianLogLp M).eval
      (standardizedFeatureObservation v (a i) x))

theorem localWeightActiveIndex_injective (n q : ℕ) (δ t : ℝ) :
    Function.Injective (localWeightActiveIndex n q δ t) := by
  intro i j hij
  exact (localWeightActiveEquiv n q δ t).injective (Subtype.ext hij)

/-- The chosen active-window enumeration preserves the grid order. -/
theorem localWeightActiveIndex_strictMono (n q : ℕ) (δ t : ℝ) :
    StrictMono (localWeightActiveIndex n q δ t) := by
  intro i j hij
  have h := ((localWeightActiveSet n q δ t).orderIsoOfFin rfl).strictMono hij
  change ((localWeightActiveSet n q δ t).orderIsoOfFin rfl i).val <
    ((localWeightActiveSet n q δ t).orderIsoOfFin rfl j).val
  exact h

end Hurst
