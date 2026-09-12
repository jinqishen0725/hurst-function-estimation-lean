import Hurst.FeatureQuadraticSpectral
import Hurst.SpectralMatchingInterface
import Hurst.HcoeffBridge

/-!
# PSD-ness of the weighted feature matrix and the discharge of the `hNN` bridge hypothesis

`Hurst.HcoeffBridge.centeredMatrixQuadratic_tendsto_secondChaos_of_rawEigenvaluePowerSums`
requires the explicit hypothesis `hNN : ∀ n i, 0 ≤ (hA n).eigenvalues i` on the Hermitian
array of weighted feature matrices.  This file discharges it:

* `eigenvalues_nonneg_of_posSemidef` : generic — a positive semidefinite real matrix has
  nonnegative eigenvalues (mathlib: `Matrix.PosSemidef.eigenvalues_nonneg`);
* `weightedFeatureQuadraticMatrix_posSemidef` : the weighted feature matrix
  `weightedFeatureQuadraticMatrix v a w = CFC.sqrt R * diagonal w * CFC.sqrt R` (with `R`
  the feature Gram/correlation matrix) is positive semidefinite **provided the weights are
  nonnegative** `∀ i, 0 ≤ w i`, as the congruence `diagonal w ↦ Sᴴ * diagonal w * S` of a
  PSD diagonal matrix by `S = CFC.sqrt R`;
* `weightedFeatureQuadraticMatrix_eigenvalues_nonneg` : the eigenvalue corollary in the
  exact `(weightedFeatureQuadraticMatrix_isHermitian v a w).eigenvalues` shape;
* `centeredMatrixQuadratic_tendsto_secondChaos_of_weightedFeature_nonnegWeights` and
  `gaussianLogQuadraticStatistic_tendsto_secondChaos_of_nonnegWeights` : the actual-data
  packaging that plugs the discharged `hNN` (together with the raw eigenvalue power sums)
  into the HcoeffBridge / SpectralMatchingInterface endpoints.

## Honest signed-weights verdict

The nonnegativity hypothesis `∀ i, 0 ≤ w i` is NOT automatic in the actual chain: the
canonical weights `localPolynomialWeights r n q b t` of `Hurst/LocalWeights.lean` are
equivalent-kernel weights
`((n*b)⁻¹ * localKernel (...)) * ∑ k, (localDesignGram r n q b t)⁻¹ 0 k * ((grid - t)/b)^k`,
whose local-kernel factor is nonnegative but whose inverse-design-gram row
`(localDesignGram r n q b t)⁻¹ 0 k` carries arbitrary signs once the polynomial degree `r`
is at least `1` (this is the familiar sign-changing boundary behaviour of local polynomial
regression weights).  For signed weights the matrix
`CFC.sqrt R * diagonal w * CFC.sqrt R` is only a *congruence* of `diagonal w`
(`weightedFeatureQuadraticMatrix_quadraticForm` records the honest consequence: the
quadratic form is the signed weighted sum of squares `∑ i, w i * y i ^ 2`), so its
eigenvalues can be negative and `hNN` genuinely fails; the peeling bridge
`Hurst.PeelingInduction.paddedRearranged_tendsto` (which needs a nonnegative array) does
not go through on the raw eigenvalues.  A signed-weights chain would have to run the
peeling on `|eigenvalues|` (even power sums `∑ λ ^ k` for even `k` equal `∑ |λ| ^ k`, so
the even-moment/trace-square inputs survive verbatim) with the odd power sums handled
separately; that variant is deliberately NOT forced here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology RealInnerProductSpace MatrixOrder

namespace Hurst

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Generic PSD ⇒ nonneg eigenvalues.**  Every eigenvalue (in mathlib's unsorted
`Matrix.IsHermitian.eigenvalues` enumeration) of a positive semidefinite real matrix is
nonnegative. -/
theorem eigenvalues_nonneg_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) (i : n) :
    0 ≤ hA.1.eigenvalues i :=
  hA.eigenvalues_nonneg i

/-- Generic form with an explicit Hermitian proof: a real Hermitian matrix is positive
semidefinite if and only if all of its eigenvalues are nonnegative. -/
theorem posSemidef_iff_eigenvalues_nonneg_real {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ i, 0 ≤ hA.eigenvalues i :=
  hA.posSemidef_iff_eigenvalues_nonneg

end Generic

section WeightedFeature

variable {iota kappa E : Type*} [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq iota] in
/-- **The weighted feature matrix is positive semidefinite under nonnegative weights.**
It is the congruence `S * diagonal w * S` of the PSD diagonal matrix `diagonal w` by the
symmetric matrix `S = CFC.sqrt R`, where `R` is the feature Gram matrix (PSD by
`Matrix.posSemidef_gram`). -/
theorem weightedFeatureQuadraticMatrix_posSemidef
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (weightedFeatureQuadraticMatrix v a w).PosSemidef := by
  have hD : (Matrix.diagonal w).PosSemidef := Matrix.PosSemidef.diagonal hw
  have hs : (CFC.sqrt (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k)))).IsHermitian :=
    (CFC.sqrt_nonneg (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k)))).isSelfAdjoint.isHermitian
  have hcong := hD.mul_mul_conjTranspose_same
    (CFC.sqrt (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k))))
  rw [hs.eq] at hcong
  rw [weightedFeatureQuadraticMatrix]
  exact hcong

/-- The eigenvalues of the weighted feature matrix are nonnegative under nonnegative
weights — this is the pointwise discharge of the `hNN` hypothesis of
`Hurst.HcoeffBridge.centeredMatrixQuadratic_tendsto_secondChaos_of_rawEigenvaluePowerSums`. -/
theorem weightedFeatureQuadraticMatrix_eigenvalues_nonneg
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : kappa) :
    0 ≤ (weightedFeatureQuadraticMatrix_isHermitian v a w).eigenvalues i :=
  (weightedFeatureQuadraticMatrix_posSemidef v a w hw).eigenvalues_nonneg i

omit [DecidableEq iota] in
/-- Honest signed-weights statement: for arbitrary (possibly signed) weights the
quadratic form of the weighted feature matrix is the *signed* weighted sum of squares
`∑ i, w i * y i ^ 2` of the transformed coordinates `y = CFC.sqrt R x`; i.e. the matrix
is congruent to `diagonal w` and inherits the signs of `w` rather than PSD-ness. -/
theorem weightedFeatureQuadraticMatrix_quadraticForm
    (v : iota → E) (a : kappa → EuclideanSpace ℝ iota) (w : kappa → ℝ)
    (x : EuclideanSpace ℝ kappa) :
    dotProduct (WithLp.ofLp x)
        ((weightedFeatureQuadraticMatrix v a w) *ᵥ WithLp.ofLp x) =
      ∑ i, w i * ((Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.sqrt (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k)))) x) i) ^ 2 := by
  rw [weightedFeatureQuadraticMatrix]
  exact matrixQuadratic_symmetric_diagonal_conjugate _
    ((CFC.sqrt_nonneg (Matrix.gram ℝ (fun k ↦ standardizedFeatureVector v (a k)))).isSelfAdjoint.isHermitian)
    w x

/-- **Actual-data packaging, matrix level.**  For the array of weighted feature matrices
`A n = weightedFeatureQuadraticMatrix (v n) (a n) (w n)` the `hNN` hypothesis of
`centeredMatrixQuadratic_tendsto_secondChaos_of_rawEigenvaluePowerSums` is discharged by
PSD-ness under the nonneg-weights hypothesis `hw`, so the raw eigenvalue power sums
`(hm, hmtop, hl, hp)` plus the second-chaos side inputs suffice verbatim. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_weightedFeature_nonnegWeights
    (m : ℕ → ℕ)
    (v : ℕ → iota → E) (w : ∀ n, Fin (m n) → ℝ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    (hw : ∀ (n : ℕ) (k : Fin (m n)), 0 ≤ w n k)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n),
        (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i ^ k)
      atTop (𝓝 (∑' j, lam j ^ k))) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic
        (weightedFeatureQuadraticMatrix (v n) (a n) (w n)))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  refine centeredMatrixQuadratic_tendsto_secondChaos_of_rawEigenvaluePowerSums m
    (fun n => weightedFeatureQuadraticMatrix (v n) (a n) (w n))
    (fun n => weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n))
    P' Q lam hQ hm hmtop ?_ hl hp
  intro n i
  exact weightedFeatureQuadraticMatrix_eigenvalues_nonneg (v n) (a n) (w n) (hw n) i

/-- **Actual-data packaging, statistic level.**  Combining the discharged `hNN` with the
peeling bridge `eigenvalues_hcoeff_of_paddedRearranged_tendsto` and the
weighted-feature interface endpoint: raw eigenvalue power sums of the weighted feature
matrices, nonnegative weights, and the correlation-energy trace-square convergence give
distributional convergence of the actual statistics `gaussianLogQuadraticStatistic`
against the second-chaos law. -/
theorem gaussianLogQuadraticStatistic_tendsto_secondChaos_of_nonnegWeights
    (m : ℕ → ℕ)
    (v : ℕ → iota → E) (w : ∀ n, Fin (m n) → ℝ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    (ha : ∀ (n : ℕ) (k : Fin (m n)), ∑ i, a n k i • v n i ≠ 0)
    (hw : ∀ (n : ℕ) (k : Fin (m n)), 0 ≤ w n k)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n),
        (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i ^ k)
      atTop (𝓝 (∑' j, lam j ^ k)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), ∑ j : Fin (m n),
        w n i * w n j * (featureCorrelation (v n) (a n i) (a n j)) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2))) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic (v n) (w n) (a n) x)
      atTop Q (fun n => featureGaussian (v n)) P' := by
  have hA : ∀ n, (weightedFeatureQuadraticMatrix (v n) (a n) (w n)).IsHermitian :=
    fun n => weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)
  have hNN : ∀ (n : ℕ) (i : Fin (m n)), 0 ≤ (hA n).eigenvalues i := fun n i =>
    weightedFeatureQuadraticMatrix_eigenvalues_nonneg (v n) (a n) (w n) (hw n) i
  refine gaussianLogQuadraticStatistic_tendsto_secondChaos_of_decreasing_matching m v w a ha
    P' Q lam hQ hmtop
    (eigenvalues_hcoeff_of_paddedRearranged_tendsto m
      (fun n => weightedFeatureQuadraticMatrix (v n) (a n) (w n)) hA lam hm hmtop hNN
      hl hp) htr2

end WeightedFeature

end Hurst
