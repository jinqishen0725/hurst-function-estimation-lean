import Hurst.PeelingInduction
import Hurst.SpectralMatchingInterface
import Hurst.SpectralMatchingSort
import Hurst.SpectralMatchingTail

/-!
# Bridge: raw mathlib eigenvalue power sums → the permuted-spectral-data interface

`Hurst.SpectralMatchingInterface` consumes the coefficientwise convergence of the
*canonically decreasingly permuted* eigenvalues in the padded dite shape

```
∀ j, Tendsto (fun n ↦ if hj : j < m n then
    (hA n).eigenvalues ((decreasingSpectralPerm (hA n).eigenvalues) ⟨j, hj⟩) else 0)
  atTop (𝓝 (lam j))
```

while `Hurst.PeelingInduction.paddedRearranged_tendsto` produces convergence of
`padRearranged (x n) j` from raw power sums of an arbitrary nonnegative array.
By the definition of `padRearranged` in `Hurst.PeelingSubtraction`,

```
padRearranged xv c = if h : c < m then xv (decreasingSpectralPerm xv ⟨c, h⟩) else 0
```

the two shapes agree *definitionally* once `x n` is instantiated with the raw
mathlib eigenvalue enumeration `(hA n).eigenvalues`; no rewrite lemma between the
two shapes is needed.  This file records that identification and combines it with
the decreasing-matching endpoint into a single consumption theorem.

Main contents:

* `eigenvalues_hcoeff_of_paddedRearranged_tendsto` : the interface's `hcoeff`
  shape, obtained from raw eigenvalue power sums via `paddedRearranged_tendsto`;
* `centeredMatrixQuadratic_tendsto_secondChaos_of_rawEigenvaluePowerSums` :
  the full package — from the raw power sums `(hm, hmtop, hNN, hl, hp)` and the
  `IsSecondChaosSeriesLaw` side inputs straight to
  `TendstoInDistribution` of the centered matrix quadratics.  The trace-square
  hypothesis of the interface is not an extra input: it is `hp 2`.

Nonnegativity caveat: mathlib's `Matrix.IsHermitian.eigenvalues` of a Hermitian
matrix need not be nonnegative, so the bridge is stated under the explicit
hypothesis `hNN : ∀ n i, 0 ≤ (hA n).eigenvalues i`.  On the actual-model side
the weighted feature matrix is a congruence of a Gram matrix, hence positive
semidefinite; that discharge belongs to a later wiring task and is not attempted
here.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-- **The interface's `hcoeff`, from raw eigenvalue power sums.**  Instantiating
`paddedRearranged_tendsto` at `x n := (hA n).eigenvalues` and unfolding
`padRearranged` gives exactly the padded dite shape consumed by
`centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching`.  Note the
explicit nonnegativity hypothesis `hNN`: Hermitian eigenvalues need not be
nonnegative in general, so the actual-model side must supply PSD-ness. -/
theorem eigenvalues_hcoeff_of_paddedRearranged_tendsto
    (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian) (lam : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hNN : ∀ (n : ℕ) (i : Fin (m n)), 0 ≤ (hA n).eigenvalues i)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), (hA n).eigenvalues i ^ k)
      atTop (𝓝 (∑' j, lam j ^ k))) :
    ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then
        (hA n).eigenvalues
          ((decreasingSpectralPerm (hA n).eigenvalues) ⟨j, hj⟩) else 0)
      atTop (𝓝 (lam j)) :=
  fun j =>
    paddedRearranged_tendsto m (fun n => (hA n).eigenvalues) lam hm hmtop hNN hl hp j

/-- **Full package corollary: raw eigenvalue power sums → distributional
convergence.**  Consumes exactly
`(hm, hmtop, hNN, hl, hp)` together with the `IsSecondChaosSeriesLaw`-side
inputs `P'`, `Q`, `hQ`, and concludes the full
`TendstoInDistribution` of the centered matrix quadratics against the
second-chaos law, via the interface endpoint
`centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching`.

The trace-square convergence is not an additional input: the interface's
`htr2` hypothesis is literally `hp 2 (le_of_lt' ...)`, i.e. the `k = 2` instance
of `hp`, and is supplied as `hp 2 le_rfl`.  Likewise a trace-of-square
formulation (`Tendsto (fun n ↦ ((A n) * (A n)).trace)`) is convertible with
`hp 2` through `hermitian_trace_square_eq_sum_eigenvalues_sq`, so the trace-based
packaging of the interface slots in without new glue.

PSD caveat as above: `hNN` must be discharged by the actual-model side (the
weighted feature matrix is a congruence of a Gram matrix); this is out of scope
for the present generic bridge. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_rawEigenvaluePowerSums
    (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hNN : ∀ (n : ℕ) (i : Fin (m n)), 0 ≤ (hA n).eigenvalues i)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), (hA n).eigenvalues i ^ k)
      atTop (𝓝 (∑' j, lam j ^ k))) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' :=
  centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching m A hA P'
    Q lam hQ hmtop
    (eigenvalues_hcoeff_of_paddedRearranged_tendsto m A hA lam hm hmtop hNN hl hp)
    (hp 2 le_rfl)

end Hurst
