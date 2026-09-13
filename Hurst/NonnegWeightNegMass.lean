import Hurst.SignedInterfaceFinal
import Hurst.WeightedMatrixPSD
import Hurst.LocalLinearWeightsNonneg

/-!
# Route (a) of the `hNegMass` discharge: the nonneg-weights regime

`Hurst.SignedInterfaceFinal.centeredMatrixQuadratic_tendsto_secondChaos_of_
signedMatching` consumes the signed matching data (`hAbs` on the absolute
eigenvalues, `htr2` on the squares) plus the single smallness hypothesis

```
hNegMass : Tendsto (fun n ↦ ∑ i, (min (λ_i (n)) 0) ^ 2) atTop (𝓝 0).
```

There are two regimes in which this hypothesis is discharged:

* **Nonneg-weights regime (THIS file, route (a)).**  When the coefficient /
  eigenvalue array is entrywise nonnegative, `min (c n i) 0 = 0` pointwise, so
  the negative mass is *identically* zero:
  `hNegMass_zero_of_nonnegWeights`.  The signed packaging then instantiates
  with no analytic work at all
  (`centeredSpectralSquares_tendsto_secondChaos_of_signedMatching_of_nonneg`,
  `centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching_of_
  nonnegEigenvalues`).  On the actual chain the entrywise nonnegativity of the
  eigenvalues comes from `Hurst.WeightedMatrixPSD`:
  nonnegative weights `w` make `weightedFeatureQuadraticMatrix v a w =
  CFC.sqrt R * diagonal w * CFC.sqrt R` a congruence of the PSD matrix
  `diagonal w` (`weightedFeatureQuadraticMatrix_posSemidef`), whence
  `weightedFeatureQuadraticMatrix_eigenvalues_nonneg`.  The bridge theorem
  `centeredMatrixQuadratic_tendsto_secondChaos_of_nonnegWeights` chains
  weights-nonneg ⇒ eigenvalues-nonneg ⇒ `hNegMass ≡ 0` ⇒ signed packaging
  with NO negative-spectrum hypothesis.
* **Signed regime (route (b)).**  For genuinely signed weights/eigenvalues
  `hNegMass` does NOT vanish identically and needs the frozen-perturbation
  rate: `λ_i (n) ≥ -δ_n` by PSD domination
  (`eigenvalues_ge_neg_delta_of_posSemidef_of_norm_le`), so
  `∑_{neg} λ² ≤ δ_n * ∑ |λ| ≤ δ_n * √(m n) * sqrt (∑ λ²)` and the rate
  `δ_n * √(m n) → 0` finishes.  The rate is produced on the actual model by
  the dimension-weighted frozen-perturbation route of
  `Hurst.ActualQuadratureFinal.lean`
  (`actualQ1_trace_pow_tendsto_of_frozenPert` and the scope note there);
  without a rate, `δ_n ≥ 0` alone cannot force the negative mass to vanish
  (the count of negative eigenvalues may grow like `m n`).

Bonus bridge for the `r = 1` local-linear case: the pointwise criterion
`μ1 * x i ≤ μ2` of `Hurst.LocalLinearWeightsNonneg.localLinearWeight_nonneg`
makes the weight profile entrywise nonnegative
(`localLinearWeights_nonnegWeights` below), which is precisely the `hw`
hypothesis consumed by the nonneg-weights bridge.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## The trivial core: entrywise nonnegativity kills the negative mass -/

/-- **Pointwise step.**  A nonnegative entry has zero negative part. -/
theorem min_eq_zero_of_nonneg {c : ℝ} (h : 0 ≤ c) : min c 0 = 0 := min_eq_right h

/-- **The squared negative mass of a nonnegative array is identically zero.** -/
theorem sum_min_sq_eq_zero_of_nonneg {m : ℕ} (c : Fin m → ℝ)
    (h : ∀ i, 0 ≤ c i) : (∑ i, (min (c i) 0) ^ 2) = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [min_eq_right (h i)]; simp

/-- **Route (a): `hNegMass` is trivially discharged in the nonneg-weights
regime.**  If the coefficient array is entrywise nonnegative then
`min (c n i) 0 = 0` for every term, so the negative-mass summand is the
constant zero function and converges to `𝓝 0` with no analytic input. -/
theorem hNegMass_zero_of_nonnegWeights {m : ℕ → ℕ} (c : ∀ n, Fin (m n) → ℝ)
    (hnn : ∀ (n : ℕ) (i : Fin (m n)), 0 ≤ c n i) :
    Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0) := by
  have h0 : ∀ n : ℕ, (∑ i : Fin (m n), (min (c n i) 0) ^ 2) = 0 :=
    fun n => sum_min_sq_eq_zero_of_nonneg (c n) (hnn n)
  exact Tendsto.congr (fun n => (h0 n).symm) tendsto_const_nhds

/-! ## The signed consumption theorem in the nonneg-weights regime -/

/-- **The signed packaging (coefficient level) in the nonneg-weights regime.**
`centeredSpectralSquares_tendsto_secondChaos_of_signedMatching` with
`hNegMass` discharged trivially by `hNegMass_zero_of_nonnegWeights`: the
matching data (`hAbs` on the absolute coefficients, `htr2` on the squares)
plus entrywise nonnegativity `hnn` suffice, with NO negative-spectrum
smallness hypothesis. -/
theorem centeredSpectralSquares_tendsto_secondChaos_of_signedMatching_of_nonneg
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hm : Tendsto m atTop atTop)
    (hAbs : ∀ j : ℕ, Tendsto (fun n ↦ padRearranged (fun i : Fin (m n) => |c n i|) j)
      atTop (𝓝 (lam j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), (c n i) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2)))
    (hnn : ∀ (n : ℕ) (i : Fin (m n)), 0 ≤ c n i) :
    TendstoInDistribution (fun n ↦ centeredSpectralSquares (c n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' :=
  centeredSpectralSquares_tendsto_secondChaos_of_signedMatching
    m c P' Q lam hQ hm hAbs htr2 (hNegMass_zero_of_nonnegWeights c hnn)

/-- **The signed packaging (matrix level) in the nonneg-weights regime.**
`centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching` with
`hNegMass` discharged trivially: the hypothesis `hnn` here matches exactly
the eigenvalue nonnegativity discharged on the actual chain by
`Hurst.WeightedMatrixPSD.weightedFeatureQuadraticMatrix_eigenvalues_nonneg`
(see the bridge theorem below). -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching_of_nonnegEigenvalues
    (m : ℕ → ℕ) (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ)
    (hA : ∀ n, (A n).IsHermitian)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hm : Tendsto m atTop atTop)
    (hAbs : ∀ j : ℕ, Tendsto (fun n ↦ padRearranged
      (fun i : Fin (m n) => |(hA n).eigenvalues i|) j) atTop (𝓝 (lam j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), (hA n).eigenvalues i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2)))
    (hnn : ∀ (n : ℕ) (i : Fin (m n)), 0 ≤ (hA n).eigenvalues i) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' :=
  centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching
    m A hA P' Q lam hQ hm hAbs htr2
    (hNegMass_zero_of_nonnegWeights (fun n => (hA n).eigenvalues) hnn)

/-! ## Bridge to the actual chain: nonneg weights ⇒ PSD ⇒ nonneg eigenvalues

`Hurst.WeightedMatrixPSD.weightedFeatureQuadraticMatrix_posSemidef` shows that
nonnegative weights make the weighted feature matrix
`CFC.sqrt R * diagonal w * CFC.sqrt R` positive semidefinite (congruence of
the PSD `diagonal w` by the symmetric `CFC.sqrt R`), and
`eigenvalues_nonneg_of_posSemidef` converts PSD-ness to entrywise eigenvalue
nonnegativity.  Feeding that into the packaging above closes the chain
weights-nonneg ⇒ `hNegMass ≡ 0` ⇒ signed packaging. -/

section WeightedFeature

variable {iota E : Type*} [Fintype iota] [DecidableEq iota]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Bridge theorem of route (a) on the actual chain.**  For the array of
weighted feature matrices, the hypothesis `hw : ∀ n k, 0 ≤ w n k`
(entrywise nonnegative weights) alone — through
`weightedFeatureQuadraticMatrix_posSemidef` and
`weightedFeatureQuadraticMatrix_eigenvalues_nonneg` — discharges BOTH the
eigenvalue nonnegativity and, trivially, the `hNegMass` smallness of
`centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching`, leaving only
the matching data `hAbs` / `htr2`. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_nonnegWeights
    (m : ℕ → ℕ)
    (v : ℕ → iota → E) (w : ∀ n, Fin (m n) → ℝ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    (hw : ∀ (n : ℕ) (k : Fin (m n)), 0 ≤ w n k)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hm : Tendsto m atTop atTop)
    (hAbs : ∀ j : ℕ, Tendsto (fun n ↦ padRearranged (fun i : Fin (m n) =>
      |(weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i|) j)
      atTop (𝓝 (lam j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n),
      (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2))) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic
        (weightedFeatureQuadraticMatrix (v n) (a n) (w n)))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  refine centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching_of_nonnegEigenvalues
    m (fun n => weightedFeatureQuadraticMatrix (v n) (a n) (w n))
    (fun n => weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n))
    P' Q lam hQ hm hAbs htr2 ?_
  intro n i
  exact weightedFeatureQuadraticMatrix_eigenvalues_nonneg (v n) (a n) (w n) (hw n) i

end WeightedFeature

/-! ## Bonus: the `r = 1` local-linear weight criterion feeds `hw ≥ 0`

`Hurst.LocalLinearWeightsNonneg.localLinearWeight_nonneg` gives the sharp
pointwise sign criterion `μ1 * x i ≤ μ2` (i.e. `G 0 1 * x i ≤ G 1 1`, no
determinant hypothesis needed) for the degree-one local-polynomial weights.
Packaged over all grid points it produces exactly the entrywise nonnegative
weight profile consumed by the bridge theorem above. -/

/-- **`r = 1` local-linear corollary of the criterion.**  Under the
balanced-window pointwise criterion `μ1 * x i ≤ μ2` for every grid point, the
degree-one weight profile `localPolynomialWeights 1 (N n) q (b n) (t n)` is
entrywise nonnegative — precisely the `hw` hypothesis of
`centeredMatrixQuadratic_tendsto_secondChaos_of_nonnegWeights` (with
`m n = N n - q` grid points), so in this regime route (a) applies and
`hNegMass` is trivially zero. -/
theorem localLinearWeights_nonnegWeights {N : ℕ → ℕ} {q : ℕ} (b t : ℕ → ℝ)
    (hN : ∀ n, 0 < N n) (hb : ∀ n, 0 < b n)
    (h : ∀ (n : ℕ) (i : Fin (N n - q)),
      (localDesignGram 1 (N n) q (b n) (t n)) (0 : Fin 2) (1 : Fin 2)
          * ((grid (N n) i.val - t n) / b n)
        ≤ (localDesignGram 1 (N n) q (b n) (t n)) (1 : Fin 2) (1 : Fin 2))
    (n : ℕ) : ∀ i : Fin (N n - q), 0 ≤ localPolynomialWeights 1 (N n) q (b n) (t n) i :=
  localLinearWeights_nonneg (N n) q (b n) (t n) (hN n) (hb n) (h n)

end Hurst
