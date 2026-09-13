import Hurst.EvenPeeling
import Hurst.EigenvaluePerturbation
import Hurst.ActualQuadratureConfluence
import Hurst.HcoeffBridge
import Hurst.FeatureQuadraticSpectral
import Hurst.FiniteSpectralArrayConvergence
import Hurst.SpectralMatchingTail
import Hurst.TriangularL1Transfer
import Hurst.L2TestApproximation

/-!
# Signed interface final packaging: |λ|-rearrangement → statistic-level TendstoInDistribution

This is the last packaging layer of the SIGNED route.  The landed consumption
endpoint `Hurst.SpectralMatchingInterface` (and the `Hurst.HcoeffBridge`
packaging of it) consumes coefficientwise convergence of the RAW eigenvalues;
the actual eigenvalues are SIGNED and what actually converged (via
`Hurst.ActualQuadratureConfluence.actualQ1EigenvaluePowerSums_tendsto`, i.e. the
output of `Hurst.EvenPeeling.paddedAbsRearranged_tendsto`) is the padded
decreasing rearrangement of the ABSOLUTE eigenvalues:

```
∀ j, Tendsto (fun n ↦ padRearranged (fun i ↦ |λ_i (n)|) j) atTop (𝓝 (lam j)).
```

The signed packaging turns this into the statistic-level
`TendstoInDistribution` at the cost of a single explicit smallness hypothesis
on the negative spectrum:

* `hNegMass : Tendsto (fun n ↦ ∑ i, (min (λ_i (n)) 0) ^ 2) atTop (𝓝 0)`
  (the squared L2 mass of the negative eigenvalues vanishes).

Deterministic core.  Under the SAME Gaussian coordinates the two centered
second-chaos statistics differ by exactly the negative-part contribution:

```
statistic(λ) − statistic(|λ|) = centeredSpectralSquares (fun i ↦ c i - |c i|),
```

whose exact second moment is `2 * ∑ i, (c i - |c i|)² = 8 * ∑_{c i < 0} c i²`
(`centeredSpectralSquares_secondMoment`, `sum_c_sub_abs_sq_eq_four_mul_min_sq`).
An exact L2 bound therefore replaces the (unprovable without rates) pointwise
`max` bound of the naive estimate.  The L2 smallness is promoted to
distributional smallness by the triangular L1 transfer
(`Hurst.TriangularL1Transfer.triangular_L1_distribution_transfer`, a Slutsky-type
tool): the statistic of `λ` and that of `|λ|` differ by a random summand whose
L2 norm is `sqrt (8 * ∑_{neg} λ²) → 0`.

Where `hNegMass` discharges from `hPert` (the one-line derivation).  H1 gives
`λ_i (n) ≥ -δ_n` for every `i`, via
`Hurst.EigenvaluePerturbation.eigenvalues_ge_neg_delta_of_posSemidef_of_norm_le`
with `B` the PSD Riesz limit matrix; `eigenvalues_negMass_le_delta_mul_absSum`
below packages the consequence

```
∑_{λ<0} λ² ≤ δ_n * ∑ i |λ_i (n)|.
```

Since `∑ i |λ_i| ≤ √(m n) * sqrt (∑ i λ_i²)` (Cauchy–Schwarz on the abs-sum)
and `∑ i λ_i² → ∑' j, lam j²` is the `htr2` input (already convergent, and
supplied by the actual model through the weighted-correlation-energy form), the
negative mass vanishes as soon as `δ_n * √(m n) → 0`.  The scale `δ_n` is
produced by `Hurst.EigenvaluePerturbation.abs_trace_pow_sub_le_l2_opNorm`
(`|tr(A^k) − tr(B^k)| ≤ m·k·(max‖A‖‖B‖)^(k-1)·‖A−B‖`): a rate
`‖A_n − B_n‖ = O(m_n^{-1/2 − η})` for the perturbation of the actual matrix
against the Riesz limit matrix is exactly what the `hPert` mesh-energy
hypothesis of `actualQ1EigenvaluePowerSums_tendsto` measures.  THIS is where
the `hPert` rate enters the signed packaging: without a rate, `δ_n ≥ 0`
together with `λ_i ≥ −δ_n` alone cannot force `∑_{neg} λ² → 0` (the count of
negative eigenvalues may grow like `m n`).

Main contents (bottom-up):

* `centeredSpectralSquares_sub_abs_eq` : the pointwise negative-part identity;
* `sum_c_sub_abs_sq_eq_four_mul_min_sq` : `∑ (c i − |c i|)² = 4 ∑ (min (c i) 0)²`;
* `sum_min_sq_le_delta_mul_absSum` : the H1-form bound of the negative mass;
* `eigenvalues_negMass_le_delta_mul_absSum` : the same bound for Hermitian
  eigenvalues under PSD domination (`hPert` entry point);
* `centeredSpectralSquares_tendsto_secondChaos_of_absMatching_and_negMass` :
  Slutsky rung — statistic of `|λ|` converging + vanishing negative mass ⇒
  statistic of `λ` converging (same target law);
* `centeredSpectralSquares_tendsto_secondChaos_of_signedMatching` : the full
  signed packaging at the coefficient level, consuming exactly the
  `paddedAbsRearranged_tendsto` / `actualQ1EigenvaluePowerSums_tendsto` output
  shape `padRearranged (|λ|) → lam`, the trace-square input, and `hNegMass`;
* `centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching` : matrix level;
* `gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching` : the
  statistic-level endpoint, replacing the raw-eigenvalue hypothesis of
  `Hurst.SpectralMatchingInterface.gaussianLogQuadraticStatistic_tendsto_
  secondChaos_of_decreasing_matching` by the signed matching data.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace Hurst

/-! ## Deterministic core: the negative-part decomposition -/

/-- **Pointwise negative-part identity.**  Under the same Gaussian coordinates,
the centered spectral-square statistic of a coefficient vector and of its
absolute value differ by exactly the negative-part statistic with coefficient
`c i - |c i|` (supported on the negative eigenvalues). -/
theorem centeredSpectralSquares_sub_abs_eq {m : ℕ} (c : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    centeredSpectralSquares c x - centeredSpectralSquares (fun i => |c i|) x
      = centeredSpectralSquares (fun i => c i - |c i|) x := by
  unfold centeredSpectralSquares
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `∑ (c i − |c i|)² = 4 * ∑ (min (c i) 0)²`: the squared negative-part mass,
up to the fixed factor `4`. -/
theorem sum_c_sub_abs_sq_eq_four_mul_min_sq {m : ℕ} (c : Fin m → ℝ) :
    (∑ i, (c i - |c i|) ^ 2) = 4 * ∑ i, (min (c i) 0) ^ 2 := by
  have hterm : ∀ i : Fin m, (c i - |c i|) ^ 2 = 4 * (min (c i) 0) ^ 2 := by
    intro i
    by_cases h : 0 ≤ c i
    · have habs : c i - |c i| = 0 := by rw [abs_of_nonneg h]; ring
      have hmin : min (c i) 0 = 0 := min_eq_right (by linarith)
      rw [habs, hmin]
      simp
    · have habs : c i - |c i| = 2 * c i := by
        rw [abs_of_nonpos (by linarith : c i ≤ 0)]; ring
      have hmin : min (c i) 0 = c i := min_eq_left (by linarith)
      rw [habs, hmin]
      ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.mul_sum]

/-- **The H1-form bound of the negative mass.**  If every coefficient is at
least `-δ` then the squared negative-part mass is bounded by `δ` times the
total absolute mass.  Note that without a RATE on `δ` this cannot force the
negative mass to vanish (the count of negative entries may grow), which is why
`hNegMass` is kept as an explicit hypothesis of the signed packaging. -/
theorem sum_min_sq_le_delta_mul_absSum {m : ℕ} (c : Fin m → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h : ∀ i, -δ ≤ c i) :
    (∑ i, (min (c i) 0) ^ 2) ≤ δ * ∑ i, |c i| := by
  have hterm : ∀ i, (min (c i) 0) ^ 2 ≤ δ * |c i| := by
    intro i
    by_cases hci : 0 ≤ c i
    · have hmin : min (c i) 0 = 0 := min_eq_right (by linarith)
      rw [hmin]
      simpa using mul_nonneg hδ0 (abs_nonneg (c i))
    · have hmin : min (c i) 0 = c i := min_eq_left (by linarith)
      have habsle : |c i| ≤ δ := by
        rw [abs_of_nonpos (by linarith : c i ≤ 0)]
        have := h i
        linarith
      rw [hmin]
      calc (c i) ^ 2 = |c i| * |c i| := by
            rw [abs_of_nonpos (by linarith : c i ≤ 0)]; ring
        _ ≤ δ * |c i| := mul_le_mul_of_nonneg_right habsle (abs_nonneg (c i))
  calc ∑ i, (min (c i) 0) ^ 2 ≤ ∑ i, δ * |c i| :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = δ * ∑ i, |c i| := by rw [Finset.mul_sum]

/-- **The `hPert` entry point of the signed packaging.**  For Hermitian `A`
whose eigenvalues dominate `-δ` because the comparison matrix `B` is PSD and
`‖A − B‖ ≤ δ` (both supplied by the actual model: `B` is the Riesz limit
matrix, and `δ` is governed by `abs_trace_pow_sub_le_l2_opNorm` against the
`hPert` mesh-energy scale), the negative eigenvalue mass obeys the H1-form
bound.  Combining with Cauchy–Schwarz (`∑ |λ| ≤ √m * sqrt (∑ λ²)`) and the
convergence of `∑ λ²` (the `htr2` input), the smallness `hNegMass` of the
signed packaging reduces to the RATE `δ_n * √(m n) → 0`. -/
theorem eigenvalues_negMass_le_delta_mul_absSum {m : ℕ} (δ : ℝ) (hδ0 : 0 ≤ δ)
    {A B : Matrix (Fin m) (Fin m) ℝ} (hB : B.PosSemidef) (hA : A.IsHermitian)
    (hop : ‖A - B‖ ≤ δ) :
    (∑ i, (min (hA.eigenvalues i) 0) ^ 2) ≤ δ * ∑ i, |hA.eigenvalues i| :=
  sum_min_sq_le_delta_mul_absSum _ hδ0 fun i =>
    eigenvalues_ge_neg_delta_of_posSemidef_of_norm_le hB hA hop i

/-! ## Slutsky rung: vanishing negative mass transfers the limit law -/

/-- **Slutsky rung of the signed packaging.**  If the statistic of the
absolute-value coefficient array converges in distribution to the second-chaos
law and the negative-part mass vanishes, then the statistic of the SIGNED
array converges to the same law.  The two statistics live on the same
standard-Gaussian space and differ by `centeredSpectralSquares (c n - |c n|)`,
whose second moment is exactly `8 * ∑ (min (c n i) 0)²`; the L2 smallness is
promoted by the triangular L1 transfer. -/
theorem centeredSpectralSquares_tendsto_secondChaos_of_absMatching_and_negMass
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (_hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hAbsStat : TendstoInDistribution (fun n ↦ centeredSpectralSquares (fun i => |c n i|))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P')
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ↦ centeredSpectralSquares (c n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  -- the perturbation statistic and its exact second moment
  have hpoint : ∀ n,
      (centeredSpectralSquares (c n) - centeredSpectralSquares (fun i => |c n i|))
        = centeredSpectralSquares (fun i => c n i - |c n i|) :=
    fun n => funext fun x => centeredSpectralSquares_sub_abs_eq (c n) x
  have hmemLp : ∀ n, MemLp (centeredSpectralSquares (fun i => c n i - |c n i|)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin (m n)))) :=
    fun n => centeredSpectralSquares_memLp_two (fun i => c n i - |c n i|)
  have hI2 : Tendsto (fun n => ∫ x, (centeredSpectralSquares
        (fun i => c n i - |c n i|) x) ^ 2
      ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n))))) atTop (𝓝 0) := by
    have hstep : ∀ n, ∫ x, (centeredSpectralSquares
        (fun i => c n i - |c n i|) x) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n))))
        = 8 * ∑ i : Fin (m n), (min (c n i) 0) ^ 2 := by
      intro n
      rw [centeredSpectralSquares_secondMoment (fun i => c n i - |c n i|),
        sum_c_sub_abs_sq_eq_four_mul_min_sq]
      ring
    have h8 := hNegMass.const_mul 8
    rw [mul_zero] at h8
    exact Tendsto.congr (fun n => (hstep n).symm) h8
  -- L1 smallness of the perturbation
  have hL1 : Tendsto (fun n => ∫ x, |centeredSpectralSquares
        (fun i => c n i - |c n i|) x|
      ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n))))) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (∫ x,
        (centeredSpectralSquares (fun i => c n i - |c n i|) x) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n)))))) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.comp hI2
    have hsqrt0 : Tendsto (fun n => Real.sqrt (∫ x,
        (centeredSpectralSquares (fun i => c n i - |c n i|) x) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n)))))) atTop (𝓝 0) := by
      convert hsqrt using 2
      exact Real.sqrt_zero.symm
    have hnonneg : ∀ n, (0 : ℝ) ≤ ∫ x,
        |centeredSpectralSquares (fun i => c n i - |c n i|) x|
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n)))) :=
      fun n => integral_nonneg fun _ => abs_nonneg _
    have hle : ∀ n, ∫ x,
        |centeredSpectralSquares (fun i => c n i - |c n i|) x|
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n))))
        ≤ Real.sqrt (∫ x,
          (centeredSpectralSquares (fun i => c n i - |c n i|) x) ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n))))) :=
      fun n => integral_abs_le_sqrt_second_moment _ _ (hmemLp n)
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero hsqrt0
      (Eventually.of_forall fun n => hnonneg n)
      (Eventually.of_forall fun n => hle n)
  -- rewrite the difference statistic and apply the triangular L1 transfer
  have hY : ∀ n, AEMeasurable (centeredSpectralSquares (c n))
      (stdGaussian (EuclideanSpace ℝ (Fin (m n)))) :=
    fun n => (centeredSpectralSquares_memLp_two (c n)).aemeasurable
  have hDint : ∀ᶠ n in atTop, Integrable
      (fun x => centeredSpectralSquares (c n) x
        - centeredSpectralSquares (fun i => |c n i|) x)
      (stdGaussian (EuclideanSpace ℝ (Fin (m n)))) := by
    filter_upwards [] with n
    have hd : (fun x => centeredSpectralSquares (c n) x
        - centeredSpectralSquares (fun i => |c n i|) x)
        = centeredSpectralSquares (fun i => c n i - |c n i|) := hpoint n
    rw [hd]
    exact (hmemLp n).integrable (by norm_num)
  have hL1' : Tendsto (fun n => ∫ x, |centeredSpectralSquares (c n) x
      - centeredSpectralSquares (fun i => |c n i|) x|
      ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n))))) atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => ?_) hL1
    exact (congrArg (fun f => ∫ x, |f x| ∂(stdGaussian (EuclideanSpace ℝ (Fin (m n)))))
      (hpoint n)).symm
  exact triangular_L1_distribution_transfer
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    (fun n => centeredSpectralSquares (fun i => |c n i|))
    (fun n => centeredSpectralSquares (c n)) Q hAbsStat hY hDint hL1'

/-! ## The signed packaging: |λ|-rearrangement → TendstoInDistribution -/

/-- **The signed packaging (coefficient level).**  This is the reduction
theorem: given

* `hAbs` — the padded decreasing rearrangement of the ABSOLUTE coefficients
  converges to `lam` (exactly the output shape of
  `Hurst.EvenPeeling.paddedAbsRearranged_tendsto`, instantiated by
  `Hurst.ActualQuadratureConfluence.actualQ1EigenvaluePowerSums_tendsto` on the
  actual q1 eigenvalues);
* `htr2` — the coefficient-square sums converge to the series (at even power
  transparency `∑ c² = ∑ |c|²`, this is the `k = 2` instance of the even
  power-sum convergence);
* `hNegMass` — the squared negative-spectrum mass vanishes (see the module
  docstring for its discharge from the `hPert` rate);

the centered spectral-square statistic of the SIGNED array converges in
distribution to the second-chaos law of `lam`. -/
theorem centeredSpectralSquares_tendsto_secondChaos_of_signedMatching
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
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ↦ centeredSpectralSquares (c n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  -- the decreasingly permuted absolute coefficients, inlined
  have hcoeffAbs : ∀ j : ℕ, Tendsto (fun n ↦
      if hj : j < m n then
        (fun j' => |c n j'|)
          ((decreasingSpectralPerm (fun j' => |c n j'|)) ⟨j, hj⟩)
      else 0)
      atTop (𝓝 (lam j)) := by
    intro j
    refine Tendsto.congr (fun _ => ?_) (hAbs j)
    rfl
  have htr2p : Tendsto (fun n ↦ ∑ i : Fin (m n),
      ((fun j => |c n j|)
        ((decreasingSpectralPerm (fun j => |c n j|)) i)) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2)) := by
    refine Tendsto.congr (fun n => ?_) htr2
    calc ∑ i : Fin (m n), (c n i) ^ 2
        = ∑ i : Fin (m n), |c n i| ^ 2 :=
          Finset.sum_congr rfl fun i _ => (sq_abs (c n i)).symm
      _ = ∑ i : Fin (m n), (fun i => |c n i| ^ 2)
            ((decreasingSpectralPerm (fun j => |c n j|)) i) :=
          (Equiv.sum_comp (decreasingSpectralPerm (fun j => |c n j|))
            (fun i => |c n i| ^ 2)).symm
      _ = ∑ i : Fin (m n),
            ((fun j => |c n j|)
              ((decreasingSpectralPerm (fun j => |c n j|)) i)) ^ 2 := rfl
  -- the |λ|-statistic converges through the padded_l2 endpoint
  obtain ⟨e, he, htail⟩ := spectralTailBound_of_padded_coefficient_convergence
    m (fun n i => (fun j => |c n j|)
      ((decreasingSpectralPerm (fun j => |c n j|)) i))
    lam hQ.2.1 hm hcoeffAbs htr2p
  have hAbsStatP := centeredSpectralSquares_tendsto_secondChaos_of_padded_l2
    m (fun n i => (fun j => |c n j|)
      ((decreasingSpectralPerm (fun j => |c n j|)) i))
    P' Q lam hQ hm hcoeffAbs e he htail
  -- transport along the decreasing permutation (row law is unchanged)
  have hAbsStat : TendstoInDistribution
      (fun n ↦ centeredSpectralSquares (fun i => |c n i|))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
    refine tendstoInDistribution_of_identDistrib_rows_varying
      (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n))))
      (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
      (fun n => centeredSpectralSquares (fun i => |c n i|))
      (fun n => centeredSpectralSquares
        (fun i => (fun j => |c n j|)
          ((decreasingSpectralPerm (fun j => |c n j|)) i)))
      Q atTop ?_ hAbsStatP
    intro n
    exact centeredSpectralSquares_permute_identDistrib
      (decreasingSpectralPerm (fun j => |c n j|)) (fun i => |c n i|)
  exact centeredSpectralSquares_tendsto_secondChaos_of_absMatching_and_negMass
    m c P' Q lam hQ hAbsStat hNegMass

/-- **The signed packaging (matrix level).**  Same data as
`centeredSpectralSquares_tendsto_secondChaos_of_signedMatching`, stated on the
eigenvalues of a Hermitian array; the conclusion is the full
`TendstoInDistribution` of the centered matrix quadratics.  On the actual
model, `hAbs` is supplied by
`Hurst.ActualQuadratureConfluence.actualQ1EigenvaluePowerSums_tendsto` (whose
conclusion is literally `padRearranged (fun i ↦ |eigenvalues i|) → lam`), the
`htr2` input by the weighted-correlation-energy convergence (via
`weightedFeatureQuadraticMatrix_sum_eigenvalues_sq` or, at the matrix level,
`hermitian_trace_square_eq_sum_eigenvalues_sq`), and `hNegMass` by the
`hPert`-rate reduction documented in the module docstring. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching
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
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n),
      (min ((hA n).eigenvalues i) 0) ^ 2) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  refine tendstoInDistribution_of_identDistrib_rows_varying
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n))))
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    (fun n => centeredMatrixQuadratic (A n))
    (fun n => centeredSpectralSquares ((hA n).eigenvalues)) Q atTop ?_ ?_
  · intro n
    exact centeredMatrixQuadratic_identDistrib_eigenvalueSquares (hA n)
  · exact centeredSpectralSquares_tendsto_secondChaos_of_signedMatching
      m (fun n => (hA n).eigenvalues) P' Q lam hQ hm hAbs htr2 hNegMass

section WeightedFeature

variable {iota E : Type*} [Fintype iota] [DecidableEq iota]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The signed packaging (statistic level).**  The signed replacement of
`Hurst.SpectralMatchingInterface.gaussianLogQuadraticStatistic_tendsto_
secondChaos_of_decreasing_matching`: the raw-eigenvalue decreasing-matching
hypothesis `hcoeff` is replaced by the SIGNED matching data —
`hAbs` (the padded rearrangement of the absolute eigenvalues converges to
`lam`; this is what `actualQ1EigenvaluePowerSums_tendsto` delivers), the
weighted-correlation-energy input `htr2` (identical to the original
endpoint's), and the single explicit smallness hypothesis `hNegMass` on the
negative eigenvalues (discharge documented in the module docstring: `λ ≥ −δ_n`
by PSD domination, `∑_{neg} λ² ≤ δ_n ∑|λ| ≤ δ_n √m √(∑λ²)`, so the `hPert`
rate `δ_n √m → 0` finishes). -/
theorem gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching
    (m : ℕ → ℕ)
    (v : ℕ → iota → E) (w : ∀ n, Fin (m n) → ℝ)
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ iota)
    (ha : ∀ (n : ℕ) (k : Fin (m n)), ∑ i, a n k i • v n i ≠ 0)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hm : Tendsto m atTop atTop)
    (hAbs : ∀ j : ℕ, Tendsto (fun n ↦ padRearranged (fun i : Fin (m n) =>
      |(weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i|) j)
      atTop (𝓝 (lam j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), ∑ j : Fin (m n),
        w n i * w n j * (featureCorrelation (v n) (a n i) (a n j)) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2)))
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n),
      (min ((weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic (v n) (w n) (a n) x)
      atTop Q (fun n => featureGaussian (v n)) P' := by
  have htr2ev : Tendsto (fun n ↦ ∑ i : Fin (m n),
      (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2)) := by
    refine Tendsto.congr (fun n => ?_) htr2
    exact (weightedFeatureQuadraticMatrix_sum_eigenvalues_sq (v n) (a n) (w n)).symm
  have hmatrix := centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching
    m (fun n => weightedFeatureQuadraticMatrix (v n) (a n) (w n))
    (fun n => weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n))
    P' Q lam hQ hm hAbs htr2ev hNegMass
  refine tendstoInDistribution_of_identDistrib_rows_varying
    (fun n => featureGaussian (v n))
    (fun n => stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P'
    (fun n x => gaussianLogQuadraticStatistic (v n) (w n) (a n) x)
    (fun n => centeredMatrixQuadratic (weightedFeatureQuadraticMatrix (v n) (a n) (w n)))
    Q atTop ?_ hmatrix
  intro n
  exact (gaussianLogQuadraticStatistic_identDistrib_normalizedCoordinates
      (v n) (a n) (w n)).trans
    (centeredSpectralSquares_featureGaussian_identDistrib_centeredMatrixQuadratic
      (v n) (a n) (w n) (ha n))

end WeightedFeature

end Hurst
