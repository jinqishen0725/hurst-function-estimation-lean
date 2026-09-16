import Hurst.NegMassUI
import Hurst.NonnegWeightNegMass

/-!
# The `hNegMass` discharge decision matrix

`Hurst.SignedInterfaceFinal.centeredMatrixQuadratic_tendsto_secondChaos_of_
signedMatching` consumes, besides the matching data (`hAbs` on the absolute
eigenvalues and `htr2` on the squares), the single smallness hypothesis

```
hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min ((hA n).eigenvalues i) 0) ^ 2)
  atTop (𝓝 0).
```

This file lands the DECISION MATRIX: for each regime of the actual model it
states and proves whether — and how — `hNegMass` is discharged.  The matrix:

* **Row 0 — the series-law regime (the constructed space).**  For the fixed
  law `λ` of `Hurst.P4GaussianSeriesLaw` (whose second-chaos series is
  CONSTRUCTED as the `L²` limit `Q`, so the signed packaging is not consumed
  there at all) the coefficient-level negative-mass control is the
  unconditional TAIL form `negMass_tail_tendsto` / `negMass_tail_tendsto'` of
  `Hurst.NegMassUI`.  Two honest observations are formalized:

  - `negMass_prefix_tendsto_tsum`: the PREFIX negative mass
    `∑_{j<K} (min λ_j 0)²` converges to the TOTAL negative mass
    `∑' (min λ 0)²` — NOT to `0` in general (it is a monotone bounded
    sequence), so the `hNegMass` → 0 requirement can never be read off the
    prefixes of a FIXED law;
  - `negMass_prefix_tendsto_zero_iff_nonneg`: the prefix negative mass tends
    to `0` **iff** the fixed law is entrywise nonnegative — the trivial
    corner of row 0;
  - `hNegMass_of_tailSpectrum`: the genuine bridge — if the stage-`n`
    spectrum `c n` is termwise dominated by the shifted tail of the fixed law
    beyond cutoffs `K n` (`min (c n i) 0² ≤ min (lam (K n + i)) 0²`), then
    `hNegMass` holds with NO analytic input, by `negMass_tail_tendsto'`.

* **Row A — the nonneg-weights regime (route (a), landed in
  `Hurst.NonnegWeightNegMass`).**  Entrywise nonnegativity of the array gives
  `min (c n i) 0 = 0` pointwise, so `hNegMass ≡ 0` trivially
  (`hNegMass_zero_of_nonnegWeights`, re-consumed below).  On the actual chain
  this is reached through `Hurst.WeightedMatrixPSD`: nonnegative weights make
  the weighted feature matrix a PSD congruence, whence
  `weightedFeatureQuadraticMatrix_eigenvalues_nonneg`.

* **Row B — the genuinely signed regime (route (b), the conditional
  discharge).**  For genuinely signed arrays `hNegMass` does NOT vanish
  identically and needs the frozen-perturbation rate.  The H1-form bound
  `eigenvalues_negMass_le_delta_mul_absSum` of `Hurst.SignedInterfaceFinal`
  gives `∑_{neg} λ² ≤ δ_n ∑ |λ|`, and Cauchy–Schwarz on the abs-sum
  (`sum_abs_le_sqrt_card_mul_sqrt_sum_sq`) turns this into

  ```
  ∑_{neg} λ² ≤ δ_n * √(m n) * √(∑ λ²).
  ```

  With the square mass bounded (which the `htr2` convergence of the packaging
  supplies via `exists_bound_of_tendsto`) the RATE `δ_n * √(m n) → 0`
  discharges `hNegMass`: `hNegMass_of_delta_sqrt_rate` at the coefficient
  level and, via the PSD-domination shift
  `eigenvalues_ge_neg_delta_of_posSemidef_of_norm_le`, at the eigenvalue
  level.  HONEST CAVEAT: without the rate, `δ_n ≥ 0` alone cannot force the
  negative mass to vanish (the count of negative eigenvalues may grow like
  `m n`); the rate is kept as an explicit hypothesis — this is exactly the
  documented `hPert` boundary of `Hurst.SignedInterfaceFinal` /
  `Hurst.ActualQuadratureFinal`.

The decision theorems: `hNegMass_of_nonnegWeights_or_delta_sqrt_rate`
(either regime discharges `hNegMass`), and the packaging-level endpoints
`centeredSpectralSquares_tendsto_secondChaos_of_signedMatching_of_regime` /
`centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching_of_regime` —
the signed consumption theorem with `hNegMass` replaced by the explicit
regime disjunction.  On the actual chain the nonneg branch of the matrix
level is already unconditional (`centeredMatrixQuadratic_tendsto_
secondChaos_of_nonnegWeights` of `Hurst.NonnegWeightNegMass`).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace Hurst

/-! ## Row 0: the series-law regime (the NegMassUI tail forms) -/

/-- **Row 0, prefix form.**  The prefix negative mass of a fixed
square-summable law converges to the TOTAL negative mass — not to `0` in
general. -/
theorem negMass_prefix_tendsto_tsum (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, (min (lambda j) 0) ^ 2)
      atTop (𝓝 (∑' j : ℕ, (min (lambda j) 0) ^ 2)) :=
  (summable_min_sq lambda hlambda).hasSum.tendsto_sum_nat

/-- **Row 0, trivial corner.**  The prefix negative mass tends to `0` iff the
fixed law is entrywise nonnegative: if some `λ_j < 0` the prefixes converge
to the positive total mass instead. -/
theorem negMass_prefix_tendsto_zero_iff_nonneg (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    (Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, (min (lambda j) 0) ^ 2)
      atTop (𝓝 0)) ↔ ∀ j, 0 ≤ lambda j := by
  constructor
  · intro htendsto
    have huniq : (∑' j : ℕ, (min (lambda j) 0) ^ 2) = 0 :=
      tendsto_nhds_unique (negMass_prefix_tendsto_tsum lambda hlambda) htendsto
    intro j
    by_contra hneg
    have hlt : lambda j < 0 := not_le.1 hneg
    have hterm : (0 : ℝ) < (min (lambda j) 0) ^ 2 := by
      rw [min_eq_left (le_of_lt hlt)]
      exact sq_pos_of_ne_zero (show (lambda j : ℝ) ≠ 0 by linarith)
    have hle := (summable_min_sq lambda hlambda).sum_le_tsum {j}
      (fun i _ => sq_nonneg _)
    rw [Finset.sum_singleton, huniq] at hle
    linarith
  · intro hall
    have h0 : ∀ K : ℕ, (∑ j ∈ Finset.range K, (min (lambda j) 0) ^ 2) = 0 := by
      intro K
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [min_eq_right (hall j)]
      simp
    exact Tendsto.congr (fun K => (h0 K).symm) tendsto_const_nhds

/-- **Row 0, the tail bridge.**  If the stage-`n` spectrum `c n` is termwise
dominated, on the squared negative parts, by the shifted tail of the fixed
law beyond cutoffs `K n → ∞`, then `hNegMass` holds with NO analytic input:
the negative mass is dominated by the tail mass
`∑' j, (min (lam (j + K n)) 0)²`, which `negMass_tail_tendsto` (composed with
`K`) sends to `0`. -/
theorem hNegMass_of_tailSpectrum {m : ℕ → ℕ} (K : ℕ → ℕ) (lam : ℕ → ℝ)
    (hlambda : Summable fun j => (lam j) ^ 2)
    (hK : Tendsto K atTop atTop) (c : ∀ n, Fin (m n) → ℝ)
    (hdom : ∀ (n : ℕ) (i : Fin (m n)),
      (min (c n i) 0) ^ 2 ≤ (min (lam (i.val + K n)) 0) ^ 2) :
    Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0) := by
  have hle : ∀ n : ℕ, (∑ i : Fin (m n), (min (c n i) 0) ^ 2)
      ≤ (∑' j : ℕ, (min (lam (j + K n)) 0) ^ 2) := by
    intro n
    have hshift : Summable (fun j : ℕ => (min (lam (j + K n)) 0) ^ 2) :=
      (summable_nat_add_iff (f := fun j => (min (lam j) 0) ^ 2) (K n)).mpr
        (summable_min_sq lam hlambda)
    calc ∑ i : Fin (m n), (min (c n i) 0) ^ 2
        ≤ ∑ i : Fin (m n), (min (lam (i.val + K n)) 0) ^ 2 :=
          Finset.sum_le_sum fun i _ => hdom n i
      _ = ∑ j ∈ Finset.range (m n), (min (lam (j + K n)) 0) ^ 2 :=
          Fin.sum_univ_eq_sum_range (fun j => (min (lam (j + K n)) 0) ^ 2) (m n)
      _ ≤ ∑' j : ℕ, (min (lam (j + K n)) 0) ^ 2 :=
          hshift.sum_le_tsum (Finset.range (m n)) (fun j _ => sq_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((negMass_tail_tendsto lam).comp hK)
    (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Eventually.of_forall hle)

/-! ## Auxiliary: boundedness from convergence -/

/-- A convergent real sequence is globally bounded above (extracting the
bounded square mass from the `htr2` convergence of the packaging). -/
theorem exists_bound_of_tendsto {f : ℕ → ℝ} {x : ℝ} (hf : Tendsto f atTop (𝓝 x)) :
    ∃ B : ℝ, ∀ n, f n ≤ B := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hf (1 : ℝ) one_pos
  have hxnn : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hxa : x ≤ |x| := le_abs_self x
  have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range N, |f i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨(∑ i ∈ Finset.range N, |f i|) + |x| + 1, fun n => ?_⟩
  by_cases hn : n < N
  · have h1 : f n ≤ |f n| := le_abs_self _
    have h2 : |f n| ≤ ∑ i ∈ Finset.range N, |f i| :=
      Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 hn)
    linarith
  · have hn' : N ≤ n := le_of_not_gt hn
    have hdist : dist (f n) x < 1 := hN n hn'
    have hab : |f n - x| < 1 := by rwa [Real.dist_eq] at hdist
    obtain ⟨_, hlt⟩ := abs_lt.1 hab
    linarith

/-! ## Row B: the signed regime — the rate discharge -/

/-- **Cauchy–Schwarz on the abs-sum.**  `∑ |c i| ≤ √(card · ∑ c²)`: the
count-of-negative-eigenvalues factor of the H1-form bound. -/
theorem sum_abs_le_sqrt_card_mul_sqrt_sum_sq {m : ℕ} (c : Fin m → ℝ) :
    ∑ i, |c i| ≤ Real.sqrt ((m : ℝ) * ∑ i, (c i) ^ 2) := by
  have hsum : ∑ i, (|c i|) ^ 2 = ∑ i, (c i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs (c i)
  have h1 : (∑ i, |c i|) ^ 2
      ≤ ((Finset.univ : Finset (Fin m)).card : ℝ) * ∑ i, (|c i|) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hsum, Finset.card_fin m] at h1
  have hnn : (0 : ℝ) ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc ∑ i, |c i| = Real.sqrt ((∑ i, |c i|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((m : ℝ) * ∑ i, (c i) ^ 2) := Real.sqrt_le_sqrt h1

/-- **Route (b), per-array form.**  The H1-form bound
(`sum_min_sq_le_delta_mul_absSum`) with the abs-sum made explicit:
`∑ (min c 0)² ≤ δ · √(card · ∑ c²)`. -/
theorem sum_min_sq_le_delta_mul_sqrt_bound {m : ℕ} (c : Fin m → ℝ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hge : ∀ i, -δ ≤ c i) :
    (∑ i, (min (c i) 0) ^ 2) ≤ δ * Real.sqrt ((m : ℝ) * ∑ i, (c i) ^ 2) :=
  (sum_min_sq_le_delta_mul_absSum c hδ0 hge).trans
    (mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_mul_sqrt_sum_sq c) hδ0)

/-- **Route (b): the signed regime, conditional on the rate.**  If every
entry of the stage-`n` array dominates `-δ n` (on the actual chain: the PSD
domination `eigenvalues_ge_neg_delta_of_posSemidef_of_norm_le`), the square
mass is bounded, and the RATE `δ n * √(m n)` tends to `0`, then `hNegMass`
follows:

```
∑ (min (c n i) 0)² ≤ δ n ∑ |c n i| ≤ δ n √(m n) √(∑ c²) → 0.
```

Without the rate the discharge is FALSE in general (`δ n ≥ 0` alone allows
the negative count to grow like `m n`); the rate is exactly the documented
`hPert` boundary of `Hurst.SignedInterfaceFinal`. -/
theorem hNegMass_of_delta_sqrt_rate {m : ℕ → ℕ} (c : ∀ n, Fin (m n) → ℝ)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n)
    (hge : ∀ (n : ℕ) (i : Fin (m n)), -δ n ≤ c n i)
    (hsq : ∃ B : ℝ, ∀ n, ∑ i : Fin (m n), (c n i) ^ 2 ≤ B)
    (hrate : Tendsto (fun n ↦ δ n * Real.sqrt ((m n : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hsq
  have hstep : ∀ n : ℕ, (∑ i : Fin (m n), (min (c n i) 0) ^ 2)
      ≤ Real.sqrt B * (δ n * Real.sqrt ((m n : ℝ))) := by
    intro n
    have h2 : Real.sqrt ((m n : ℝ) * ∑ i : Fin (m n), (c n i) ^ 2)
        ≤ Real.sqrt ((m n : ℝ) * B) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hB n) (by positivity))
    have h3 : Real.sqrt ((m n : ℝ) * B)
        = Real.sqrt (m n : ℝ) * Real.sqrt B :=
      Real.sqrt_mul (by positivity) B
    calc ∑ i : Fin (m n), (min (c n i) 0) ^ 2
        ≤ δ n * Real.sqrt ((m n : ℝ) * ∑ i : Fin (m n), (c n i) ^ 2) :=
          sum_min_sq_le_delta_mul_sqrt_bound (c n) (hδ0 n) (fun i => hge n i)
      _ ≤ δ n * Real.sqrt ((m n : ℝ) * B) := mul_le_mul_of_nonneg_left h2 (hδ0 n)
      _ = Real.sqrt B * (δ n * Real.sqrt (m n : ℝ)) := by rw [h3]; ring
  have hprod : Tendsto
      (fun n ↦ Real.sqrt B * (δ n * Real.sqrt ((m n : ℝ)))) atTop (𝓝 0) := by
    have h := hrate.const_mul (Real.sqrt B)
    rw [mul_zero] at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Eventually.of_forall hstep)

/-- **Route (b) at the eigenvalue level (`hPert` entry point).**  For
Hermitian `A n` PSD-dominated by `Bm n` through the operator-norm shift
`‖A n − Bm n‖ ≤ δ n`, the eigenvalue array dominates `-δ n` termwise, so the
rate discharge applies verbatim to `(hA n).eigenvalues`. -/
theorem hNegMass_eigenvalues_of_delta_sqrt_rate {m : ℕ → ℕ}
    (A : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ) (hA : ∀ n, (A n).IsHermitian)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n)
    (Bm : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ) (hB : ∀ n, (Bm n).PosSemidef)
    (hop : ∀ n, ‖A n - Bm n‖ ≤ δ n)
    (hsq : ∃ B : ℝ, ∀ n, ∑ i : Fin (m n), ((hA n).eigenvalues i) ^ 2 ≤ B)
    (hrate : Tendsto (fun n ↦ δ n * Real.sqrt ((m n : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (m n),
      (min ((hA n).eigenvalues i) 0) ^ 2) atTop (𝓝 0) :=
  hNegMass_of_delta_sqrt_rate (fun n => (hA n).eigenvalues) δ hδ0
    (fun n i => eigenvalues_ge_neg_delta_of_posSemidef_of_norm_le (hB n) (hA n)
      (hop n) i)
    hsq hrate

/-! ## The decision matrix: either regime discharges `hNegMass` -/

/-- **THE DECISION (coefficient level).**  Under the bounded-square-mass side
condition, `hNegMass` is discharged in EITHER regime:

* **nonneg weights** (Row A): the sum is identically zero;
* **signed** (Row B): `c n i ≥ -δ n` with the rate `δ n * √(m n) → 0`.

No third regime is needed: Row 0 (the fixed series law) reduces to the
nonneg corner by `negMass_prefix_tendsto_zero_iff_nonneg` or to the tail
bridge `hNegMass_of_tailSpectrum`. -/
theorem hNegMass_of_nonnegWeights_or_delta_sqrt_rate {m : ℕ → ℕ}
    (c : ∀ n, Fin (m n) → ℝ)
    (hsq : ∃ B : ℝ, ∀ n, ∑ i : Fin (m n), (c n i) ^ 2 ≤ B)
    (href : (∀ (n : ℕ) (i : Fin (m n)), 0 ≤ c n i) ∨
      (∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧
        (∀ (n : ℕ) (i : Fin (m n)), -δ n ≤ c n i) ∧
        Tendsto (fun n ↦ δ n * Real.sqrt ((m n : ℝ))) atTop (𝓝 0))) :
    Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0) := by
  rcases href with hnn | ⟨δ, hδ0, hge, hrate⟩
  · exact hNegMass_zero_of_nonnegWeights c hnn
  · exact hNegMass_of_delta_sqrt_rate c δ hδ0 hge hsq hrate

/-! ## The decision theorems at the consumption level -/

/-- **The signed packaging with `hNegMass` decided (coefficient level).**
`centeredSpectralSquares_tendsto_secondChaos_of_signedMatching` with the
`hNegMass` hypothesis replaced by the regime disjunction: the matching data
`hAbs` / `htr2` plus EITHER entrywise nonnegativity OR the frozen-perturbation
rate `δ n * √(m n) → 0` suffice. -/
theorem centeredSpectralSquares_tendsto_secondChaos_of_signedMatching_of_regime
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
    (href : (∀ (n : ℕ) (i : Fin (m n)), 0 ≤ c n i) ∨
      (∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧
        (∀ (n : ℕ) (i : Fin (m n)), -δ n ≤ c n i) ∧
        Tendsto (fun n ↦ δ n * Real.sqrt ((m n : ℝ))) atTop (𝓝 0))) :
    TendstoInDistribution (fun n ↦ centeredSpectralSquares (c n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto htr2
  exact centeredSpectralSquares_tendsto_secondChaos_of_signedMatching
    m c P' Q lam hQ hm hAbs htr2
    (hNegMass_of_nonnegWeights_or_delta_sqrt_rate c ⟨B, hB⟩ href)

/-- **The signed packaging with `hNegMass` decided (matrix level).**
`centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching` with the
`hNegMass` hypothesis replaced by the regime disjunction:

* nonneg eigenvalues (Row A — on the actual chain, from
  `weightedFeatureQuadraticMatrix_eigenvalues_nonneg`); or
* the signed regime (Row B): a PSD comparison matrix `Bm n` with
  `‖A n − Bm n‖ ≤ δ n` (the `hPert` perturbation input) and the rate
  `δ n * √(m n) → 0`.

The square-mass boundedness needed by Row B is extracted from the `htr2`
convergence of the packaging. -/
theorem centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching_of_regime
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
    (href : (∀ (n : ℕ) (i : Fin (m n)), 0 ≤ (hA n).eigenvalues i) ∨
      (∃ (Bm : ∀ n, Matrix (Fin (m n)) (Fin (m n)) ℝ) (δ : ℕ → ℝ),
        (∀ n, (Bm n).PosSemidef) ∧ (∀ n, 0 ≤ δ n) ∧
        (∀ n, ‖A n - Bm n‖ ≤ δ n) ∧
        Tendsto (fun n ↦ δ n * Real.sqrt ((m n : ℝ))) atTop (𝓝 0))) :
    TendstoInDistribution (fun n ↦ centeredMatrixQuadratic (A n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  rcases href with hnn | ⟨Bm, δ, hBpsd, hδ0, hop, hrate⟩
  · exact
      centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching_of_nonnegEigenvalues
        m A hA P' Q lam hQ hm hAbs htr2 hnn
  · obtain ⟨B, hB⟩ := exists_bound_of_tendsto htr2
    exact centeredMatrixQuadratic_tendsto_secondChaos_of_signedMatching
      m A hA P' Q lam hQ hm hAbs htr2
      (hNegMass_eigenvalues_of_delta_sqrt_rate A hA δ hδ0 Bm hBpsd hop ⟨B, hB⟩
        hrate)

end Hurst
