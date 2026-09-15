import Hurst.FourthMomentAssembly
import Hurst.SignedInterfaceFinal
import Hurst.P4GaussianSeriesLaw

/-!
# Uniform-integrability corollaries of the fourth-moment identity

This file packages the uniform-integrability corollaries of the fourth-moment
identity of `Hurst.FourthMomentAssembly` for the partial sums
`S_K = ∑_{j<K} λ_j (Z_j² − 1)` of the Gaussian second-chaos series on the
constructed space `gaussianSeqMeasure` of `Hurst.P4GaussianSeriesLaw`, in the
coefficient shapes consumed by the signed packaging
(`hNegMass` of `Hurst.SignedInterfaceFinal`: the sums
`∑ (min c i 0)²` of squared negative parts).

Main contents:

* `fourthMoment_partialSum_le_uniform` — **(b) the uniform `L⁴` bound**: for a
  square-summable coefficient sequence `λ` the fourth moments of the partial
  sums are bounded uniformly in the cutoff `K`,
  `∀ K, E[S_K⁴] ≤ 60 * (∑' j, λ_j²)²`.  Direct from the landed
  `fourthMoment_partialSum_le` (`E[S_K⁴] ≤ 60 (∑_{j<K} λ²)²`) plus the
  monotone convergence of the partial sums of `λ²` to `∑' λ²`
  (`sum_range_sq_tendsto_tsum`, its pointwise `sum_le_tsum` form here).  This
  is the uniform-integrability certificate for the signed consumption.
* `fourthMoment_partialSum_le_uniform_abs` — the same bound in the
  `E|S_K|⁴` shape (the integrand is an even power, so the two agree
  pointwise).
* `negMass_partial_le` — **(a) partial form**: the `hNegMass`-style negative
  mass of every prefix is dominated by the full square mass,
  `∑_{j<K} (min λ_j 0)² ≤ ∑' j, λ_j²`.
* `negMass_tsum_le` — the full-series domination
  `∑' (min λ 0)² ≤ ∑' λ²`.
* `negMass_tail_tendsto` — **(a) tail form**: the `hNegMass`-style sum for the
  TAIL coefficients tends to zero,
  `Tendsto (fun K ↦ ∑' j, (min λ_{K+j} 0)²) atTop (𝓝 0)`.
* `exists_gaussSeries_L2limit_abs` — the landed `L²` tail of the series
  (`E[(Q − S_K)²] → 0`, third field of `exists_gaussSeries_L2limit`) restated
  in the `∫ |Q − S_K|² → 0` shape, so that the negative-part contribution of
  the tail has a single consistent interface together with
  `negMass_tail_tendsto`.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-! ### Pointwise negative-mass domination -/

/-- The squared negative part of a coefficient is dominated by its square. -/
private theorem minSq_le_sq (c : ℝ) : (min c 0) ^ 2 ≤ c ^ 2 := by
  by_cases h : 0 ≤ c
  · have h0 : (min c 0) ^ 2 = (0 : ℝ) := by
      rw [min_eq_right h]
      norm_num
    rw [h0]
    exact sq_nonneg c
  · rw [min_eq_left (le_of_lt (not_le.1 h))]

/-- Square-summability of the coefficient sequence implies summability of the
squared negative parts (the `hNegMass` array), by pointwise domination. -/
theorem summable_min_sq (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    Summable fun j => (min (lambda j) 0) ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => minSq_le_sq (lambda j)) hlambda

/-! ### (b) The uniform `L⁴` bound -/

/-- Monotone convergence of the partial sums of `λ²` to `∑' λ²`. -/
theorem sum_range_sq_tendsto_tsum (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, (lambda j) ^ 2)
      atTop (𝓝 (∑' j : ℕ, (lambda j) ^ 2)) :=
  hlambda.hasSum.tendsto_sum_nat

set_option maxHeartbeats 1000000 in
/-- **(b) The uniform `L⁴` bound.**  For a square-summable coefficient
sequence the fourth moments of the Gaussian second-chaos partial sums are
bounded uniformly in the cutoff:

`∀ K, E[S_K⁴] ≤ 60 * (∑' j, λ_j²)²`.

This is the uniform-integrability certificate for the signed consumption: the
landed `fourthMoment_partialSum_le` bound `E[S_K⁴] ≤ 60 (∑_{j<K} λ²)²` is made
uniform in `K` by the domination `∑_{j<K} λ² ≤ ∑' λ²`. -/
theorem fourthMoment_partialSum_le_uniform (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) (K : ℕ) :
    (∫ x : ℕ → ℝ, (∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) ^ 4
        ∂gaussianSeqMeasure)
      ≤ 60 * (∑' j : ℕ, (lambda j) ^ 2) ^ 2 := by
  have h1 := fourthMoment_partialSum_le lambda K
  have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range K, (lambda j) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hle : (∑ j ∈ Finset.range K, (lambda j) ^ 2)
      ≤ (∑' j : ℕ, (lambda j) ^ 2) :=
    hlambda.sum_le_tsum (Finset.range K) (fun j _ => sq_nonneg _)
  have hpow : (∑ j ∈ Finset.range K, (lambda j) ^ 2) ^ 2
      ≤ (∑' j : ℕ, (lambda j) ^ 2) ^ 2 := pow_le_pow_left₀ hnn hle 2
  calc (∫ x : ℕ → ℝ, (∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) ^ 4
        ∂gaussianSeqMeasure)
      ≤ 60 * (∑ j ∈ Finset.range K, (lambda j) ^ 2) ^ 2 := h1
    _ ≤ 60 * (∑' j : ℕ, (lambda j) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)

/-- The uniform `L⁴` bound in the `E|S_K|⁴` shape (the integrand is an even
power, so `|S_K|⁴ = S_K⁴` pointwise). -/
theorem fourthMoment_partialSum_le_uniform_abs (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) (K : ℕ) :
    (∫ x : ℕ → ℝ, |∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)| ^ 4
        ∂gaussianSeqMeasure)
      ≤ 60 * (∑' j : ℕ, (lambda j) ^ 2) ^ 2 := by
  have hpoint : ∀ x : ℕ → ℝ,
      |∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)| ^ 4
        = (∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) ^ 4 := by
    intro x
    rw [← abs_pow]
    exact abs_of_nonneg (by positivity)
  calc (∫ x : ℕ → ℝ, |∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)| ^ 4
        ∂gaussianSeqMeasure)
      = (∫ x : ℕ → ℝ, (∑ j ∈ Finset.range K, lambda j * ((x j) ^ 2 - 1)) ^ 4
        ∂gaussianSeqMeasure) :=
        integral_congr_ae (Eventually.of_forall hpoint)
    _ ≤ 60 * (∑' j : ℕ, (lambda j) ^ 2) ^ 2 :=
        fourthMoment_partialSum_le_uniform lambda hlambda K

/-! ### (a) Negative mass of the prefixes and of the tail -/

/-- **(a) Partial form.**  The `hNegMass`-style negative mass of every prefix
is dominated by the full square mass:

`∑_{j<K} (min λ_j 0)² ≤ ∑' j, λ_j²`. -/
theorem negMass_partial_le (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) (K : ℕ) :
    (∑ j ∈ Finset.range K, (min (lambda j) 0) ^ 2)
      ≤ (∑' j : ℕ, (lambda j) ^ 2) := by
  calc ∑ j ∈ Finset.range K, (min (lambda j) 0) ^ 2
      ≤ ∑ j ∈ Finset.range K, (lambda j) ^ 2 :=
        Finset.sum_le_sum fun j _ => minSq_le_sq (lambda j)
    _ ≤ ∑' j : ℕ, (lambda j) ^ 2 :=
        hlambda.sum_le_tsum (Finset.range K) (fun j _ => sq_nonneg _)

/-- Full-series domination: the total negative mass is at most the total
square mass. -/
theorem negMass_tsum_le (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    (∑' j : ℕ, (min (lambda j) 0) ^ 2) ≤ (∑' j : ℕ, (lambda j) ^ 2) :=
  hasSum_le (fun j => minSq_le_sq (lambda j))
    (summable_min_sq lambda hlambda).hasSum hlambda.hasSum

/-- **(a) Tail form.**  The `hNegMass`-style sum for the TAIL coefficients
tends to zero:

`Tendsto (fun K ↦ ∑' j, (min λ_{j+K} 0)²) atTop (𝓝 0)`.

Mathlib's `tendsto_sum_nat_add` gives this without any summability hypothesis
(a non-summable tail `tsum` is `0` by convention; for the square-summable
model the sums are the honest tail masses). -/
theorem negMass_tail_tendsto (lambda : ℕ → ℝ) :
    Tendsto (fun K : ℕ => ∑' j : ℕ, (min (lambda (j + K)) 0) ^ 2) atTop (𝓝 0) :=
  tendsto_sum_nat_add (f := fun j => (min (lambda j) 0) ^ 2)

/-- Cutoff-first form of the tail negative mass, for the `∑_{j≥K}` reading:
`Tendsto (fun K ↦ ∑' j, (min λ_{K+j} 0)²) atTop (𝓝 0)`. -/
theorem negMass_tail_tendsto' (lambda : ℕ → ℝ) :
    Tendsto (fun K : ℕ => ∑' j : ℕ, (min (lambda (K + j)) 0) ^ 2) atTop (𝓝 0) :=
  Tendsto.congr (fun K => tsum_congr (fun j => by rw [Nat.add_comm]))
    (negMass_tail_tendsto lambda)

/-- The landed `L²` tail of the series, restated in the `∫ |Q − S_K|²` shape:
for the `L²`-limit `Q` of the Gaussian second-chaos series the squared error
integrals tend to zero, so the (negative-part) contribution of the tail has
the consistent `∫ |·|²` interface alongside `negMass_tail_tendsto`. -/
theorem exists_gaussSeries_L2limit_abs (lambda : ℕ → ℝ)
    (hlambda : Summable fun j => (lambda j) ^ 2) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      MemLp Q 2 gaussianSeqMeasure ∧
      Tendsto (fun K : ℕ =>
        ∫ x, |Q x - gaussPartial lambda K x| ^ 2 ∂gaussianSeqMeasure) atTop (𝓝 0) := by
  obtain ⟨Q, hQ, _hmem, htail⟩ := exists_gaussSeries_L2limit lambda hlambda
  refine ⟨Q, hQ, ?_⟩
  have hcongr : (fun K : ℕ =>
      ∫ x, |Q x - gaussPartial lambda K x| ^ 2 ∂gaussianSeqMeasure)
      = fun K : ℕ =>
      ∫ x, (Q x - gaussPartial lambda K x) ^ 2 ∂gaussianSeqMeasure := by
    funext K
    exact integral_congr_ae
      (Eventually.of_forall fun x => by simp only [sq_abs])
  rw [hcongr]
  exact htail

end Hurst
