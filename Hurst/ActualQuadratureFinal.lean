import Hurst.ActualKernelBandAsymptotics
import Hurst.ActualQuadratureConfluence
import Hurst.SignedInterfaceFinal
import Hurst.HcoeffBridge

/-!
# Actual quadrature final confluence: the corrected route

This file assembles the CORRECTED final route for the actual normalized
matrix's eigenvalue even-power sums.  The corrected decomposition of
`Hurst.ActualKernelBandAsymptotics` replaces the dead Frobenius-perturbation
hypothesis `hPert` (which compared the actual matrix to the RIESZ matrix
across a nonvanishing diagonal) by the frozen decomposition

```
actual kernel K_A = frozen kernel F + E_n,   |E_n i j| ≤ 4 * S^ψ * gridCovarianceError n
```

with `gridCovarianceError n = C * (1 + log (2n)) * (n⁻¹ + n^{2b-2}) → 0`
(`Hurst.GridErrorLimit.gridCovarianceError_tendsto`, explicit polynomial
rate).  Both sides share the same diagonal structure, so no diagonal removal
is needed on the difference.

## Contents

1. `actualQ1NormalizedFrozenMatrix` : the frozen kernel under the SAME verified
   `S^{ψ-1}` normalization as `actualQ1NormalizedActualMatrix`
   (`S⁻¹ * u_i * frozenK i j`, the row-weighted form).
2. `actualQ1_frozenError_entry_le` : the normalized error bridge, entrywise —
   every entry of `A_n - F_n` is at most
   `4 * S^{ψ-1} * |u_i| * gridCovarianceError n` (no diagonal exception).
3. `actualQ1_frobenius_frozenError_le` : the Frobenius bridge
   `‖A_n - F_n‖_F ≤ card * 4 * S^{ψ-1} * U * gridCovarianceError n` given a
   uniform weight bound `|u_i| ≤ U`.  The frozen-approx error is uniform over
   ALL pairs, so the Frobenius norm honestly carries a factor `card n` (the
   band-localized, factor-free analogue is
   `actual_q1_kernel_band_predicate_tendsto_zero`).
4. `actualQ1_trace_pow_sub_le_frozen` : the word-bound decomposition
   `|tr(A^k) - tr(F^k)| ≤ √card * k * (max ‖A‖ ‖F‖)^{k-1} * ‖A - F‖_F`.
5. `actualQ1_trace_pow_tendsto_of_frozenPert` : the trace-power bridge —
   from `card * ‖A_n - F_n‖_F² → 0` (the dimension-weighted frozen
   perturbation) and frozen-trace convergence to the Riesz cycle integrals,
   the actual traces converge to the same integrals.  This is the exact
   functional slot `hPert` used to fill, with the diagonal obstruction
   removed by the frozen decomposition.
6. `actualQ1LongStatistic_tendsto_secondChaos_signed` : the signed packaging —
   `gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching`
   instantiated on the actual data.  `hAbs` is discharged from the
   even-power-sum convergence via `paddedAbsRearranged_tendsto`; `htr2` from
   the weighted-correlation-energy identity
   `weightedFeatureQuadraticMatrix_sum_eigenvalues_sq`; the hypotheses
   `hane` (nonzero feature rows) and `hNegMass` (vanishing negative spectrum)
   remain explicit (see scope note).

## Scope note: `hNegMass` and the remaining quadrature-run residue

* `hNegMass` is NOT discharged unconditionally.  The frozen decomposition
  removes the diagonal obstruction (the frozen kernel shares the actual
  diagonal), but the uniform error `4 * S^{ψ-1} * |u_i| * gridCovarianceError`
  still accumulates `card n` in Frobenius norm.  Two documented discharge
  routes, both reduced but not closed here: (a) a nonnegativity theorem for
  the local-polynomial weight profile — `u_i ≥ 0` makes the actual spectral
  matrix `√R * diag(w) * √R` positive semidefinite by congruence (its Gram
  factor `R = gram ℝ (standardizedFeatureVector ·)` is PSD), whence
  `hNegMass ≡ 0`; (b) the dimension-weighted frozen-perturbation rate
  `card * ‖A_n - F_n‖_F² → 0`, which needs the frozen-kernel quadrature below.
* The remaining quadrature-run residue is the FROZEN-kernel quadrature: the
  frozen kernel is `S^ψ * firstIncrementCrossLagCorrelation(h_i, h_j, x)`
  (`normalizedFrozenIncrement_grid_inner_eq_cross_dist`), a rank-distance
  kernel agreeing with the pure power law at relative error `O(1/x)` on the
  far band (`hurstHolder_q1_active_scaled_actual_tail_error_le_envelope`)
  and satisfying the near-band predicate
  `actual_q1_kernel_band_predicate_tendsto_zero`.  Running the
  three-predicate quadrature (as in `Hurst.RieszQuadratureInstance` with `ω`
  the frozen row-profile) yields `tr(F_n^k) → weightedRieszCycleIntegral`,
  which is hypothesis `hFrozenQuad` of
  `actualQ1_trace_pow_tendsto_of_frozenPert` and, through it, hypothesis
  `hPow` of `actualQ1LongStatistic_tendsto_secondChaos_signed`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## Private helpers -/

private theorem sq_le_sq_of_abs_le {x B : ℝ} (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  rcases abs_le.mp h with ⟨h1, h2⟩
  nlinarith

private theorem frobenius_norm_eq_sqrt_sum_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ‖A‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin m, A i j ^ 2) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

private theorem gridCov_nonneg {n : ℕ} (hn : 0 < n) {b C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ gridCovarianceError b C₀ n := by
  unfold gridCovarianceError
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by norm_cast; omega)
  positivity

/-! ## The normalized frozen matrix -/

/-- The frozen approximation kernel under the SAME verified `S^{ψ-1}`
normalization as `actualQ1NormalizedActualMatrix`: `S⁻¹ * u_i * F i j`. -/
def actualQ1NormalizedFrozenMatrix (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (n : ℕ) (δ t : ℝ) :
    Matrix (Fin (localWeightActiveSet n 1 δ t).card)
      (Fin (localWeightActiveSet n 1 δ t).card) ℝ :=
  fun i j => ((n : ℝ) * δ)⁻¹ *
    (actualQ1ChainWeight f r n δ t i *
      actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j)

/-! ## Deliverable (1): the Frobenius error bridge -/

/-- **Normalized frozen-error entry bound (deliverable 1, entrywise).**  Under
the verified `S^{ψ-1}` normalization, every entry of `A_n - F_n` is at most
`4 * S^{ψ-1} * |u_i| * gridCovarianceError n` — the uniform frozen-approx
error attenuated by the normalization, with NO diagonal exception. -/
theorem actualQ1_frozenError_entry_le
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) :
    ∃ C₀ ≥ 0, ∀ n : ℕ, 0 < n → ∀ δ : ℝ, 0 < δ →
      gridCovarianceError b C₀ n ≤ 1 / 2 →
      ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      |actualQ1NormalizedActualMatrix f hf r n δ t i j -
          actualQ1NormalizedFrozenMatrix f hf r n δ t i j| ≤
        4 * ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) *
          |actualQ1ChainWeight f r n δ t i| * gridCovarianceError b C₀ n := by
  obtain ⟨C, hC, happrox⟩ :=
    actual_q1_kernel_frozen_uniform_approx p a b M hp ha hb hab hM f hf hF t
  refine ⟨C, hC, ?_⟩
  intro n hn δ hδ hsmall i j
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  have hinv0 : 0 ≤ ((n : ℝ) * δ)⁻¹ := inv_nonneg.mpr hS0.le
  have hpert' : |q1ActualLongActiveKernel f hf n δ t ((n : ℝ) * δ) (2 - 2 * f t) i j -
      actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j| ≤
      4 * ((n : ℝ) * δ) ^ (2 - 2 * f t) * gridCovarianceError b C n :=
    happrox n hn δ ((n : ℝ) * δ) hδ hS0 hsmall i j
  have hA : actualQ1NormalizedActualMatrix f hf r n δ t i j
      = ((n : ℝ) * δ)⁻¹ *
        (actualQ1ChainWeight f r n δ t i *
          q1ActualLongActiveKernel f hf n δ t ((n : ℝ) * δ) (2 - 2 * f t) i j) := rfl
  have hFr : actualQ1NormalizedFrozenMatrix f hf r n δ t i j
      = ((n : ℝ) * δ)⁻¹ *
        (actualQ1ChainWeight f r n δ t i *
          actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j) := rfl
  rw [hA, hFr, ← mul_sub, ← mul_sub, abs_mul, abs_of_nonneg hinv0, abs_mul]
  calc ((n : ℝ) * δ)⁻¹ *
        (|actualQ1ChainWeight f r n δ t i| *
          |q1ActualLongActiveKernel f hf n δ t ((n : ℝ) * δ) (2 - 2 * f t) i j -
            actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j|) ≤
      ((n : ℝ) * δ)⁻¹ *
        (|actualQ1ChainWeight f r n δ t i| *
          (4 * ((n : ℝ) * δ) ^ (2 - 2 * f t) * gridCovarianceError b C n)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpert' (abs_nonneg _)) hinv0
    _ = 4 * ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) *
          |actualQ1ChainWeight f r n δ t i| * gridCovarianceError b C n := by
        have hkey : ((n : ℝ) * δ)⁻¹ * ((n : ℝ) * δ) ^ (2 - 2 * f t)
            = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) := by
          rw [Real.rpow_sub hS0 (2 - 2 * f t) 1, Real.rpow_one]
          ring
        rw [← hkey]
        ring

/-! ## Frobenius-corollary status note

The Frobenius-norm corollary `actualQ1_frobenius_frozenError_le`
(`‖A_n - F_n‖_F ≤ card * 4 * S^{ψ-1} * U * gridCovarianceError n`, the
direct consequence of the entrywise bound above via
`frobenius_norm_eq_sqrt_sum_sq` + `Finset.sum_le_sum` + `Finset.sum_const`)
is drafted below as a comment: its finisher (`Real.sqrt_sq` on the
`card * X` product) hit remaining elaboration issues within budget; the
trace-power bridge below consumes the dimension-weighted hypothesis
`hFrozenPert` directly and does not depend on this corollary. -/
-- /-- **The Frobenius error bridge (deliverable 1).**  With a uniform weight
-- bound `|u_i| ≤ U`, the normalized frozen perturbation obeys
-- `‖A_n - F_n‖_F ≤ card * 4 * S^{ψ-1} * U * gridCovarianceError n`. -/
-- theorem actualQ1_frobenius_frozenError_le
--     (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
--     (hab : a ≤ b) (hM : 0 ≤ M)
--     (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
--     (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
--     (t : ℝ) (U : ℝ) (hU : 0 ≤ U) :
--     ∃ C₀ ≥ 0, ∀ n : ℕ, 0 < n → ∀ δ : ℝ, 0 < δ →
--       gridCovarianceError b C₀ n ≤ 1 / 2 →
--       (∀ i : Fin (localWeightActiveSet n 1 δ t).card,
--         |actualQ1ChainWeight f r n δ t i| ≤ U) →
--       ‖actualQ1NormalizedActualMatrix f hf r n δ t -
--           actualQ1NormalizedFrozenMatrix f hf r n δ t‖ ≤
--         ((localWeightActiveSet n 1 δ t).card : ℝ) *
--           (4 * ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U * gridCovarianceError b C₀ n) := by
--   obtain ⟨C₀, hC₀, hentry⟩ := actualQ1_frozenError_entry_le p a b M hp ha hb hab hM f hf hF t
--   refine ⟨C₀, hC₀, ?_⟩
--   intro n hn δ hδ hsmall hu
--   have hnR : (0 : ℝ) < n := by exact_mod_cast hn
--   have hS0 : 0 < (n : ℝ) * δ := mul_pos hnR hδ
--   have hge : 0 ≤ gridCovarianceError b C₀ n := gridCov_nonneg hn hC₀
--   set X := 4 * ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U * gridCovarianceError b C₀ n with hX
--   have hX0 : 0 ≤ X := by
--     rw [hX]
--     exact mul_nonneg (mul_nonneg (by norm_num)
--       (Real.rpow_nonneg hS0.le _)) (mul_nonneg hU hge)
--   have hentry' : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
--       |(actualQ1NormalizedActualMatrix f hf r n δ t -
--           actualQ1NormalizedFrozenMatrix f hf r n δ t) i j| ≤ X := by
--     intro i j
--     have hb := hentry n hn δ hδ hsmall i j
--     rw [hX]
--     exact hb.trans (mul_le_mul_of_nonneg_right
--       (mul_le_mul_of_nonneg_left (hu i) (by norm_num)) hge)
--   have hsum : ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
--         ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
--           (actualQ1NormalizedActualMatrix f hf r n δ t -
--               actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
--       ≤ (((localWeightActiveSet n 1 δ t).card : ℝ) * X) ^ 2 := by
--     have hstep : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
--         ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
--           (actualQ1NormalizedActualMatrix f hf r n δ t -
--               actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
--         ≤ ((localWeightActiveSet n 1 δ t).card : ℝ) * X ^ 2 := by
--       intro i
--       calc ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
--             (actualQ1NormalizedActualMatrix f hf r n δ t -
--                 actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
--           ≤ ∑ _j : Fin (localWeightActiveSet n 1 δ t).card, X ^ 2 :=
--             Finset.sum_le_sum fun j _ => sq_le_sq_of_abs_le (hentry' i j)
--         _ = ((localWeightActiveSet n 1 δ t).card : ℝ) * X ^ 2 := by
--             rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
--     calc ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
--           ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
--             (actualQ1NormalizedActualMatrix f hf r n δ t -
--                 actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
--         ≤ ((localWeightActiveSet n 1 δ t).card : ℝ) * (((localWeightActiveSet n 1 δ t).card : ℝ) * X ^ 2) :=
--           Finset.sum_le_sum fun i _ => hstep i
--       _ = (((localWeightActiveSet n 1 δ t).card : ℝ) * X) ^ 2 := by
--           rw [pow_two]
--           ring
--   rw [frobenius_norm_eq_sqrt_sum_sq]
--   refine le_trans (Real.sqrt_le_sqrt hsum) ?_
--   exact Real.sqrt_sq (mul_nonneg (by
--     exact_mod_cast Nat.zero_le (localWeightActiveSet n 1 δ t).card) hX0)
--
--
--/-! ## Deliverable (2): the word-bound decomposition and the trace-power bridge -/

/-- **The word-bound decomposition (deliverable 2, L3 form).**  The trace-power
difference between the actual normalized matrix and the frozen normalized
matrix is bounded by the Frobenius word bound: one `E`-factor and `k-1`
bounded factors, at the cost of `√card`. -/
theorem actualQ1_trace_pow_sub_le_frozen (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (n : ℕ) (δ t : ℝ) (k : ℕ) :
    |Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n δ t) ^ k) -
        Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n δ t) ^ k)| ≤
      Real.sqrt (Fintype.card (Fin (localWeightActiveSet n 1 δ t).card)) *
        (k * (max ‖actualQ1NormalizedActualMatrix f hf r n δ t‖
              ‖actualQ1NormalizedFrozenMatrix f hf r n δ t‖) ^ (k - 1) *
          ‖actualQ1NormalizedActualMatrix f hf r n δ t -
            actualQ1NormalizedFrozenMatrix f hf r n δ t‖) :=
  abs_trace_pow_sub_le_of_fintype _ _ k

/-- **Trace-power bridge of the corrected route (deliverable 2).**  If the
dimension-weighted frozen perturbation vanishes
(`card * ‖A_n - F_n‖_F² → 0`) and the frozen traces converge to the weighted
Riesz cycle integrals (the frozen-kernel quadrature run, documented in the
module docstring), then the ACTUAL traces converge to the same integrals.
This is the corrected replacement of the `hPert`-consuming
`actualQ1_trace_pow_tendsto`: the perturbation is measured against the frozen
matrix, which shares the actual diagonal, so no diagonal obstruction arises. -/
theorem actualQ1_trace_pow_tendsto_of_frozenPert
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) ((n : ℝ) * δ n)
        (R n)) atTop (𝓝 0))
    (Bω : ℝ) (hBω : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ Bω)
    (Cref : ℝ)
    (hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤ Cref)
    (hcard : ∀ n : ℕ, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (hFrozenPert : Tendsto (fun n : ℕ =>
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2) atTop (𝓝 0))
    (k : ℕ)
    (hFrozenQuad : Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r)))) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) := by
  -- the uniform bound for ‖A‖ from the ordinary hypotheses
  have hEmesh := actualQ1_meshEnergy_tendsto_zero p a b M r hp ha hb hab hM f hf hF
    t ht hlong δ hδpos hδ0 hN R hR hcut henv
  obtain ⟨C, hC0, hCev⟩ := actualQ1UniformFrobeniusBound_of_bounded f hf r δ t ht
    hδpos hδ0 hN Bω hBω Cref hCref hEmesh
  -- the Frobenius difference tends to zero (the small direction of hFrozenPert)
  have hAFsq : Tendsto
      (fun n : ℕ => ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun n => by
        have h1 : (1 : ℝ) ≤ (localWeightActiveSet n 1 (δ n) t).card := by
          exact_mod_cast (Nat.succ_le_of_lt (hcard n))
        calc ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
              actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2
            = (1 : ℝ) * ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
                actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 := (one_mul _).symm
          _ ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
                ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
                  actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
      hFrozenPert
  have hAF0 : Tendsto
      (fun n : ℕ => ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖) atTop (𝓝 0) := by
    refine Tendsto.congr' (Eventually.of_forall fun n =>
      Real.sqrt_sq (norm_nonneg _)) ?_
    have hcomp := Filter.Tendsto.comp
      (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto hAFsq
    rwa [Real.sqrt_zero] at hcomp
  -- the δ'-shaped input of the mesh trace-power transfer
  have hδ'0 : Tendsto (fun n : ℕ => Real.sqrt
      (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2) atTop (𝓝 0) := by
      simpa using hFrozenPert.div_const 2
    refine Tendsto.congr' (Eventually.of_forall fun _ => rfl) ?_
    have hcomp := Filter.Tendsto.comp
      (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto h2
    rwa [Real.sqrt_zero] at hcomp
  have hΔ : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖
      ≤ Real.sqrt (2 / ((Fintype.card (Fin (localWeightActiveSet n 1 (δ n) t).card)) : ℝ)) *
        Real.sqrt (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
            actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2) :=
    Eventually.of_forall fun n => by
      rw [Fintype.card_fin]
      have hcardpos : (0 : ℝ) ≤ (localWeightActiveSet n 1 (δ n) t).card :=
        Nat.cast_nonneg _
      have hne : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (hcard n))
      have hrw : (2 / ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
          (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
              actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2)
          = ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
              actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 := by
        field_simp
      have hs1 : Real.sqrt (2 / ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
          Real.sqrt (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
              actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2)
          = Real.sqrt (2 / ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
              ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
                actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2)) :=
        (Real.sqrt_mul (div_nonneg (by norm_num) hcardpos)
          (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
              actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2)).symm
      rw [hs1, hrw, Real.sqrt_sq (norm_nonneg _)]
  -- the uniform bound for max ‖A‖ ‖F‖
  have hAF1 : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ 1 :=
    hAF0.eventually_le_const (show ((0 : ℝ) < 1) by norm_num)
  have hC2 : ∀ᶠ n : ℕ in atTop,
      max ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t‖
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ C + 1 := by
    filter_upwards [hCev, hAF1] with n hmax hle
    have hA : ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t‖ ≤ C :=
      le_trans (le_max_left _ _) hmax
    have htri : ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t‖ +
          ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
            actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ := by
      have h := norm_sub_le (actualQ1NormalizedActualMatrix f hf r n (δ n) t)
        (actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t)
      rwa [sub_sub_cancel] at h
    exact max_le (by linarith) (by linarith)
  -- the mesh trace-power transfer, run against the FROZEN matrix
  have htrace := mesh_frobenius_trace_pow_tendsto
    (fun n : ℕ => Fin (localWeightActiveSet n 1 (δ n) t).card)
    (fun n => actualQ1NormalizedActualMatrix f hf r n (δ n) t)
    (fun n => actualQ1NormalizedFrozenMatrix f hf r n (δ n) t)
    (fun n => Real.sqrt (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 / 2))
    (C + 1) hC2 hΔ (Eventually.of_forall fun _ => Real.sqrt_nonneg _) hδ'0 k
  -- combine with the frozen-quadrature convergence
  have h2 : Tendsto (fun n : ℕ =>
      |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) -
        weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r)|) atTop (𝓝 0) := by
    simpa only [Real.dist_eq, sub_zero] using
      tendsto_iff_dist_tendsto_zero.mp hFrozenQuad
  have h3 : Tendsto (fun n : ℕ =>
      |Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k) -
        weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r)|) atTop (𝓝 0) := by
    refine squeeze_zero'
      (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun n => by
        have h := abs_add_le
          (Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k) -
            Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k))
          (Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) -
            weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
              (equivalentKernel r))
        simpa only [sub_add_sub_cancel] using h)
      (by
        have hsum2 := htrace.add h2
        rwa [add_zero] at hsum2)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq, sub_zero] using h3)

/-! ## Deliverable (3): the signed packaging hookup -/


/-! ## Deliverable (3): the signed packaging hookup — landed

The elaboration hazard documented previously (an irreducible `whnf` heartbeat
timeout on the defeq
`(actualQ1Hermitian …).eigenvalues ≡ (weightedFeatureQuadraticMatrix_isHermitian (v n) …).eigenvalues`,
forced by CFC.sqrt unfolding) is avoided structurally: the two Hermitian
wrappers are bound by the exact defining equation of `actualQ1Hermitian`
(`hEv`), the pointwise eigenvalue identity is obtained by `congrArg` (`hPt`),
and every input of
`gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching` is
transported to the EXPLICIT `weightedFeatureQuadraticMatrix_isHermitian` form
(`hPowW`, `hAbsW`, `htr2W`, `hNegMassW`), so the final application performs no
defeq check on eigenvalues at all. -/

set_option maxHeartbeats 10000000 in
/-- **The signed endpoint of the corrected route (deliverable 3).**  The
statistic-level signed packaging
`gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching`
instantiated on the ACTUAL data (`v` = the harmonizable grid features of the
midpoint sample, `w` = the `S^{ψ-1}`-normalized spectral weights, `a` = the
first-stride difference coefficients).  Of the signed matching data:

* `hAbs` (the padded decreasing rearrangement of `|eigenvalues|` converges to
  `lam`) is DISCHARGED from the even-power-sum convergence `hPow` via
  `paddedAbsRearranged_tendsto` — `hPow` is exactly the output shape of the
  corrected-route quadrature (hypothesis `hFrozenQuad` of
  `actualQ1_trace_pow_tendsto_of_frozenPert` plus the eigenvalue trace
  identity `trace_pow_weightedFeatureQuadraticMatrix_eq`);
* `htr2` (the weighted-correlation-energy input) is DISCHARGED from `hPow` at
  `k = 2` via `weightedFeatureQuadraticMatrix_sum_eigenvalues_sq`;
* `hane` (nonzero feature rows) and `hNegMass` (vanishing negative-spectrum
  mass) remain explicit — see the module scope note. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_signed
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (min ((actualQ1Hermitian f hf r n (δ n) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1SpectralWeight f r n (δ n) t)
        (actualQ1Coeff n (δ n) t) x)
      atTop Q (fun n => featureGaussian
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  -- the exact eigenvalue binding: `actualQ1Hermitian` IS the
  -- `weightedFeatureQuadraticMatrix_isHermitian` of the actual data (its
  -- defining equation); everything below is transported to the explicit form
  -- so the final application never checks a defeq on `.eigenvalues`.
  have hEv : ∀ n : ℕ, actualQ1Hermitian f hf r n (δ n) t
      = weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t)
          (actualQ1SpectralWeight f r n (δ n) t) := fun _ => rfl
  have hPt : ∀ (n : ℕ) (i : Fin (localWeightActiveSet n 1 (δ n) t).card),
      (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i
        = (weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i := fun n i =>
    congrArg (fun H : (weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t)
        (actualQ1SpectralWeight f r n (δ n) t)).IsHermitian =>
      H.eigenvalues i) (hEv n)
  -- the active-card cardinality tends to infinity
  have hmtop : Tendsto (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      atTop atTop := by
    obtain ⟨_, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1
      t ht δ hδpos hδ0 hN
    rw [Filter.tendsto_atTop_atTop]
    intro N
    have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) <
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) / ((n : ℝ) * δ n) ∧
        (N : ℝ) ≤ (n : ℝ) * δ n ∧ (1 : ℝ) ≤ (n : ℝ) * δ n := by
      filter_upwards [hratio.eventually_const_lt one_lt_two,
        hN.eventually_ge_atTop (N : ℝ), hN.eventually_ge_atTop 1] with n h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨i, hi⟩ := Filter.eventually_atTop.mp hall
    refine ⟨i, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi a ha
    have hS0 : (0 : ℝ) < (a : ℝ) * δ a := by linarith
    have hle : ((a : ℝ) * δ a) ≤ (localWeightActiveSet a 1 (δ a) t).card := by
      have hfac : ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          = ((localWeightActiveSet a 1 (δ a) t).card : ℝ) / ((a : ℝ) * δ a) *
            ((a : ℝ) * δ a) :=
        (div_mul_cancel₀ ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          (ne_of_gt hS0)).symm
      rw [hfac]
      exact le_trans (by rw [one_mul])
        (le_of_lt (mul_lt_mul_of_pos_right h1 hS0))
    exact_mod_cast (h2.trans hle)
  -- the even power sums, in the explicit weightedFeatureQuadraticMatrix form
  have hPowW : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) := by
    intro k hk hev
    refine Tendsto.congr (fun n => Finset.sum_congr rfl fun i _ => ?_)
      (hPow k hk hev)
    exact congrArg (fun z : ℝ => z ^ k) (hPt n i)
  -- hAbs: the even-power sums imply the padded |λ|-rearrangement convergence
  have hAbsW : ∀ j : ℕ, Tendsto (fun n : ℕ => padRearranged
      (fun i : Fin (localWeightActiveSet n 1 (δ n) t).card =>
        |(weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i|) j)
      atTop (𝓝 (lam j)) :=
    paddedAbsRearranged_tendsto
      (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      (fun n i => (weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t)
          (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i)
      lam hm hmtop hlam hPowW
  -- htr2: the weighted-correlation-energy input, from hPow at k = 2
  have htr2W : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          actualQ1SpectralWeight f r n (δ n) t i *
            actualQ1SpectralWeight f r n (δ n) t j *
            (featureCorrelation
              (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
              (actualQ1Coeff n (δ n) t i)
              (actualQ1Coeff n (δ n) t j)) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2)) := by
    refine Tendsto.congr (fun n => ?_) (hPowW 2 (by norm_num) ⟨1, by norm_num⟩)
    exact weightedFeatureQuadraticMatrix_sum_eigenvalues_sq
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n (δ n) t)
      (actualQ1SpectralWeight f r n (δ n) t)
  -- hNegMass: transported to the explicit eigenvalue form
  have hNegMassW : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (min ((weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t)
            (actualQ1SpectralWeight f r n (δ n) t)).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => Finset.sum_congr rfl fun i _ => ?_) hNegMass
    exact congrArg (fun z : ℝ => (min z 0) ^ 2) (hPt n i)
  exact gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n => actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    (fun n => actualQ1SpectralWeight f r n (δ n) t)
    (fun n => actualQ1Coeff n (δ n) t)
    hane P' Q lam hQ hmtop hAbsW htr2W hNegMassW
--
end Hurst
