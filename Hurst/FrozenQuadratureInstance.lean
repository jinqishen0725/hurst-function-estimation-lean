import Hurst.ActualQuadratureFinal
import Hurst.GridErrorLimit

/-!
# The frozen-kernel quadrature instance: perturbation rate and packaging

This file addresses the last analytic input of the corrected route
(`Hurst.ActualQuadratureFinal`): the quadrature of the FROZEN kernel
`actualQ1NormalizedFrozenMatrix` (`F_n = S⁻¹ u_i * F i j`, the `S^{ψ-1}`
normalization shared with the actual matrix).

## The KEY QUESTION: is the frozen kernel `profile(i) * purePower(i, j)`?

**NO.**  By definition
(`Hurst.ActualKernelBandAsymptotics.actualQ1FrozenApproxKernel`)
the frozen kernel is
`S ^ ψ * ⟪normalizedFrozenIncrement_i, normalizedFrozenIncrement_j⟫`
with `ψ = 2 - 2 * f t`, i.e. (by
`normalizedFrozenIncrement_grid_inner_eq_cross_dist`)
`S ^ ψ * firstIncrementCrossLagCorrelation(h_i, h_j, rank dist)`.
It is therefore NOT of the form `profile(i) * rankRieszKernel(i, j)`:

* its diagonal is exactly `S ^ ψ * 1` (the frozen increments have unit
  norm), while the pure-power kernel `rankRieszKernel` vanishes on the
  diagonal — no row profile `ω_i` can absorb the diagonal;
* off the diagonal it agrees with the pure power law only at relative
  error `O(1/x)` on the far band (the `16 * x⁻¹` term of
  `hurstHolder_q1_active_scaled_actual_tail_error_le_envelope`), not
  exactly.

Hence `HasWeightedRieszCycleQuadrature` cannot be instantiated with
`omega := ` the frozen row profile; the frozen quadrature requires the
full three-predicate run (fixed-cutoff lattice reindexing for the frozen
row profile + discrete band removal + continuum removal), which remains
the documented open residue.  What this file lands:

1. `frozenQ1_frobeniusError_le` : the Frobenius error bridge (deliverable
   1 of the corrected route, previously left as a commented draft in
   `Hurst.ActualQuadratureFinal`)
   `‖A_n - F_n‖_F ≤ card * 4 * S^{ψ-1} * U * gridCovarianceError n`.
2. `frozenQ1_frozenPert_tendsto_zero_of_bandwidth` : the
   dimension-weighted frozen-perturbation rate
   `card * ‖A_n - F_n‖_F² → 0` under the explicit remaining bandwidth
   condition `2 * b + ψ < 3 / 2` (i.e. `b < f t - 1 / 4`, consistent with
   `3 / 4 < f t`).  This discharges `hFrozenPert` of
   `actualQ1_trace_pow_tendsto_of_frozenPert` from the ordinary model.
3. `frozenQ1_diagonal_trace_tendsto_zero` : the frozen kernel's
   pure-diagonal cycles `∑ i, (F_n i i) ^ k → 0` for `k ≥ 2` (exact unit
   diagonal of the frozen increments; no grid error needed).
4. `actualQ1_trace_pow_tendsto_of_frozenBandwidth` : the composed
   endpoint — the corrected route with `hFrozenPert` DISCHARGED from the
   ordinary model + bandwidth, leaving the frozen quadrature `hFrozenQuad`
   as the single explicit analytic input.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## Private helpers -/

private theorem frob_sq_le_sq {x B : ℝ} (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  rcases abs_le.mp h with ⟨h1, h2⟩
  nlinarith

private theorem pow_le_pow_of_abs_le' {x y : ℝ} (h : |x| ≤ y) (k : ℕ) :
    x ^ k ≤ y ^ k := by
  have hy : 0 ≤ y := (abs_nonneg x).trans h
  have hmono : ∀ j : ℕ, |x| ^ j ≤ y ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ]
        calc |x| ^ j * |x| ≤ y ^ j * |x| := mul_le_mul_of_nonneg_right ih (abs_nonneg x)
          _ ≤ y ^ j * y := mul_le_mul_of_nonneg_left h (pow_nonneg hy j)
  calc x ^ k ≤ |x| ^ k := by rw [← abs_pow]; exact le_abs_self _
    _ ≤ y ^ k := hmono k

private theorem frobenius_norm_eq_sqrt_sum_sq' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ‖A‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin m, A i j ^ 2) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

private theorem gridCov_nonneg' {n : ℕ} (hn : 0 < n) {b C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ gridCovarianceError b C₀ n := by
  unfold gridCovarianceError
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by norm_cast; omega)
  positivity

private theorem tendsto_abs_le_tendsto_zero' {f g : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, |f n| ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have habs : Tendsto (fun n => |f n|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) h hg
  have hneg : Tendsto (fun n => -|f n|) atTop (𝓝 0) := by simpa using habs.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
    (Pi.le_def.mpr fun i => by
      have h1 := le_abs_self (-(f i))
      have h2 := abs_neg (f i)
      linarith)
    (Pi.le_def.mpr fun i => le_abs_self _)

/-! ## Deliverable (1): the Frobenius error bridge -/

/-- **The Frobenius error bridge of the corrected route.**  With a uniform
weight bound `|u_i| ≤ U`, the normalized frozen perturbation obeys
`‖A_n - F_n‖_F ≤ card * 4 * S^{ψ-1} * U * gridCovarianceError n` — the
direct consequence of the entrywise bridge
`actualQ1_frozenError_entry_le` via Frobenius = sqrt of the entrywise
square sum. -/
theorem frozenQ1_frobeniusError_le
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (r : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ∃ C₀ ≥ 0, ∀ n : ℕ, 0 < n → ∀ δ : ℝ, 0 < δ →
      gridCovarianceError b C₀ n ≤ 1 / 2 →
      (∀ i : Fin (localWeightActiveSet n 1 δ t).card,
        |actualQ1ChainWeight f r n δ t i| ≤ U) →
      ‖actualQ1NormalizedActualMatrix f hf r n δ t -
          actualQ1NormalizedFrozenMatrix f hf r n δ t‖ ≤
        ((localWeightActiveSet n 1 δ t).card : ℝ) *
          (4 * ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U * gridCovarianceError b C₀ n) := by
  obtain ⟨C₀, hC₀, hentry⟩ :=
    actualQ1_frozenError_entry_le p a b M hp ha hb hab hM f hf hF t
  refine ⟨C₀, hC₀, ?_⟩
  intro n hn δ hδ hsmall hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  have hge : 0 ≤ gridCovarianceError b C₀ n := gridCov_nonneg' hn hC₀
  set X := 4 * ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U * gridCovarianceError b C₀ n with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    refine mul_nonneg ?_ hge
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg hS0.le (2 - 2 * f t - 1))) hU
  have hentry' : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      |(actualQ1NormalizedActualMatrix f hf r n δ t -
          actualQ1NormalizedFrozenMatrix f hf r n δ t) i j| ≤ X := by
    intro i j
    have hb2 := hentry n hn δ hδ hsmall i j
    have h4 : (0 : ℝ) ≤ 4 * ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hS0.le (2 - 2 * f t - 1))
    rw [hX]
    exact hb2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hu i) h4) hge)
  have hcard0 : (0 : ℝ) ≤ (localWeightActiveSet n 1 δ t).card :=
    Nat.cast_nonneg _
  have hsum : ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          (actualQ1NormalizedActualMatrix f hf r n δ t -
              actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
      ≤ (((localWeightActiveSet n 1 δ t).card : ℝ) * X) ^ 2 := by
    have hstep : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
        ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          (actualQ1NormalizedActualMatrix f hf r n δ t -
              actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
        ≤ ((localWeightActiveSet n 1 δ t).card : ℝ) * X ^ 2 := by
      intro i
      calc ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            (actualQ1NormalizedActualMatrix f hf r n δ t -
                actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
          ≤ ∑ _j : Fin (localWeightActiveSet n 1 δ t).card, X ^ 2 :=
            Finset.sum_le_sum fun j _ => frob_sq_le_sq (hentry' i j)
        _ = ((localWeightActiveSet n 1 δ t).card : ℝ) * X ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    calc ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            (actualQ1NormalizedActualMatrix f hf r n δ t -
                actualQ1NormalizedFrozenMatrix f hf r n δ t) i j ^ 2
        ≤ ∑ _i : Fin (localWeightActiveSet n 1 δ t).card,
            ((localWeightActiveSet n 1 δ t).card : ℝ) * X ^ 2 :=
          Finset.sum_le_sum (s := Finset.univ) fun i _ => hstep i
      _ = ((localWeightActiveSet n 1 δ t).card : ℝ) *
            (((localWeightActiveSet n 1 δ t).card : ℝ) * X ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ = (((localWeightActiveSet n 1 δ t).card : ℝ) * X) ^ 2 := by
          rw [pow_two]
          ring
  rw [frobenius_norm_eq_sqrt_sum_sq']
  refine le_trans (Real.sqrt_le_sqrt hsum) ?_
  exact le_of_eq (Real.sqrt_sq (mul_nonneg hcard0 hX0))

/-! ## Deliverable (2): the dimension-weighted frozen-perturbation rate -/

/-- **The dimension-weighted frozen-perturbation rate.**  Under the
ordinary model plus the explicit remaining bandwidth condition
`2 * b + ψ < 3 / 2` (equivalently `b < f t - 1 / 4`), the
dimension-weighted frozen perturbation `card * ‖A_n - F_n‖_F²` tends to
zero.  This is exactly the hypothesis `hFrozenPert` of
`actualQ1_trace_pow_tendsto_of_frozenPert`.

The rate: `card ≤ 3 S` and `S ≤ n` give
`card * ‖A - F‖² ≤ 432 * U² * S^{2ψ+1} * gridErr²` with
`gridErr = C₀ (1 + log 2n)(n⁻¹ + n^{2b-2})`; the two summands of
`gridErr²` decay as `(1 + log 2n)² n^{2ψ-1} → 0` (needs `ψ < 1/2`, i.e.
`3/4 < f t`) and `(1 + log 2n)² n^{2ψ+4b-3} → 0` (needs `2b + ψ < 3/2`). -/
theorem frozenQ1_frozenPert_tendsto_zero_of_bandwidth
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hband : 2 * b + (2 - 2 * f t) < 3 / 2)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ᶠ n in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U) :
    Tendsto (fun n : ℕ =>
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀, hfrob⟩ := frozenQ1_frobeniusError_le p a b M hp ha hb hab hM f hf hF t r U
    hU0
  have hg := gridCovarianceError_tendsto b C₀ hb
  have hsmall : ∀ᶠ n in atTop, gridCovarianceError b C₀ n ≤ 1 / 2 :=
    hg.eventually_le_const (by norm_num)
  have hnEv : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hS1ev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * δ n := hN.eventually_ge_atTop 1
  have hδ1 : ∀ᶠ n in atTop, δ n ≤ 1 := hδ0.eventually_le_const (by norm_num)
  set psi : ℝ := 2 - 2 * f t with hpsi
  have hpsi0 : 0 < psi := by
    rw [hpsi]
    have hfb := (hF ht).2
    linarith
  have hpsihalf : psi < 1 / 2 := by rw [hpsi]; linarith
  have hpsum : psi + 2 * b < 3 / 2 := by rw [hpsi]; linarith
  -- the two log-power null sequences
  have t1 := (mesh_log_rpow_tendsto (psi - 1 / 2) (by linarith)).pow 2
  have t2 := (mesh_log_rpow_tendsto (psi + 2 * b - 3 / 2) (by linarith)).pow 2
  have hfin0 : Tendsto (fun n : ℕ => (864 : ℝ) * U ^ 2 * C₀ ^ 2 *
      (((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
        ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2))
      atTop (𝓝 0) := by
    have h := (t1.add t2).const_mul ((864 : ℝ) * U ^ 2 * C₀ ^ 2)
    simpa using h
  have hpos : ∀ n : ℕ, (0 : ℝ) ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2 := by
    intro n
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine squeeze_zero' (Eventually.of_forall hpos) ?_ hfin0
  filter_upwards [hδpos, hδ1, hsmall, hnEv, hS1ev, hU] with n hδ hd1 hsm hn hS1 hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set S : ℝ := (n : ℝ) * δ n with hS
  have hSn0 : 0 < S := by rw [hS]; exact mul_pos hnR hδ
  have hSle : S ≤ (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hd1 hnR.le
    rwa [mul_one] at h
  have hcardle : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * S :=
    localWeightActiveSet_card n 1 hn (δ n) t hδ hS1
  have hcardpos : (0 : ℝ) ≤ (localWeightActiveSet n 1 (δ n) t).card :=
    Nat.cast_nonneg _
  set G : ℝ := gridCovarianceError b C₀ n with hG
  have hGdec : G = C₀ * ((1 : ℝ) + Real.log (2 * (n : ℝ))) *
      ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := by
    rw [hG]
    unfold gridCovarianceError
    ring
  set X : ℝ := 4 * S ^ (psi - 1) * U * G with hX
  have hG0 : 0 ≤ G := gridCov_nonneg' hn hC₀
  have hX0 : 0 ≤ X := by
    rw [hX]
    refine mul_nonneg ?_ hG0
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg hSn0.le (psi - 1))) hU0
  have hfrob' : ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
      actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * X :=
    hfrob n hn (δ n) hδ hsm hu
  -- card * ‖A - F‖² ≤ card³ * X²
  have hstep1 : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2
      ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 3 * X ^ 2 := by
    have habs' : |‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖| ≤
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * X := by
      rwa [abs_of_nonneg (norm_nonneg _)]
    have h1 := frob_sq_le_sq habs'
    rw [mul_pow] at h1
    calc ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
            actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ^ 2
        ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            (((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 2 * X ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hcardpos
      _ = ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 3 * X ^ 2 := by ring
  -- card³ ≤ 27 S³ and X² = 16 S^{2ψ-2} U² G²
  have hcard3 : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 3 ≤ 27 * S ^ 3 := by
    have h1 : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 3 ≤ (3 * S) ^ 3 :=
      pow_le_pow_left₀ hcardpos hcardle 3
    have h2 : (3 * S) ^ 3 = 27 * S ^ 3 := by ring
    exact h1.trans h2.le
  have hXsq : X ^ 2 = 16 * S ^ (2 * psi - 2) * U ^ 2 * G ^ 2 := by
    rw [hX, mul_pow, mul_pow, mul_pow]
    have hp1 : (S ^ (psi - 1)) ^ 2 = S ^ (2 * psi - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hSn0.le]
      congr 1
      ring
    rw [hp1]
    ring
  -- S^{2ψ+1} ≤ n^{2ψ+1}
  have hSsup : S ^ (2 * psi + 1) ≤ (n : ℝ) ^ (2 * psi + 1) := by
    refine Real.rpow_le_rpow hSn0.le hSle ?_
    linarith
  -- the two exact square identities
  have hn0le : 0 ≤ (n : ℝ) := hnR.le
  have e1 : (n : ℝ) ^ (2 * psi - 1) = ((n : ℝ) ^ (psi - 1 / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0le]
    congr 1
    ring
  have e2 : (n : ℝ) ^ (2 * psi + 4 * b - 3) = ((n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0le]
    congr 1
    ring
  -- (A + B)² ≤ 2 A² + 2 B²
  have hAB : ∀ A B : ℝ, (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    intro A B
    nlinarith [sq_nonneg (A - B)]
  -- n^{2ψ+1} * G² ≤ 2 C₀² (term1 + term2)
  have hcore : (n : ℝ) ^ (2 * psi + 1) * G ^ 2 ≤
      (2 : ℝ) * C₀ ^ 2 *
        (((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
          ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2) := by
    have hexpand : (n : ℝ) ^ (2 * psi + 1) * G ^ 2
        = C₀ ^ 2 * ((1 : ℝ) + Real.log (2 * (n : ℝ))) ^ 2 *
          ((n : ℝ) ^ (2 * psi + 1) *
            ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) ^ 2) := by
      rw [hGdec, mul_pow]
      ring
    have hp1 : (n : ℝ) ^ (2 * psi + 1) * ((n : ℝ) ^ (-1 : ℝ)) ^ 2
        = ((n : ℝ) ^ (psi - 1 / 2)) ^ 2 := by
      have h2 : ((n : ℝ) ^ (-1 : ℝ)) ^ 2 = (n : ℝ) ^ ((-2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0le]
        congr 1
        ring
      have hjoin : ((2 : ℝ) * psi + 1 + -2) = 2 * psi - 1 := by ring
      rw [h2, ← Real.rpow_add hnR, hjoin, e1]
    have hp2 : (n : ℝ) ^ (2 * psi + 1) * ((n : ℝ) ^ (2 * b - 2)) ^ 2
        = ((n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2 := by
      have h2 : ((n : ℝ) ^ (2 * b - 2)) ^ 2 = (n : ℝ) ^ (4 * b - 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0le]
        congr 1
        ring
      have hjoin : ((2 : ℝ) * psi + 1 + (4 * b - 4)) = 2 * psi + 4 * b - 3 := by ring
      rw [h2, ← Real.rpow_add hnR, hjoin, e2]
    have hsplit : (n : ℝ) ^ (2 * psi + 1) *
          ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) ^ 2 ≤
        (2 : ℝ) * (((n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
          ((n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2) := by
      calc (n : ℝ) ^ (2 * psi + 1) *
              ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) ^ 2
          ≤ (n : ℝ) ^ (2 * psi + 1) *
              ((2 : ℝ) * ((n : ℝ) ^ (-1 : ℝ)) ^ 2 +
                (2 : ℝ) * ((n : ℝ) ^ (2 * b - 2)) ^ 2) :=
            mul_le_mul_of_nonneg_left (hAB _ _)
              (Real.rpow_nonneg hn0le _)
        _ = (2 : ℝ) * ((n : ℝ) ^ (2 * psi + 1) * ((n : ℝ) ^ (-1 : ℝ)) ^ 2 +
              (n : ℝ) ^ (2 * psi + 1) * ((n : ℝ) ^ (2 * b - 2)) ^ 2) := by ring
        _ = (2 : ℝ) * (((n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
              ((n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2) := by rw [hp1, hp2]
    calc (n : ℝ) ^ (2 * psi + 1) * G ^ 2
        = C₀ ^ 2 * ((1 : ℝ) + Real.log (2 * (n : ℝ))) ^ 2 *
            ((n : ℝ) ^ (2 * psi + 1) *
              ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) ^ 2) := hexpand
      _ ≤ C₀ ^ 2 * ((1 : ℝ) + Real.log (2 * (n : ℝ))) ^ 2 *
            ((2 : ℝ) * (((n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
              ((n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsplit
            (by positivity)
      _ = (2 : ℝ) * C₀ ^ 2 *
            (((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
              ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2) := by
          rw [mul_pow, mul_pow]
          ring
  -- final assembly
  have hU2 : (0 : ℝ) ≤ 432 * U ^ 2 := by positivity
  have hXsq' : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 3 * X ^ 2
      ≤ (864 : ℝ) * U ^ 2 * C₀ ^ 2 *
        (((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
          ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2) := by
    calc ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 3 * X ^ 2
        ≤ 27 * S ^ 3 * X ^ 2 := by nlinarith [hcard3, pow_nonneg hcardpos 3, sq_nonneg X]
      _ = 27 * S ^ 3 * (16 * S ^ (2 * psi - 2) * U ^ 2 * G ^ 2) := by rw [hXsq]
      _ = 432 * (S ^ 3 * S ^ (2 * psi - 2) * (U ^ 2 * G ^ 2)) := by ring
      _ = 432 * (S ^ (2 * psi + 1) * (U ^ 2 * G ^ 2)) := by
          have hjoin : S ^ 3 * S ^ (2 * psi - 2) = S ^ (2 * psi + 1) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hSn0]
            congr 1
            ring
          rw [hjoin]
      _ = 432 * U ^ 2 * (S ^ (2 * psi + 1) * G ^ 2) := by ring
      _ ≤ 432 * U ^ 2 * ((n : ℝ) ^ (2 * psi + 1) * G ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSsup (sq_nonneg G)) hU2
      _ ≤ 432 * U ^ 2 * ((2 : ℝ) * C₀ ^ 2 *
            (((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
              ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcore hU2
      _ = (864 : ℝ) * U ^ 2 * C₀ ^ 2 *
            (((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi - 1 / 2)) ^ 2 +
              ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (psi + 2 * b - 3 / 2)) ^ 2) := by
          ring
  exact hstep1.trans hXsq'

/-! ## Deliverable (3): the frozen kernel's diagonal trace contribution -/

/-- **The frozen kernel's diagonal trace contribution tends to zero.**  The
frozen increments have EXACT unit norm, so the normalized frozen matrix has
diagonal `F_n i i = S^{ψ-1} * u_i` identically; for `k ≥ 2` and `ψ < 1 / 2`
(i.e. `3 / 4 < f t`) the pure-diagonal cycles satisfy
`|∑ i, (F_n i i) ^ k| ≤ 3 * U^k * S^{k(1-ψ)-1}^{-1} → 0`.  This is the
frozen-side analogue of `actual_q1_diagonal_trace_contribution_tendsto_zero`
(needs no grid error at all, by exactness of the unit diagonal). -/
theorem frozenQ1_diagonal_trace_tendsto_zero
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (k : ℕ) (hk : 2 ≤ k)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ᶠ n in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U) :
    Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i) ^ k) atTop (𝓝 0) := by
  set psi : ℝ := 2 - 2 * f t with hpsi
  have hpsi0 : 0 < psi := by
    rw [hpsi]
    have hfb := (hF ht).2
    linarith
  have hpsihalf : psi < 1 / 2 := by rw [hpsi]; linarith
  have hk1p : (0 : ℝ) < k * (1 - psi) - 1 := by
    have h2k : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hprod : 2 * (1 - psi) ≤ k * (1 - psi) :=
      mul_le_mul_of_nonneg_right h2k (by linarith)
    have hring : 2 * (1 - psi) = (1 - psi) + (1 - psi) := by ring
    linarith
  have hStop : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (k * (1 - psi) - 1)) atTop atTop :=
    (tendsto_rpow_atTop hk1p).comp hN
  have hinv0 : Tendsto (fun n : ℕ =>
      (((n : ℝ) * δ n) ^ (k * (1 - psi) - 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hStop
  have hfinal : Tendsto (fun n : ℕ =>
      (3 : ℝ) * (U ^ k * (((n : ℝ) * δ n) ^ (k * (1 - psi) - 1))⁻¹)) atTop (𝓝 0) := by
    have h1 := hinv0.const_mul (U ^ k)
    have h2 := h1.const_mul 3
    simpa using h2
  have hnEv : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hS1ev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * δ n := hN.eventually_ge_atTop 1
  refine tendsto_abs_le_tendsto_zero' ?_ hfinal
  filter_upwards [hδpos, hnEv, hS1ev, hU] with n hδ hn hS1 hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set S : ℝ := (n : ℝ) * δ n with hS
  have hSn0 : 0 < S := by rw [hS]; exact mul_pos hnR hδ
  have hcardle : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * S :=
    localWeightActiveSet_card n 1 hn (δ n) t hδ hS1
  -- the exact diagonal identity `F_n i i = S^{ψ-1} * u_i`
  have hAA : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ⟪normalizedFrozenIncrement
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)))
          (grid n (localWeightActiveIndex n 1 (δ n) t i).val) (((1 : ℕ) : ℝ) / n),
        normalizedFrozenIncrement
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)))
          (grid n (localWeightActiveIndex n 1 (δ n) t i).val) (((1 : ℕ) : ℝ) / n)⟫
      = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq]
    exact normalizedFrozenIncrement_norm_sq _ _ _ (div_pos (by norm_num) hnR)
  have hident : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i
        = S ^ (psi - 1) * actualQ1ChainWeight f r n (δ n) t i := by
    intro i
    have hunfold : actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i
        = ((n : ℝ) * δ n)⁻¹ *
          (actualQ1ChainWeight f r n (δ n) t i *
            actualQ1FrozenApproxKernel f hf n (δ n) t ((n : ℝ) * δ n) i i) := rfl
    have hkern : actualQ1FrozenApproxKernel f hf n (δ n) t ((n : ℝ) * δ n) i i
        = ((n : ℝ) * δ n) ^ psi := by
      unfold actualQ1FrozenApproxKernel
      rw [hAA i]
      ring
    have hkey : ((n : ℝ) * δ n)⁻¹ * ((n : ℝ) * δ n) ^ psi
        = ((n : ℝ) * δ n) ^ (psi - 1) := by
      rw [Real.rpow_sub hSn0 psi 1, Real.rpow_one]
      ring
    have hkey' : S⁻¹ * S ^ psi = S ^ (psi - 1) := by
      rw [hS]
      exact hkey
    rw [hunfold, hkern, ← hS, ← mul_assoc, mul_comm S⁻¹
      (actualQ1ChainWeight f r n (δ n) t i), mul_assoc, hkey', mul_comm]
  have hnonneg : 0 ≤ S ^ (psi - 1) := Real.rpow_nonneg hSn0.le _
  have hbound : |∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i) ^ k|
      ≤ (3 : ℝ) * (U ^ k * (S ^ (k * (1 - psi) - 1))⁻¹) := by
    have hterm : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i| ≤ S ^ (psi - 1) * U := by
      intro i
      rw [hident i, abs_mul, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_left (hu i) hnonneg
    have hstep : ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |(actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i) ^ k|
          ≤ (S ^ (psi - 1) * U) ^ k := fun i => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hterm i) k
    have hinvpos : (0 : ℝ) ≤ (S ^ (k * (1 - psi)))⁻¹ :=
      inv_nonneg.mpr (Real.rpow_nonneg hSn0.le (k * (1 - psi)))
    have hUk : (0 : ℝ) ≤ U ^ k := pow_nonneg hU0 k
    have hpowk : (S ^ (psi - 1)) ^ k = (S ^ (k * (1 - psi)))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hSn0.le,
        ← Real.rpow_neg hSn0.le (k * (1 - psi))]
      congr 1
      ring
    have hSmul : S * (S ^ (k * (1 - psi)))⁻¹ = (S ^ (k * (1 - psi) - 1))⁻¹ := by
      rw [← Real.rpow_neg hSn0.le (k * (1 - psi)),
        ← Real.rpow_neg hSn0.le (k * (1 - psi) - 1)]
      have h1 : S * S ^ (-(k * (1 - psi)))
          = S ^ ((1 : ℝ)) * S ^ (-(k * (1 - psi))) := by rw [Real.rpow_one]
      rw [h1, ← Real.rpow_add hSn0]
      congr 1
      ring
    calc |∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i) ^ k|
        ≤ ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (S ^ (psi - 1) * U) ^ k :=
          le_trans (Finset.abs_sum_le_sum_abs
            (f := fun i => (actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i i) ^ k)
            (s := Finset.univ)) (Finset.sum_le_sum (s := Finset.univ) fun i _ => hstep i)
      _ = ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (S ^ (psi - 1) * U) ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ = ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            (S ^ (k * (1 - psi)))⁻¹ * U ^ k := by
          rw [mul_pow, hpowk]
          ring
      _ ≤ (3 * S) * (S ^ (k * (1 - psi)))⁻¹ * U ^ k := by
          rw [mul_comm ((localWeightActiveSet n 1 (δ n) t).card : ℝ)
            ((S ^ (k * (1 - psi)))⁻¹), mul_comm (3 * S) ((S ^ (k * (1 - psi)))⁻¹)]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcardle hinvpos) hUk
      _ = (3 : ℝ) * (U ^ k * (S ^ (k * (1 - psi) - 1))⁻¹) := by
          have h2 : (3 * S) * (S ^ (k * (1 - psi)))⁻¹ * U ^ k
              = (3 : ℝ) * (U ^ k * (S * (S ^ (k * (1 - psi)))⁻¹)) := by ring
          rw [h2, hSmul]
  exact hbound

/-! ## Deliverable (4): the composed endpoint -/

/-- **The composed corrected route with the frozen perturbation discharged.**
This is `actualQ1_trace_pow_tendsto_of_frozenPert` with its hypothesis
`hFrozenPert` (`card * ‖A_n - F_n‖_F² → 0`) replaced by the ordinary model +
bandwidth data that DERIVE it
(`frozenQ1_frozenPert_tendsto_zero_of_bandwidth`).  After this discharge the
corrected route has exactly ONE explicit analytic input left: the frozen
quadrature `hFrozenQuad`
(`tr(F_n ^ k) → weightedRieszCycleIntegral k ψ c (equivalentKernel r)`),
whose three-predicate run is the documented open residue (see the module
docstring: the frozen kernel is NOT a row-profile instantiation of
`HasWeightedRieszCycleQuadrature`). -/
theorem actualQ1_trace_pow_tendsto_of_frozenBandwidth
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hband : 2 * b + (2 - 2 * f t) < 3 / 2)
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
    (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ᶠ n in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U)
    (k : ℕ)
    (hFrozenQuad : Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r)))) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) := by
  refine actualQ1_trace_pow_tendsto_of_frozenPert p a b M r hp ha hb hab hM f hf hF
    t ht hlong δ hδpos hδ0 hN R hR hcut henv Bω hBω Cref hCref hcard ?_ k hFrozenQuad
  exact frozenQ1_frozenPert_tendsto_zero_of_bandwidth p a b M r hp ha hb hab hM f hf hF
    t ht hlong hband δ hδpos hδ0 hN U hU0 hU

end Hurst
