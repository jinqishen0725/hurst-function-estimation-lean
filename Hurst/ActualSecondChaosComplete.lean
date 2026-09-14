import Hurst.FrozenQuadClosed
import Hurst.FrozenPertEnergyDischarge
import Hurst.WeightedMatrixPSD

/-!
# The corrected-route capstone: the actual q1 long-memory statistic converges to the second chaos

This file lands the three final deliverables of the corrected route, glued:

1. **The kernel-energy cutoff inputs, discharged from ordinary bandwidth data.**
   For the polynomial bandwidth `δ n = n^{-γ}` the two `Tendsto` hypotheses of the
   frozen-quadrature chain (`hcut` and `henv`) are discharged:
   * the cutoff, by the `ordinary_cutoff_satisfiable` pattern reproved here
     (`poly_cutoff_satisfiable`: take `R n = ⌊S n ^ γ'⌋ + 1` with
     `0 < γ' < 4 * h0 - 3`, nonempty exactly under `3 / 4 < h0`; the exponent
     `2 * (2 - 2 * h0) - 2 = 2 - 4 * h0 < -1` makes
     `S^{2 - 4 h0} * card * (2 R + 1) ≤ 15 * S^{γ' + 3 - 4 h0} → 0`);
   * the tail envelope: `q1ActualLongTailEnvelope` splits EXACTLY as
     `secondChaosTailFreePart + 16 / (R + 1)`
     (`q1ActualLongTailEnvelope_eq_free`); the `R`-term dies since the chosen
     `R → ∞`, and the free part dies under the polynomial bandwidth
     (`secondChaosTailFreePart_tendsto_zero_powBandwidth`): the `δ`-driven terms
     via `n^{-γ} log n → 0` and the grid-error term
     `4 * (2 S)^{2 - 2 h0} * gridCovarianceError b Ccov n` via the explicit
     polynomial rate `(1 - γ) * (2 - 2 * h0) < 2 - 2 * b` (together with
     `h0 > 3 / 4` making `(1 - γ) * (2 - 2 * h0) < 1`).  The discharge holds for
     EVERY witness constants `Ccov ≥ 0, Ctail ≥ 0, L > 0`, matching the
     ∀-form of the kernel theorem's envelope hypothesis
     (`polyBandwidth_cutoff_and_envelope`).
2. **The even power sums.**  The `hband`-free chain
   `actualQ1EigenvaluePowerSums_complete` gives the eigenvalue `k`-th power sums
   of the actual spectral matrix for EVERY `k ≥ 2` (in particular the even-k
   form consumed by the signed packaging).  It re-assembles the frozen
   quadrature WITHOUT the route-sketch bandwidth condition
   `2 * b + (2 - 2 * f t) < 3 / 2` (which is unsatisfiable jointly with
   `f t ≤ b`): the Frobenius difference `‖F_n - T_n‖ → 0` is routed through
   `‖F_n - A_n‖ → 0` (the weight-energy discharge
   `frozenPert_card_tendsto_powBandwidth`, which needs only the polynomial
   bandwidth condition `4 * b + 1 - 4 * f t < γ * (2 * (2 - 2 * f t) + 1)`) and
   `‖A_n - T_n‖ → 0` (the mesh-energy input from 1).  The Riesz spectrum bridge
   is the `HasSum` hypothesis `hRiesz` (`Σ' lam ^ k` = cycle integral), i.e.
   the second component of `IsWeightedRieszSpectrum`.
3. **The capstone.**  `actualQ1LongStatistic_tendsto_secondChaos_complete`
   applies
   `Hurst.ActualQuadratureFinal.actualQ1LongStatistic_tendsto_secondChaos_signed`
   with ALL its analytic hypotheses discharged:
   * `hPow` from 2 (all `k ≥ 2`, hence the even-k form);
   * `hNegMass` from the weight-sign regime: under nonnegative spectral weights
     the actual matrix is the PSD congruence `√R * diag w * √R`
     (`weightedFeatureQuadraticMatrix_posSemidef`), so every eigenvalue is
     nonnegative and the negative mass is IDENTICALLY zero.  (Honest note: the
     `EigenvaluePerturbation` shift-lemma route is NOT available here because
     neither the frozen matrix `F_n` (row-weighted, non-symmetric) nor the Riesz
     matrix is positive semidefinite, so there is no PSD side `B` with
     `‖A - B‖ → 0`; the PSD-of-the-actual-matrix route is used instead, with the
     weight-sign condition `hwnn` kept explicit — it is supplied, e.g., by the
     balanced degree-one design via `localLinearWeights_nonneg`.)
   * `hane` (nondegeneracy of the feature rows) and `hcard` (nonempty active
     set) remain explicit ordinary hypotheses;
   * the spectrum/law data: `lam` antitone nonnegative (the spectral-shape
     data; the `Summable (lam ^ 2)` member is derived from `hRiesz` at `k = 2`),
     `hRiesz` (`HasSum`, the `IsWeightedRieszSpectrum` bridge),
     `IsSecondChaosSeriesLaw P' Q lam` (the law identification).

CONCLUSION: `TendstoInDistribution` of the actual q1 long-memory quadratic
statistic to the second-chaos law `Q` — the corrected-route capstone.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius

namespace Hurst

/-! ## Helpers: the polynomial bandwidth `δ n = n^{-γ}` -/

/-- Negative real powers of a divergent positive sequence tend to zero (local
reproved copy of the `KernelEnergyRateDischarge` pattern). -/
theorem tendsto_rpow_neg_atTop' (S : ℕ → ℝ) (e : ℝ) (he : e < 0)
    (hS : Tendsto S atTop atTop) :
    Tendsto (fun n : ℕ => S n ^ e) atTop (𝓝 0) := by
  have hpos : ∀ᶠ n in atTop, 0 < S n := hS.eventually_gt_atTop 0
  have hkey : Tendsto (fun n : ℕ => (S n) ^ (-e)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hS
  have hinv : Tendsto (fun n : ℕ => ((S n) ^ (-e))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hkey
  refine Tendsto.congr' ?_ hinv
  filter_upwards [hpos] with n hn
  rw [← Real.rpow_neg hn.le, neg_neg]

/-- `n^{-γ}` is eventually positive. -/
private theorem powDelta_pos (γ : ℝ) (hγ0 : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn1
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn1) _

/-- `n^{-γ} → 0`. -/
private theorem powDelta_tendsto_zero (γ : ℝ) (hγ0 : 0 < γ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) := by
  have h := mesh_log_power_rpow_tendsto (-γ) (by linarith) 0
  refine h.congr' (Eventually.of_forall fun n => ?_)
  rw [pow_zero, one_mul]

/-- `n * n^{-γ} = n^{1-γ} → ∞` for `γ < 1`. -/
private theorem mul_powDelta_tendsto_atTop (γ : ℝ) (hγ1 : γ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) - γ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
      tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring, Real.rpow_add hnR (1 : ℝ) (-γ),
    Real.rpow_one]

/-! ## Deliverable 1: the envelope decomposition and its polynomial-bandwidth discharge -/

/-- The `R`-free part of `q1ActualLongTailEnvelope` (local reproved copy of the
`KernelEnergyRateDischarge.q1TailEnvelopeFreePart` definition). -/
def secondChaosTailFreePart (b Ccov Ctail L M h0 : ℝ) (n : ℕ) (δ S : ℝ) : ℝ :=
  18 * Ctail * (2 * L * (1 + M) * δ) *
      (1 + Real.exp ((2 * L * (1 + M) * δ) * Real.log n) *
        ((2 * L * (1 + M) * δ) * Real.log n)) +
    9 * Real.exp ((2 * L * (1 + M) * δ) * Real.log n) *
      ((2 * L * (1 + M) * δ) * Real.log n) +
    (3 / 2 : ℝ) * (2 * L * (1 + M) * δ) +
    4 * (2 * S) ^ (2 - 2 * h0) * gridCovarianceError b Ccov n

/-- **Exact envelope split**: the long-tail envelope is the `R`-free part plus
the single term `16 / (R + 1)`. -/
theorem q1ActualLongTailEnvelope_eq_free (b Ccov Ctail L M h0 : ℝ) (n : ℕ)
    (δ S : ℝ) (R : ℕ) :
    q1ActualLongTailEnvelope b Ccov Ctail L M h0 n δ S R
      = secondChaosTailFreePart b Ccov Ctail L M h0 n δ S
        + 16 * ((R + 1 : ℕ) : ℝ)⁻¹ := by
  unfold q1ActualLongTailEnvelope secondChaosTailFreePart
  dsimp only
  ring

/-- **The free part of the envelope dies under the polynomial bandwidth.**
For `δ n = n^{-γ}` with `0 < γ < 1`: the `δ`-driven terms die via
`n^{-γ} log n → 0`, and the grid-error term dies under the explicit polynomial
rate `(1 - γ) * (2 - 2 * h0) < 2 - 2 * b` (the `n⁻¹`-part dies already from
`h0 > 3/4`, which makes `(1 - γ) * (2 - 2 * h0) < 1/2 < 1`).  No condition on
the witness constants beyond their signs. -/
theorem secondChaosTailFreePart_tendsto_zero_powBandwidth
    (b Ccov Ctail L M h0 γ : ℝ) (hCcov : 0 ≤ Ccov) (hCtail : 0 ≤ Ctail)
    (hL : 0 < L) (hM : 0 ≤ M) (hh0 : 3 / 4 < h0) (hh01 : h0 < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * h0) < 2 - 2 * b) :
    Tendsto (fun n : ℕ => secondChaosTailFreePart b Ccov Ctail L M h0 n
      ((n : ℝ) ^ (-γ)) ((n : ℝ) * (n : ℝ) ^ (-γ))) atTop (𝓝 0) := by
  have hnR1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  have hD0 : Tendsto (fun n : ℕ => 2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) atTop (𝓝 0) := by
    simpa using (powDelta_tendsto_zero γ hγ0).const_mul (2 * L * (1 + M))
  have hE0 : Tendsto (fun n : ℕ =>
      (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log (n : ℝ)) atTop (𝓝 0) := by
    have hbase := (nat_log_power_div_rpow_tendsto γ hγ0 1).const_mul (2 * L * (1 + M))
    have hstep : Tendsto (fun n : ℕ => (2 * L * (1 + M)) *
        (Real.log (n : ℝ) ^ 1 / (n : ℝ) ^ γ)) atTop (𝓝 0) := by
      simpa using hbase
    refine hstep.congr' ?_
    filter_upwards [hnR1] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Real.rpow_neg hnR.le, pow_one]
    field_simp
  have hDpos : ∀ᶠ n : ℕ in atTop, 0 ≤ 2 * L * (1 + M) * ((n : ℝ) ^ (-γ)) := by
    filter_upwards [hnR1] with n hn
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) (by linarith))
      (Real.rpow_nonneg (le_trans zero_le_one hn) _)
  have hEpos : ∀ᶠ n : ℕ in atTop,
      0 ≤ (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log (n : ℝ) := by
    filter_upwards [hDpos, hnR1] with n hD hn
    exact mul_nonneg hD (Real.log_nonneg hn)
  -- the two grid-error power terms die under the explicit polynomial rate
  have ha1 : ((1 : ℝ) - γ) * (2 - 2 * h0) + (-1 : ℝ) < 0 := by
    have hψ0 : (0 : ℝ) < 2 - 2 * h0 := by linarith
    have hstep1 : ((1 : ℝ) - γ) * (2 - 2 * h0) < (1 : ℝ) * (2 - 2 * h0) :=
      mul_lt_mul_of_pos_right (by linarith) hψ0
    have hstep2 : (1 : ℝ) * (2 - 2 * h0) < 1 := by
      have hψhalf : (2 : ℝ) - 2 * h0 < 1 / 2 := by linarith
      linarith
    linarith
  have ha2 : ((1 : ℝ) - γ) * (2 - 2 * h0) + (2 * b - 2) < 0 := by linarith
  have hX1 : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) *
      (n : ℝ) ^ (((1 : ℝ) - γ) * (2 - 2 * h0) + (-1 : ℝ))) atTop (𝓝 0) := by
    have h := mesh_log_power_rpow_tendsto
      (((1 : ℝ) - γ) * (2 - 2 * h0) + (-1 : ℝ)) ha1 1
    refine h.congr' (Eventually.of_forall fun n => ?_)
    rw [pow_one]
  have hX2 : Tendsto (fun n : ℕ => (1 + Real.log (2 * (n : ℝ))) *
      (n : ℝ) ^ (((1 : ℝ) - γ) * (2 - 2 * h0) + (2 * b - 2))) atTop (𝓝 0) := by
    have h := mesh_log_power_rpow_tendsto
      (((1 : ℝ) - γ) * (2 - 2 * h0) + (2 * b - 2)) ha2 1
    refine h.congr' (Eventually.of_forall fun n => ?_)
    rw [pow_one]
  -- pointwise rewrite of the grid-error term into the two power terms
  have hterm4eq : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) →
      4 * (2 * ((n : ℝ) * (n : ℝ) ^ (-γ))) ^ (2 - 2 * h0) *
        gridCovarianceError b Ccov n
      = 4 * (2 : ℝ) ^ (2 - 2 * h0) * Ccov *
        ((1 + Real.log (2 * (n : ℝ))) *
            (n : ℝ) ^ (((1 : ℝ) - γ) * (2 - 2 * h0) + (-1 : ℝ)) +
          (1 + Real.log (2 * (n : ℝ))) *
            (n : ℝ) ^ (((1 : ℝ) - γ) * (2 - 2 * h0) + (2 * b - 2))) := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hS : ((n : ℝ) * (n : ℝ) ^ (-γ)) = (n : ℝ) ^ ((1 : ℝ) - γ) := by
      rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
        Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]
    have hmul : (2 * (n : ℝ) ^ ((1 : ℝ) - γ)) ^ (2 - 2 * h0)
        = (2 : ℝ) ^ (2 - 2 * h0) * (n : ℝ) ^ (((1 : ℝ) - γ) * (2 - 2 * h0)) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnR.le _),
        Real.rpow_mul hnR.le]
    have hgd : gridCovarianceError b Ccov n
        = Ccov * (1 + Real.log (2 * (n : ℝ))) *
          ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := rfl
    rw [hS, hmul, hgd, Real.rpow_add hnR (((1 : ℝ) - γ) * (2 - 2 * h0)) (-1 : ℝ),
      Real.rpow_add hnR (((1 : ℝ) - γ) * (2 - 2 * h0)) (2 * b - 2)]
    ring
  have hterm4 : Tendsto (fun n : ℕ => 4 * (2 * ((n : ℝ) * (n : ℝ) ^ (-γ))) ^
      (2 - 2 * h0) * gridCovarianceError b Ccov n) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun n : ℕ => 4 * (2 : ℝ) ^ (2 - 2 * h0) * Ccov *
        ((1 + Real.log (2 * (n : ℝ))) *
            (n : ℝ) ^ (((1 : ℝ) - γ) * (2 - 2 * h0) + (-1 : ℝ)) +
          (1 + Real.log (2 * (n : ℝ))) *
            (n : ℝ) ^ (((1 : ℝ) - γ) * (2 - 2 * h0) + (2 * b - 2)))) atTop (𝓝 0) := by
      have hadd := hX1.add hX2
      simpa using hadd.const_mul (4 * (2 : ℝ) ^ (2 - 2 * h0) * Ccov)
    refine Tendsto.congr' ?_ hcomp
    filter_upwards [hnR1] with n hn
    exact (hterm4eq n hn).symm
  -- E < 1 eventually, for the exp bound
  have hE1 : ∀ᶠ n : ℕ in atTop,
      (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log (n : ℝ) < 1 :=
    hE0.eventually_lt_const (show ((0 : ℝ) < 1) by norm_num)
  -- the squeeze: free ≥ 0 and free ≤ the dying bound
  have hbound : Tendsto (fun n : ℕ =>
      18 * Ctail * (1 + Real.exp 1) * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) +
      (9 * Real.exp 1 * ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log (n : ℝ)) +
        (3 / 2 : ℝ) * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))))) atTop (𝓝 0) := by
    have h1 := hD0.const_mul (18 * Ctail * (1 + Real.exp 1))
    have h2 := hE0.const_mul (9 * Real.exp 1)
    have h3 := hD0.const_mul (3 / 2 : ℝ)
    simpa using h1.add (h2.add h3)
  have htot : Tendsto (fun n : ℕ =>
      18 * Ctail * (1 + Real.exp 1) * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) +
      (9 * Real.exp 1 * ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log (n : ℝ)) +
        (3 / 2 : ℝ) * (2 * L * (1 + M) * ((n : ℝ) ^ (-γ)))) +
      4 * (2 * ((n : ℝ) * (n : ℝ) ^ (-γ))) ^ (2 - 2 * h0) *
        gridCovarianceError b Ccov n) atTop (𝓝 0) := by
    simpa using hbound.add hterm4
  refine squeeze_zero' ?_ ?_ htot
  · -- nonnegativity of the free part (eventually)
    filter_upwards [hnR1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := hn
    have hnR0 : (0 : ℝ) ≤ (n : ℝ) := le_trans zero_le_one hn
    have hD : 0 ≤ 2 * L * (1 + M) * ((n : ℝ) ^ (-γ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) (by linarith))
        (Real.rpow_nonneg hnR0 _)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have hE : 0 ≤ (2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log (n : ℝ) :=
      mul_nonneg hD hlog
    have hexp : 0 ≤ Real.exp
        ((2 * L * (1 + M) * ((n : ℝ) ^ (-γ))) * Real.log (n : ℝ)) := Real.exp_nonneg _
    have hrpow : 0 ≤ (2 * ((n : ℝ) * (n : ℝ) ^ (-γ))) ^ (2 - 2 * h0) :=
      Real.rpow_nonneg (mul_nonneg zero_le_two
        (mul_nonneg hnR0 (Real.rpow_nonneg hnR0 _))) _
    have hgrid' : 0 ≤ gridCovarianceError b Ccov n := by
      unfold gridCovarianceError
      have h2n : (1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
      exact mul_nonneg (mul_nonneg hCcov (add_nonneg zero_le_one (Real.log_nonneg h2n)))
        (add_nonneg (Real.rpow_nonneg hnR0 _) (Real.rpow_nonneg hnR0 _))
    unfold secondChaosTailFreePart
    refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCtail) hD)
        (add_nonneg zero_le_one (mul_nonneg hexp hE))
    · exact mul_nonneg (mul_nonneg (by norm_num) hexp) hE
    · exact mul_nonneg (by norm_num) hD
    · exact mul_nonneg (mul_nonneg (by norm_num) hrpow) hgrid'
  · -- the upper bound
    filter_upwards [hnR1, hE1, hDpos, hEpos] with n hn hElt hDge hEge
    unfold secondChaosTailFreePart
    set Dn : ℝ := 2 * L * (1 + M) * ((n : ℝ) ^ (-γ)) with hDn
    set En : ℝ := Dn * Real.log (n : ℝ) with hEn
    have hc18 : 0 ≤ 18 * Ctail := mul_nonneg (by norm_num) hCtail
    have hexp : Real.exp En ≤ Real.exp 1 := Real.exp_le_exp.mpr hElt.le
    have hkey : Real.exp En * En ≤ Real.exp 1 := by
      have h1 : Real.exp En * En ≤ Real.exp 1 * En :=
        mul_le_mul_of_nonneg_right hexp hEge
      have h2 : Real.exp 1 * En ≤ Real.exp 1 * 1 :=
        mul_le_mul_of_nonneg_left hElt.le (Real.exp_nonneg 1)
      linarith
    have hψnn : 0 ≤ (2 : ℝ) ^ (2 - 2 * h0) :=
      Real.rpow_nonneg (by norm_num) _
    have hCovnn : 0 ≤ 4 * (2 : ℝ) ^ (2 - 2 * h0) * Ccov :=
      mul_nonneg (mul_nonneg (by norm_num) hψnn) hCcov
    have ht1 : 18 * Ctail * Dn * (1 + Real.exp En * En)
        ≤ 18 * Ctail * (1 + Real.exp 1) * Dn := by
      calc 18 * Ctail * Dn * (1 + Real.exp En * En)
          = 18 * Ctail * ((1 + Real.exp En * En) * Dn) := by ring
        _ ≤ 18 * Ctail * ((1 + Real.exp 1) * Dn) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith [hkey]) hDge) hc18
        _ = 18 * Ctail * (1 + Real.exp 1) * Dn := by ring
    have ht2 : 9 * Real.exp En * En ≤ 9 * Real.exp 1 * En :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (by norm_num)) hEge
    linarith

/-- **The ordinary cutoff is satisfiable under the polynomial bandwidth**
(the `ordinary_cutoff_satisfiable` pattern, reproved locally): taking
`R n = ⌊S n ^ γ'⌋ + 1` with `γ' = (4 * h0 - 3) / 2 ∈ (0, 4 * h0 - 3)` gives
`R ≥ 1`, `R → ∞`, and the ordinary cutoff `S^{2 - 4 h0} * card * (2 R + 1) → 0`
(bounded by `15 * S^{γ' + 3 - 4 h0}`, exponent `< 0`). -/
theorem poly_cutoff_satisfiable
    (h0 : ℝ) (card : ℕ → ℕ) (S : ℕ → ℝ)
    (hS : Tendsto S atTop atTop)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * S n)
    (hh0 : 3 / 4 < h0) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => (R n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (S n) ^ (2 * (2 - 2 * h0) - 2) *
        (card n : ℝ) * (2 * (R n : ℝ) + 1)) atTop (𝓝 0) := by
  obtain ⟨γ', hγ'pos, hγ'lt⟩ : ∃ γ' : ℝ, 0 < γ' ∧ γ' < 4 * h0 - 3 :=
    ⟨(4 * h0 - 3) / 2, by linarith, by linarith⟩
  set R : ℕ → ℕ := fun n => Nat.floor (S n ^ γ') + 1 with hRdef
  refine ⟨R, Eventually.of_forall fun _ => Nat.le_add_left 1 _, ?_, ?_⟩
  · -- R → ∞
    have hSγ : Tendsto (fun n : ℕ => S n ^ γ') atTop atTop :=
      (tendsto_rpow_atTop hγ'pos).comp hS
    rw [Filter.tendsto_atTop_atTop]
    intro β
    obtain ⟨N, hN'⟩ := Filter.eventually_atTop.mp
      (hSγ.eventually_ge_atTop (β : ℝ))
    refine ⟨N, fun a ha => ?_⟩
    have hge : (β : ℝ) ≤ S a ^ γ' := hN' a ha
    have hlt := Nat.lt_floor_add_one (S a ^ γ')
    show (β : ℝ) ≤ ((Nat.floor (S a ^ γ') + 1 : ℕ) : ℝ)
    push_cast
    linarith
  · -- the cutoff
    have hS1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n := hS.eventually_ge_atTop 1
    have hSγ1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n ^ γ' :=
      ((tendsto_rpow_atTop hγ'pos).comp hS).eventually_ge_atTop 1
    have hRle : ∀ᶠ n in atTop, (R n : ℝ) ≤ S n ^ γ' + 1 := by
      filter_upwards [hS1] with n hSn
      show ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ) ≤ S n ^ γ' + 1
      have hf := Nat.floor_le (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ S n) γ')
      push_cast
      linarith
    have hexp : 2 * (2 - 2 * h0) - 2 + 1 + γ' = γ' + 3 - 4 * h0 := by ring
    have hsmall := tendsto_rpow_neg_atTop' S (γ' + 3 - 4 * h0)
      (by linarith) hS
    apply squeeze_zero'
    · filter_upwards [hS1] with n hSn
      exact mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ S n) _)
        (Nat.cast_nonneg _)) (by positivity)
    · filter_upwards [hcardub, hRle, hSγ1, hS1] with n hc hr hγ1 hSn
      have hSn' : 0 < S n := lt_of_lt_of_le zero_lt_one hSn
      have hpow0 : 0 ≤ S n ^ (2 * (2 - 2 * h0) - 2) := by positivity
      have hband : (2 * (R n : ℝ) + 1) ≤ 5 * S n ^ γ' := by
        have h2 : (2 : ℝ) * (R n : ℝ) ≤ 2 * (S n ^ γ' + 1) := by
          exact mul_le_mul_of_nonneg_left hr (by norm_num)
        linarith
      have hkey : (S n) ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ'
          = S n ^ (γ' + 3 - 4 * h0) := by
        have hsplit : (S n) ^ (2 * (2 - 2 * h0) - 2) * S n
            = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) := by
          rw [Real.rpow_add hSn' (2 * (2 - 2 * h0) - 2) 1, Real.rpow_one]
        have hjoin : (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) * S n ^ γ'
            = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1 + γ') := by
          rw [Real.rpow_add hSn' (2 * (2 - 2 * h0) - 2 + 1) γ']
        calc (S n) ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ'
            = ((S n) ^ (2 * (2 - 2 * h0) - 2) * S n) * S n ^ γ' := by ring
          _ = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) * S n ^ γ' := by rw [hsplit]
          _ = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1 + γ') := hjoin
          _ = S n ^ (γ' + 3 - 4 * h0) := by rw [hexp]
      calc (S n) ^ (2 * (2 - 2 * h0) - 2) * (card n : ℝ) *
            (2 * (R n : ℝ) + 1)
          ≤ (S n) ^ (2 * (2 - 2 * h0) - 2) * (3 * S n) * (5 * S n ^ γ') :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc hpow0) hband
              (by positivity) (by positivity)
        _ = 15 * (S n ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ') := by ring
        _ = 15 * S n ^ (γ' + 3 - 4 * h0) := by rw [hkey]
    · simpa using hsmall.const_mul 15

/-- **The bandwidth-rate bundle (deliverable 1).**  For the polynomial
bandwidth `δ n = n^{-γ}` the ordinary cutoff AND the ∀-form tail-envelope
hypothesis of the frozen-quadrature chain hold simultaneously for the single
choice `R n = ⌊(n^{1-γ})^{γ'}⌋ + 1`, `γ' = (4 h0 - 3)/2`.  The γ-regime:
`0 < γ < 4 * h0 - 3` (nonempty exactly under `h0 > 3/4`) and the grid-error
rate `(1 - γ) * (2 - 2 * h0) < 2 - 2 * b`. -/
theorem polyBandwidth_cutoff_and_envelope
    (b M h0 γ : ℝ) (hM : 0 ≤ M)
    (hh0 : 3 / 4 < h0) (hh01 : h0 < 1) (hγ0 : 0 < γ) (hγcut : γ < 4 * h0 - 3)
    (hgrid : (1 - γ) * (2 - 2 * h0) < 2 - 2 * b)
    (card : ℕ → ℕ)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * ((n : ℝ) * (n : ℝ) ^ (-γ))) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => (R n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => ((n : ℝ) * (n : ℝ) ^ (-γ)) ^ (2 * (2 - 2 * h0) - 2) *
        (card n : ℝ) * (2 * (R n : ℝ) + 1)) atTop (𝓝 0) ∧
      ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M h0 n ((n : ℝ) ^ (-γ))
          ((n : ℝ) * (n : ℝ) ^ (-γ)) (R n)) atTop (𝓝 0) := by
  obtain ⟨R, hR1, hRtop, hcut⟩ :=
    poly_cutoff_satisfiable h0 card (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ))
      (mul_powDelta_tendsto_atTop γ (by linarith [hγcut, hh01])) hcardub hh0
  refine ⟨R, hR1, hRtop, hcut, ?_⟩
  intro Ccov hCcov Ctail hCtail L hL
  have hfree := secondChaosTailFreePart_tendsto_zero_powBandwidth b Ccov Ctail L M
    h0 γ hCcov hCtail hL hM hh0 hh01 hγ0 (by linarith [hγcut, hh01]) hgrid
  -- 16 / (R + 1) → 0 from R → ∞
  have hRinf : Tendsto (fun n : ℕ => (R n : ℝ) + 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro β
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hRtop.eventually_ge_atTop (β - 1))
    exact ⟨N, fun a ha => by have hle := hN a ha; linarith⟩
  have hRterm : Tendsto (fun n : ℕ => 16 * ((R n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hRinf).const_mul 16
  have hsum : Tendsto (fun n : ℕ =>
      secondChaosTailFreePart b Ccov Ctail L M h0 n ((n : ℝ) ^ (-γ))
        ((n : ℝ) * (n : ℝ) ^ (-γ)) + 16 * ((R n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using hfree.add hRterm
  refine Tendsto.congr (fun n => ?_) hsum
  rw [q1ActualLongTailEnvelope_eq_free]
  push_cast
  ring

/-! ## Deliverable 2: the eigenvalue power sums (all k ≥ 2), hband-free -/

/-- **The eigenvalue power sums of the actual q1 spectral matrix (the
`hband`-free corrected chain).**  From the ordinary model data, the
bandwidth-rate bundle (cutoff + envelope, discharged by
`polyBandwidth_cutoff_and_envelope`) and the polynomial-bandwidth frozen
perturbation (`frozenPert_card_tendsto_powBandwidth`): for EVERY `k ≥ 2` the
`k`-th power sums of the eigenvalues of `actualQ1Hermitian` converge to
`∑' j, lam j ^ k`, the Riesz spectrum identified through `hRiesz` (`HasSum` =
cycle integral).  NOTE: this chain deliberately avoids the frozen-quadrature
assembly of `FrozenQuadClosed`, whose route-sketch bandwidth condition
`2 * b + (2 - 2 * f t) < 3 / 2` is unsatisfiable jointly with `f t ≤ b`; the
Frobenius input is instead supplied by the weight-energy discharge. -/
theorem actualQ1EigenvaluePowerSums_complete
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγcut : γ < 4 * f t - 3)
    (hγgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (hγdec : (4 : ℝ) * b + 1 - 4 * f t < γ * (2 * (2 - 2 * f t) + 1))
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * (n : ℝ) ^ (-γ)) ^
      (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
      (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n ((n : ℝ) ^ (-γ))
        ((n : ℝ) * (n : ℝ) ^ (-γ)) (R n)) atTop (𝓝 0))
    (hcard : ∀ n : ℕ, 0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card)
    (lam : ℕ → ℝ)
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) := by
  -- the polynomial-bandwidth ordinary events
  have hδpos := powDelta_pos γ hγ0
  have hδ0 := powDelta_tendsto_zero γ hγ0
  have hN := mul_powDelta_tendsto_atTop γ (by
    linarith [hγcut, lt_of_le_of_lt (hF ht).2 hb])
  -- 1. the mesh-energy convergence from the bundle
  have hE := actualQ1_meshEnergy_tendsto_zero p a b M r hp ha hb hab hM f hf hF
    t ht hlong (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN R hR hcut henv
  -- the explicit constants
  obtain ⟨Bω, hBω0, hBωall⟩ := equivalentKernel_bounded r
  have hBω : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ Bω :=
    fun z hz => hBωall z
  have hψle : (0 : ℝ) ≤ 2 - 2 * f t := by linarith [(hF ht).2]
  have hψhalf : (2 : ℝ) - 2 * f t < 1 / 2 := by linarith
  have hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤
        2 * (f t * (2 * f t - 1)) ^ 2 *
          (3 + 3 * 4 ^ (1 - 2 * (2 - 2 * f t)) / (1 - 2 * (2 - 2 * f t))) :=
    fun S m hS hm =>
      rankRieszKernel_energy_le_const S (2 - 2 * f t) (f t * (2 * f t - 1))
        hS hm hψle hψhalf
  -- 2. the frozen perturbation, discharged by the weight-energy route
  have hFrozenPert := frozenPert_card_tendsto_powBandwidth p a b M r γ hp ha hb hab
    hM f hf hF t ht hlong hγ0 (by
      linarith [hγcut, lt_of_le_of_lt (hF ht).2 hb]) hγdec
  -- 3. the uniform Frobenius bound
  obtain ⟨C, hC0, hmaxb⟩ := actualQ1UniformFrobeniusBound_of_bounded f hf r
    (fun n : ℕ => (n : ℝ) ^ (-γ)) t ht hδpos hδ0 hN Bω hBω _ hCref hE
  -- 4. ‖A − F‖ → 0 from the dimension-weighted discharge
  have hAF0 : Tendsto (fun n : ℕ =>
      ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
        actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖) atTop (𝓝 0) := by
    have hsq0 : Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
          actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ^ 2)
        atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ hFrozenPert
      filter_upwards [eventually_ge_atTop 1] with n hn1
      have hcard1 : ((1 : ℝ) : ℝ)
          ≤ (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card := by
        exact_mod_cast (Nat.succ_le_of_lt (hcard n))
      calc ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
              actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ^ 2
          = (1 : ℝ) * ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
              actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ^ 2 :=
            (one_mul _).symm
        _ ≤ (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card *
              ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
                actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hcard1 (sq_nonneg _)
    refine Tendsto.congr' (Eventually.of_forall fun n =>
      Real.sqrt_sq (norm_nonneg _)) ?_
    have hcomp := Filter.Tendsto.comp
      (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto hsq0
    rwa [Real.sqrt_zero] at hcomp
  -- 5. ‖A − T‖ → 0 from the mesh-energy input
  have hAT0 := actualQ1_frobenius_norm_tendsto_zero f hf r
    (fun n : ℕ => (n : ℝ) ^ (-γ)) t hδpos hE
  -- 6. ‖F − T‖ → 0 by the triangle route through A
  have hΔ : Tendsto (fun n : ℕ =>
      ‖actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
        actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t‖) atTop (𝓝 0) := by
    have hsum0 : Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
          actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ +
        ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
          actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t‖) atTop (𝓝 0) := by
      simpa using hAF0.add hAT0
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum0
    filter_upwards [] with n
    have hsplit : actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
        actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t
        = -(actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
              actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t) +
            (actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
              actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t) := by abel
    rw [hsplit]
    simpa only [norm_neg] using norm_add_le
      (-(actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
          actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t))
      (actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
        actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t)
  -- 7. the eventual bounds for ‖F‖ and ‖T‖
  have hAF1 : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
        actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ≤ 1 :=
    hAF0.eventually_le_const (show ((0 : ℝ) < 1) by norm_num)
  have hTb : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t‖ ≤ C + 1 := by
    filter_upwards [hmaxb] with n hmax
    have h1 := le_max_right
      ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖
      ‖actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t‖
    linarith [h1, hmax, hC0]
  have hFb : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ≤ C + 1 := by
    filter_upwards [hAF1, hmaxb] with n hfa hmax
    have hA : ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ ≤ C := by
      have h1 := le_max_left
        ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖
        ‖actualQ1RieszMatrix f r n ((n : ℝ) ^ (-γ)) t‖
      linarith
    have hrev : ‖actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
        actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖
        = ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
          actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ :=
      norm_sub_rev _ _
    have hjoin : (actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
        actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t) +
        actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t
      = actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t := by abel
    calc ‖actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖
        = ‖(actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
              actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t) +
            actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ := by
          rw [hjoin]
      _ ≤ ‖actualQ1NormalizedFrozenMatrix f hf r n ((n : ℝ) ^ (-γ)) t -
              actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ +
            ‖actualQ1NormalizedActualMatrix f hf r n ((n : ℝ) ^ (-γ)) t‖ :=
          norm_add_le _ _
      _ ≤ C + 1 := by rw [hrev]; linarith
  -- 8. the frozen quadrature
  have hFQ := frozenQuad_hFquad_of_frobeniusSmall p a b M r hp ha hb hab hM f hf
    hF t ht hlong (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN k hk (C + 1) hFb hTb hΔ
  -- 9. the trace-power transfer with the discharged perturbation
  have htr := actualQ1_trace_pow_tendsto_of_frozenPert p a b M r hp ha hb hab hM
    f hf hF t ht hlong (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN R hR hcut henv
    Bω hBω _ hCref hcard hFrozenPert k hFQ
  -- 10. the eigenvalue trace identity along the sequence
  have hcardpos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card :=
    (localWeightActiveSet_card_ratio_tendsto_two 1 t ht
      (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN).1
  have hsum : ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k
      = Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n
          ((n : ℝ) ^ (-γ)) t) ^ k) := by
    filter_upwards [hcardpos, hδpos] with n hcard hδ
    have hn : 0 < n := by
      have hlt := (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t ⟨0, hcard⟩).isLt
      omega
    rw [← hermitian_trace_pow_eq_sum_eigenvalues_pow
      (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t) k]
    rw [trace_pow_weightedFeatureQuadraticMatrix_eq
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
      (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) k]
    rw [actualQ1_diagonalCorrelation_eq f hf r n hn ((n : ℝ) ^ (-γ)) t hδ]
  -- 11. the Riesz spectral identification and the conclusion
  rw [show (∑' j : ℕ, lam j ^ k)
      = weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) from (hRiesz k hk).tsum_eq]
  refine Tendsto.congr' (hsum.mono fun n h => h.symm) ?_
  exact htr

/-! ## Deliverable 3: the capstone -/

set_option maxHeartbeats 10000000 in
/-- **THE CORRECTED-ROUTE CAPSTONE.**  The actual q1 long-memory quadratic
statistic converges in distribution to the second-chaos law `Q`.  All analytic
hypotheses are discharged from the ordinary model plus the explicit polynomial
bandwidth regime; what remains explicit is ORDINARY data only: the model
(`p/a/b/M/r/f/hf/hF/t/ht/hlong`), the γ-regime (`hγ0/hγcut/hγgrid/hγdec`), the
spectrum/law data (`hlam/hRiesz/hQ`), nondegeneracy (`hcard/hane`), and the
weight-sign regime `hwnn` (which discharges `hNegMass`; supplied, e.g., by the
balanced degree-one design via `localLinearWeights_nonneg`). -/
theorem actualQ1LongStatistic_tendsto_secondChaos_complete
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγcut : γ < 4 * f t - 3)
    (hγgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (hγdec : (4 : ℝ) * b + 1 - 4 * f t < γ * (2 * (2 - 2 * f t) + 1))
    (lam : ℕ → ℝ)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j)
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hcard : ∀ n : ℕ, 0 < (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hwnn : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogQuadraticStatistic
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
        (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
      atTop Q (fun n => featureGaussian
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  -- the eventual cardinality bound consumed by the bandwidth-rate bundle
  have hcardub : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ)
        ≤ 3 * ((n : ℝ) * (n : ℝ) ^ (-γ)) := by
    have hδpos := powDelta_pos γ hγ0
    have hδ0 := powDelta_tendsto_zero γ hγ0
    have hN := mul_powDelta_tendsto_atTop γ (by
      linarith [hγcut, lt_of_le_of_lt (hF ht).2 hb])
    obtain ⟨hcardpos, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht
      (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN
    have hS1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ (-γ) :=
      hN.eventually_ge_atTop 1
    filter_upwards [hcardpos, hδpos,
      hratio.eventually_lt_const (show ((2 : ℝ) < 3) by norm_num), hS1] with n
      hcard hδ hlt hS1
    have hn : 0 < n := by
      have hlt2 := (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t ⟨0, hcard⟩).isLt
      omega
    have hS0 : (0 : ℝ) < (n : ℝ) * (n : ℝ) ^ (-γ) := mul_pos (by exact_mod_cast hn) hδ
    have hle := (div_lt_iff₀ hS0).mp hlt
    linarith
  -- deliverable 1: cutoff + envelope for one R
  obtain ⟨R, hR, hRtop, hcut, henv⟩ := polyBandwidth_cutoff_and_envelope b M
    (h0 := f t) (γ := γ) hM hlong (lt_of_le_of_lt (hF ht).2 hb) hγ0 hγcut hγgrid
    (fun n : ℕ => (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card) hcardub
  -- the polynomial-bandwidth ordinary events
  have hδpos := powDelta_pos γ hγ0
  have hδ0 := powDelta_tendsto_zero γ hγ0
  have hN := mul_powDelta_tendsto_atTop γ (by
    linarith [hγcut, lt_of_le_of_lt (hF ht).2 hb])
  -- deliverable 2: the power sums for all k ≥ 2, hence the even-k form of hPow
  have hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) :=
    fun k hk _ => actualQ1EigenvaluePowerSums_complete p a b M r hp ha hb hab hM
      f hf hF t ht hlong γ hγ0 hγcut hγgrid hγdec R hR hcut henv hcard lam hRiesz k hk
  -- hNegMass: discharged by the weight-sign regime (PSD congruence)
  have hEv : ∀ n : ℕ, actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t
      = weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) := fun _ => rfl
  have hPt : ∀ (n : ℕ) (i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i
        = (weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
            (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).eigenvalues i :=
    fun n i => congrArg (fun H : (weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
        (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).IsHermitian =>
      H.eigenvalues i) (hEv n)
  have hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0) := by
    have hstep : ∀ᶠ n : ℕ in atTop,
        (∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
        = 0 := by
      filter_upwards [hwnn] with n hwn
      refine Finset.sum_eq_zero fun i _ => ?_
      have h0 : 0 ≤ (weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).eigenvalues i :=
        weightedFeatureQuadraticMatrix_eigenvalues_nonneg
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) hwn i
      rw [← hPt n i, min_eq_right h0]
      ring
    exact tendsto_nhds_of_eventually_eq hstep
  exact actualQ1LongStatistic_tendsto_secondChaos_signed f hf r t
    (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN ht P' Q lam hQ
    ⟨hlam.1, fun j => ⟨hlam.2 j, (hRiesz 2 (by norm_num)).summable⟩⟩
    hcard hPow hane hNegMass

end Hurst
