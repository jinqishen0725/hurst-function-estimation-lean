import Hurst.KernelEnergyRate
import Hurst.ActualQuadratureConfluence
import Hurst.LocalWeights
import Hurst.MeshFactorizationLimit
import Hurst.ActualFirstLongBandEnergy
import Hurst.OptimalActiveRowDensity

/-!
# Discharge round for the `hPert` hypothesis of `Hurst.ActualQuadratureConfluence`

This file documents the discharge of

`hPert : card n * realScaleMeshEnergy S (actualQ1WeightedActualKernel -
  actualQ1WeightedRieszKernel) -> 0`

via the dimension-weighted rate `kernelEnergy_card_rate`
(`Hurst.KernelEnergyRate`), whose band bridges consume the STRENGTHENED
cutoff `S * (S^(2ψ-2) * card * (2R+1)) -> 0` in place of the ordinary
`hcut`.  The strengthened cutoff turned out to be REFUTABLE under the
ordinary model (`strengthened_cutoff_unsatisfiable`), so the chain does
not close; the file lands the investigation's findings and the final
HONEST packaging of the main theorem.  Findings, each landed as a
theorem:

* `q1TailEnvelopeFreePart`, `q1ActualLongTailEnvelope_eq` : the long-tail
  envelope is EXACTLY `free part + 16 / (R+1)`; the free part does not
  depend on `R`, and `16 / (R+1)` decays like `1/R`.  So the two
  `R`-constraints (`cut -> 0` wants `R = o(S^(4*h0-3))`, envelope wants
  `R >> √card`) balance at `R = ⌊S^γ⌋` whenever `1/2 < γ < 4*h0 - 3`,
  i.e. `h0 > 7/8`.
* `q1_band_cut_envelope_sqrt_card_balance` (items 1+2 of the discharge
  plan): under the `h0 > 7/8`-class exponents and the free-part rate
  `√card * free -> 0`, the explicit `R = ⌊S^γ⌋ + 1` has BOTH
  `cut R -> 0` AND `√card * envelope(R) -> 0`.
* `card_mul_weight_sq_tendsto_zero_of_row_rate` (item 3): the
  dimension-weighted weight-error rate `card * w² -> 0` follows from the
  explicit per-row rate `|w n| ≤ K / S n` (the shape delivered by
  `localPolynomialWeights_uniform_stability` for the weights themselves;
  the repo's `localPolynomialWeights_scaled_uniform_tendsto` proves the
  row error `u - v -> 0` only qualitatively, so the `K / S` rate for the
  ERROR is not derivable from current repo ingredients).
* `strengthened_cutoff_unsatisfiable` (**the central negative finding**):
  the strengthened cutoff `S * cut -> 0` consumed by
  `kernelBandActual_card_tendsto_zero_of_cut` /
  `kernelBandRiesz_card_tendsto_zero_of_cut` holds for NO choice of
  bandwidths and NO choice of `R` under the ordinary model: since
  `card ≍ 2S` (`localWeightActiveSet_card_ratio_tendsto_two`) and
  `2ψ = 2 * (2 - 2*h0) > 0` iff `h0 < 1`, `S * cut ≥ 3 * S^(2ψ) -> ∞`.
  The obstruction is real, not technical: on the band the comparison
  kernels differ at the diagonal by `q1RieszActiveKernel = 0` versus
  `q1ActualLongActiveKernel = S^ψ * 1`, so the dimension-weighted band
  energy is `Θ(S^(2ψ))` whenever the row weights are not `o(1)`; the
  `√card` loss of the trace-power transfer is not absorbable for these
  kernels.
* `ordinary_cutoff_satisfiable` (the positive packaging finding): the
  ORDINARY cutoff `S^(2ψ-2) * card * (2R+1) -> 0` IS jointly
  satisfiable with `R -> ∞` (take `R = ⌊S^γ⌋ + 1` with
  `0 < γ < 4*h0 - 3`, a nonempty range exactly in the `hlong` regime
  `h0 > 3/4`), unlike the strengthened cutoff refuted below.
* `actualQ1EigenvaluePowerSums_tendsto_ordinary` (the chain, final
  honest form): the main theorem with the perturbation input taken
  DIRECTLY at the `hPert` shape of `Hurst.ActualQuadratureConfluence`
  and the ordinary cutoff `hcut` as an explicit (satisfiable)
  hypothesis.  An earlier draft instead PRODUCED the rate from an
  existential bundle `hres` whose strengthened-cutoff member is
  refutable, making that theorem VACUOUS; see the theorem docstring
  and `strengthened_cutoff_unsatisfiable` for why the bundle packaging
  was abandoned.  The ordinary envelope input `henv` is still derived
  inside, from the free-part rate `hEfree` (the item-1+2 balance
  class) combined with `card -> ∞` and `R -> ∞`.

REWIRED (2026-09-12, discharge round 2): this file is the LAST-LAYER
module; the rewired final theorem lives in
`Hurst.KernelEnergyRateDischarged`
(`actualQ1EigenvaluePowerSums_tendsto_discharged`, which imports THIS
file), where the `hPert` hypothesis is no longer explicit: the cutoff
is CHOSEN as `R n = floor(S n ^ γ) + 1` (discharging `R`, `hR1`,
`hRtop`, `hcut` via `R_balance_cutoff`, feasible `1/2 < γ < 4*f t - 3`),
and `hPert` is produced by `hPert_discharged` from (i) the off-band
relative comparison, (ii) the balance, and (iii) the two documented
residuals — the card-weighted band rate `hband` (obstructed at
`Θ(S^{2ψ} R^{1-2ψ})` for `O(1)` row weights; no `R` discharges it) and
the quantitative weight-error rate `hκw`.  The envelope's `R`-exponent
is `θ = 1` (`tailEnvelope_decay_of_R`).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter
open scoped Topology

namespace Hurst

/-! ## The envelope decomposition (exact, no estimates) -/

/-- The `R`-free part of `q1ActualLongTailEnvelope`: every term of the
envelope except `16 * ((R + 1 : ℕ) : ℝ)⁻¹`. -/
def q1TailEnvelopeFreePart (b Ccov Ctail L M h0 : ℝ) (n : ℕ) (δ S : ℝ) : ℝ :=
  18 * Ctail * (2 * L * (1 + M) * δ) *
      (1 + Real.exp ((2 * L * (1 + M) * δ) * Real.log n) *
        ((2 * L * (1 + M) * δ) * Real.log n)) +
    9 * Real.exp ((2 * L * (1 + M) * δ) * Real.log n) *
      ((2 * L * (1 + M) * δ) * Real.log n) +
    (3 / 2 : ℝ) * (2 * L * (1 + M) * δ) +
    4 * (2 * S) ^ (2 - 2 * h0) * gridCovarianceError b Ccov n

/-- **Exact envelope decomposition**: the long-tail envelope is the free
part plus the single `R`-term `16 / (R + 1)`, which is decreasing in
`R`.  So `envelope -> 0` forces `R n -> ∞`, and conversely any
`R n -> ∞` with `√card * (free part) -> 0` gives the strengthened
`envelope = o(card^{-1/2})`. -/
theorem q1ActualLongTailEnvelope_eq (b Ccov Ctail L M h0 : ℝ) (n : ℕ)
    (δ S : ℝ) (R : ℕ) :
    q1ActualLongTailEnvelope b Ccov Ctail L M h0 n δ S R
      = q1TailEnvelopeFreePart b Ccov Ctail L M h0 n δ S
        + 16 * ((R + 1 : ℕ) : ℝ)⁻¹ := by
  unfold q1ActualLongTailEnvelope q1TailEnvelopeFreePart
  dsimp only
  ring

/-- Negative real powers of a divergent positive sequence tend to zero. -/
theorem tendsto_rpow_neg_of_atTop (S : ℕ → ℝ) (e : ℝ) (he : e < 0)
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

/-! ## Item 1 + 2: the band/envelope parameter balance -/

/-- **The parameter-balance lemma.**  With `R` chosen as `⌊S^γ⌋ + 1`, the
band cutoff `S^(2ψ-2) * card * (2R+1)` and the dimension-strengthened
envelope `√card * envelope(R)` BOTH tend to zero, provided the exponent
class allows it (`1/2 < γ < 4*h0 - 3`, i.e. `7/8 < h0` when also
`γ > 1/2`) and the `R`-free envelope part decays at the
`o(card^{-1/2})` rate.  This is the discharge plan's items 1+2 in their
exact repo shapes. -/
theorem q1_band_cut_envelope_sqrt_card_balance
    (b Ccov Ctail L M h0 γ : ℝ) (card : ℕ → ℕ) (δ S : ℕ → ℝ)
    (hS : Tendsto S atTop atTop)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * S n)
    (hγpos : 0 < γ) (hγ1 : 1 / 2 < γ) (hγ2 : γ + 3 < 4 * h0)
    (hEfree : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
      q1TailEnvelopeFreePart b Ccov Ctail L M h0 n (δ n) (S n)) atTop (𝓝 0)) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => (S n) ^ (2 * (2 - 2 * h0) - 2) *
        (card n : ℝ) * (2 * (R n : ℝ) + 1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
        q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n) (R n))
        atTop (𝓝 0) := by
  set R : ℕ → ℕ := fun n => Nat.floor (S n ^ γ) + 1 with hRdef
  have hR1 : ∀ᶠ n in atTop, 1 ≤ R n :=
    Eventually.of_forall fun _ => Nat.le_add_left 1 _
  have hS1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n := hS.eventually_ge_atTop 1
  have hSγ1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n ^ γ :=
    ((tendsto_rpow_atTop hγpos).comp hS).eventually_ge_atTop 1
  have hRle : ∀ᶠ n in atTop, (R n : ℝ) ≤ S n ^ γ + 1 := by
    filter_upwards [hS1] with n hSn
    show ((Nat.floor (S n ^ γ) + 1 : ℕ) : ℝ) ≤ S n ^ γ + 1
    have hf := Nat.floor_le (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ S n) γ)
    push_cast
    linarith
  have hfloorlt : ∀ᶠ n in atTop, S n ^ γ < (R n : ℝ) + 1 := by
    refine Eventually.of_forall fun n => ?_
    have hlt := Nat.lt_floor_add_one (S n ^ γ)
    show S n ^ γ < ((Nat.floor (S n ^ γ) + 1 : ℕ) : ℝ) + 1
    push_cast
    linarith
  refine ⟨R, hR1, ?_, ?_⟩
  · -- the band cutoff, bounded by 15 * S^(γ + 3 - 4h0) with exponent < 0
    have hexp : 2 * (2 - 2 * h0) - 2 + 1 + γ = γ + 3 - 4 * h0 := by ring
    have hsmall := tendsto_rpow_neg_of_atTop S (γ + 3 - 4 * h0)
      (by linarith) hS
    apply squeeze_zero'
    · filter_upwards [hS1] with n hSn
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ S n) _)
        (Nat.cast_nonneg _)) (by positivity)
    · filter_upwards [hcardub, hRle, hSγ1, hS1] with n hc hr hγ hSn
      have hSn' : 0 < S n := lt_of_lt_of_le zero_lt_one hSn
      have hpow0 : 0 ≤ S n ^ (2 * (2 - 2 * h0) - 2) := by positivity
      have hband : (2 * (R n : ℝ) + 1) ≤ 5 * S n ^ γ := by
        have h2 : (2 : ℝ) * (R n : ℝ) ≤ 2 * (S n ^ γ + 1) := by
          exact mul_le_mul_of_nonneg_left hr (by norm_num)
        linarith
      have hkey : (S n) ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ
          = S n ^ (γ + 3 - 4 * h0) := by
        have hsplit : (S n) ^ (2 * (2 - 2 * h0) - 2) * S n
            = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) := by
          rw [Real.rpow_add hSn' (2 * (2 - 2 * h0) - 2) 1, Real.rpow_one]
        have hjoin : (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) * S n ^ γ
            = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1 + γ) := by
          rw [Real.rpow_add hSn' (2 * (2 - 2 * h0) - 2 + 1) γ]
        calc (S n) ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ
            = ((S n) ^ (2 * (2 - 2 * h0) - 2) * S n) * S n ^ γ := by ring
          _ = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) * S n ^ γ := by rw [hsplit]
          _ = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1 + γ) := hjoin
          _ = S n ^ (γ + 3 - 4 * h0) := by rw [hexp]
      calc (S n) ^ (2 * (2 - 2 * h0) - 2) * (card n : ℝ) *
            (2 * (R n : ℝ) + 1)
          ≤ (S n) ^ (2 * (2 - 2 * h0) - 2) * (3 * S n) * (5 * S n ^ γ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc hpow0) hband
              (by positivity) (by positivity)
        _ = 15 * (S n ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ) := by ring
        _ = 15 * S n ^ (γ + 3 - 4 * h0) := by rw [hkey]
    · simpa using hsmall.const_mul 15
  · -- the strengthened envelope: √card * (free + 16/(R+1)) -> 0
    have hSγpos : ∀ᶠ n in atTop, 0 < (S n) ^ γ := by
      filter_upwards [hS1] with n hSn
      exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hSn) _
    have hinv : Tendsto (fun n : ℕ =>
        (16 : ℝ) * Real.sqrt 3 * S n ^ ((1 : ℝ) / 2 - γ)) atTop (𝓝 0) := by
      have hexpneg : ((1 : ℝ) / 2 - γ) < 0 := by linarith
      simpa using (tendsto_rpow_neg_of_atTop S ((1 : ℝ) / 2 - γ) hexpneg
        hS).const_mul (16 * Real.sqrt 3)
    have hterm : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
        (16 * ((R n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun n => by positivity
      · filter_upwards [hcardub, hfloorlt, hSγpos, hS1] with n hc hf hγ hSn
        have hinvle : ((R n + 1 : ℕ) : ℝ)⁻¹ ≤ ((S n) ^ γ)⁻¹ :=
          (inv_le_inv₀ (by positivity) hγ).2 (by push_cast; linarith)
        have hsqrt : Real.sqrt ((card n : ℝ)) ≤ Real.sqrt ((3 : ℝ) * S n) :=
          Real.sqrt_le_sqrt hc
        have hsqrtform : Real.sqrt ((3 : ℝ) * S n)
            = Real.sqrt 3 * (S n) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
            (by linarith : (0 : ℝ) ≤ S n), Real.sqrt_eq_rpow]
        have hjoin : (S n) ^ ((1 : ℝ) / 2) * (S n) ^ (-(γ : ℝ))
            = (S n) ^ ((1 : ℝ) / 2 - γ) := by
          have hSn' : 0 < S n := lt_of_lt_of_le zero_lt_one hSn
          rw [← Real.rpow_add hSn' ((1 : ℝ) / 2) (-(γ : ℝ)),
            show (((1 : ℝ) / 2 : ℝ) + (-(γ : ℝ))) = ((1 : ℝ) / 2 - γ) by ring]
        have hjoin' : (S n) ^ ((1 : ℝ) / 2) * ((S n) ^ γ)⁻¹
            = (S n) ^ ((1 : ℝ) / 2 - γ) := by
          rw [← Real.rpow_neg (by linarith : (0 : ℝ) ≤ S n) γ]
          exact hjoin
        calc Real.sqrt ((card n : ℝ)) * (16 * ((R n + 1 : ℕ) : ℝ)⁻¹)
            = 16 * (Real.sqrt ((card n : ℝ)) * ((R n + 1 : ℕ) : ℝ)⁻¹) := by ring
          _ ≤ 16 * (Real.sqrt ((3 : ℝ) * S n) * ((R n + 1 : ℕ) : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsqrt (by positivity))
              (by norm_num)
          _ ≤ 16 * (Real.sqrt ((3 : ℝ) * S n) * ((S n) ^ γ)⁻¹) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinvle
                (Real.sqrt_nonneg ((3 : ℝ) * S n)))
              (by norm_num)
          _ = (16 : ℝ) * Real.sqrt 3 * (S n) ^ ((1 : ℝ) / 2) *
                ((S n) ^ γ)⁻¹ := by rw [hsqrtform]; ring
          _ = (16 : ℝ) * Real.sqrt 3 *
                ((S n) ^ ((1 : ℝ) / 2) * ((S n) ^ γ)⁻¹) := by ring
          _ = (16 : ℝ) * Real.sqrt 3 * S n ^ ((1 : ℝ) / 2 - γ) := by
                rw [hjoin']
      · exact hinv
    have h1 : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
        q1TailEnvelopeFreePart b Ccov Ctail L M h0 n (δ n) (S n) +
      Real.sqrt ((card n : ℝ)) * (16 * ((R n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using hEfree.add hterm
    refine Tendsto.congr (fun n => ?_) h1
    rw [q1ActualLongTailEnvelope_eq]
    ring

/-! ## Item 3: the dimension-weighted weight-error rate -/

/-- **The quantitative weight upgrade.**  If the rank-uniform weight
error is bounded at the explicit per-row rate `|w n| ≤ K / S n` (the
shape delivered by `localPolynomialWeights_uniform_stability` for the
weights themselves; the repo's scaled-uniform convergence proves the
error `-> 0` only qualitatively), then the dimension-weighted rate
`card * w² -> 0` holds: `card ≤ 3S` gives `card * w² ≤ 3K²/S -> 0`. -/
theorem card_mul_weight_sq_tendsto_zero_of_row_rate
    (S w : ℕ → ℝ) (K : ℝ) (card : ℕ → ℕ)
    (hS : Tendsto S atTop atTop)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * S n)
    (hw : ∀ᶠ n in atTop, |w n| ≤ K / S n) :
    Tendsto (fun n : ℕ => (card n : ℝ) * w n ^ 2) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ => 3 * K ^ 2 / S n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 3 * K ^ 2 * (S n)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hS).const_mul (3 * K ^ 2)
    refine Tendsto.congr (fun n => ?_) h1
    field_simp
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hupper
  · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · filter_upwards [hcardub, hw, hS.eventually_ge_atTop 1] with n hc hwk hS1
    have hSn : 0 < S n := lt_of_lt_of_le zero_lt_one hS1
    have habs : |w n| ≤ |K| / S n :=
      le_trans hwk (div_le_div_of_nonneg_right (le_abs_self K) hSn.le)
    have hsq : w n ^ 2 ≤ K ^ 2 / S n ^ 2 := by
      have h1 : w n ^ 2 = |w n| ^ 2 := (sq_abs (w n)).symm
      rw [h1]
      have h2 := pow_le_pow_left₀ (abs_nonneg (w n)) habs 2
      calc |w n| ^ 2 ≤ (|K| / S n) ^ 2 := h2
        _ = |K| ^ 2 / S n ^ 2 := div_pow _ _ 2
        _ = K ^ 2 / S n ^ 2 := by rw [sq_abs K]
    calc (card n : ℝ) * w n ^ 2
        ≤ (3 * S n) * w n ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ ≤ (3 * S n) * (K ^ 2 / S n ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = 3 * K ^ 2 / S n := by field_simp

/-! ## The central negative finding: the strengthened cutoff is unsatisfiable -/

/-- **Refutation of the strengthened cutoff.**  Under the ordinary model
assumptions (`t` interior, `h0 < 1`, bandwidths with `n δ n -> ∞`), for
EVERY bandwidth-adapted `R` eventually `≥ 1`, the strengthened cutoff
`S^(2ψ-2) * card * (2R+1) * S` does NOT tend to zero: since
`card ≍ 2 S` and `2ψ = 2 * (2 - 2*h0) > 0` iff `h0 < 1`, it is bounded
below by `3 * S^(2ψ) -> ∞`.  Consequently the band-bridge hypotheses of
`Hurst.KernelEnergyRate` (`kernelBandActual_card_tendsto_zero_of_cut`,
`kernelBandRiesz_card_tendsto_zero_of_cut`) can never be supplied under
the ordinary model, for any choice of the free parameter `R`: the
diagonal mismatch of the actual versus Riesz kernels (`B_ii = 0` versus
`A_ii = S^ψ` up to row weights) makes the dimension-weighted band energy
`Θ(S^(2ψ))`.

Critical-review verdict (recorded 2026-09-12): an external review claimed
this statement is FALSE when `3/4 < h0 < 1`, on the ground that the proof
"applies `tendsto_rpow_atTop` to `S^(2-4*h0)`, which diverges only for
`h0 < 1/2`".  That reading is INCORRECT.  The exponent `2*(2-2*h0) - 2
= 2 - 4*h0` belongs to the LEADING factor only; the sequence also carries
`card ≍ 2 * S` and one explicit factor `S`, so its net asymptotic exponent
is `(2 - 4*h0) + 1 + 1 = 2*(2-2*h0) = 4 - 4*h0`, which is `> 0` exactly
under the stated hypothesis `h0 < 1`.  The proof's `tendsto_rpow_atTop`
is applied (see `hpow` below) to `X^(2*(2-2*h0))`, i.e. to the NET
exponent, and `linarith` discharges `0 < 2*(2-2*h0)` from `h0 < 1`.  The
review's counterexample "`2 * S^(4-4*h0) * (2R+1) -> 0` for constant `R`"
is arithmetically wrong: for `h0 ∈ (3/4, 1)` one has `4 - 4*h0 ∈ (0,1)`,
so that quantity tends to `∞`, not to `0`.  The theorem is therefore kept
in its sharp form with hypothesis `h0 < 1` (no `h0 < 1/2` restriction).
It is not invoked downstream; it documents why the earlier
existential-bundle packaging of
`actualQ1EigenvaluePowerSums_tendsto_ordinary` (a bundle carrying the
strengthened cutoff as a member, consumed to re-derive the ordinary
cutoff) was VACUOUS, and why that theorem now takes the ordinary cutoff
`hcut` (satisfiable, see `ordinary_cutoff_satisfiable`) and the
card-weighted energy rate `hPert` as direct honest hypotheses. -/
theorem strengthened_cutoff_unsatisfiable
    (h0 t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hh0 : h0 < 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n) :
    ¬ Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * h0) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1) * ((n : ℝ) * δ n)) atTop (𝓝 0) := by
  intro hg
  obtain ⟨hcardpos, hratio⟩ :=
    localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos hδ0 hN
  have hS1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) * δ n :=
    hN.eventually_ge_atTop 1
  have hcardS : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * δ n) < (localWeightActiveSet n 1 (δ n) t).card := by
    filter_upwards [hratio.eventually (Ioi_mem_nhds
      (show ((1 : ℝ) < 2) by norm_num)), hS1] with n hr hSn
    have hpos : 0 < (n : ℝ) * δ n := lt_of_lt_of_le zero_lt_one hSn
    have h1 : (1 : ℝ) * ((n : ℝ) * δ n) <
        ((localWeightActiveSet n 1 (δ n) t).card / ((n : ℝ) * δ n)) *
          ((n : ℝ) * δ n) := mul_lt_mul_of_pos_right hr hpos
    have h2 : ((localWeightActiveSet n 1 (δ n) t).card / ((n : ℝ) * δ n)) *
        ((n : ℝ) * δ n) = (localWeightActiveSet n 1 (δ n) t).card :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    rwa [one_mul, h2] at h1
  have hpow : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * h0))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hN
  have hbig : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 3 ≤ ((n : ℝ) * δ n) ^ (2 * (2 - 2 * h0)) :=
    hpow.eventually_ge_atTop (1 / 3)
  have hpt : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * h0) - 2) *
        (localWeightActiveSet n 1 (δ n) t).card * (2 * (R n : ℝ) + 1) *
        ((n : ℝ) * δ n) := by
    filter_upwards [hbig, hS1, hcardS, hR] with n hbig hS1 hcard hRn
    have hSn : 0 < (n : ℝ) * δ n := lt_of_lt_of_le zero_lt_one hS1
    set X : ℝ := (n : ℝ) * δ n with hX
    have hpow0 : 0 ≤ X ^ (2 * (2 - 2 * h0) - 2) :=
      Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ X) _
    have hc : X ≤ (localWeightActiveSet n 1 (δ n) t).card := le_of_lt hcard
    have hRn' : ((1 : ℕ) : ℝ) ≤ (R n : ℝ) := Nat.cast_le.mpr hRn
    have hRn1 : (1 : ℝ) ≤ (R n : ℝ) := by rwa [Nat.cast_one] at hRn'
    have hr3 : (3 : ℝ) ≤ 2 * (R n : ℝ) + 1 := by linarith
    have hstep1 : X ^ (2 * (2 - 2 * h0) - 2) * X * X
        = X ^ (2 * (2 - 2 * h0)) := by
      have hexp2 : (2 * (2 - 2 * h0) - 2) + 1 + 1 = 2 * (2 - 2 * h0) := by ring
      have hsplit : X ^ (2 * (2 - 2 * h0) - 2) * X
          = X ^ (2 * (2 - 2 * h0) - 2 + 1) := by
        rw [Real.rpow_add hSn (2 * (2 - 2 * h0) - 2) 1, Real.rpow_one]
      have hjoin : X ^ (2 * (2 - 2 * h0) - 2 + 1) * X
          = X ^ (2 * (2 - 2 * h0) - 2 + 1 + 1) := by
        rw [Real.rpow_add hSn (2 * (2 - 2 * h0) - 2 + 1) 1, Real.rpow_one]
      calc X ^ (2 * (2 - 2 * h0) - 2) * X * X
          = (X ^ (2 * (2 - 2 * h0) - 2) * X) * X := by ring
        _ = X ^ (2 * (2 - 2 * h0) - 2 + 1) * X := by rw [hsplit]
        _ = X ^ (2 * (2 - 2 * h0) - 2 + 1 + 1) := hjoin
        _ = X ^ (2 * (2 - 2 * h0)) := by rw [hexp2]
    calc (1 : ℝ) ≤ 3 * X ^ (2 * (2 - 2 * h0)) := by linarith
      _ = X ^ (2 * (2 - 2 * h0) - 2) * X * X * 3 := by rw [hstep1]; ring
      _ ≤ X ^ (2 * (2 - 2 * h0) - 2) *
            (localWeightActiveSet n 1 (δ n) t).card * (2 * (R n : ℝ) + 1) * X := by
          have hkey : X ^ (2 * (2 - 2 * h0) - 2) * X * X * 3
              = (X ^ (2 * (2 - 2 * h0) - 2) * X) * 3 * X := by ring
          have hmid : (X ^ (2 * (2 - 2 * h0) - 2) * X) * 3 * X
              ≤ (X ^ (2 * (2 - 2 * h0) - 2) *
                  (localWeightActiveSet n 1 (δ n) t).card) * 3 * X := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hc hpow0) (by norm_num))
              (by linarith)
          have hlast : (X ^ (2 * (2 - 2 * h0) - 2) *
                  (localWeightActiveSet n 1 (δ n) t).card) * 3 * X
              ≤ (X ^ (2 * (2 - 2 * h0) - 2) *
                  (localWeightActiveSet n 1 (δ n) t).card) *
                (2 * (R n : ℝ) + 1) * X := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hr3
                (mul_nonneg hpow0 (Nat.cast_nonneg _))) (by linarith)
          rw [hkey]
          exact le_trans hmid hlast
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hpt
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
    (Tendsto.eventually_lt_const (show ((0 : ℝ) < 1) by norm_num) hg)
  have hboth := hN1 (max N1 N2) (le_max_left _ _)
  have hlt' := hN2 (max N1 N2) (le_max_right _ _)
  exact absurd hboth (not_le.mpr hlt')

/-! ## The positive packaging finding: the ordinary cutoff IS satisfiable -/

/-- **The ordinary cutoff is jointly satisfiable with `R -> ∞`.**  Take
`R = ⌊S^γ⌋ + 1` with `0 < γ < 4 * h0 - 3` (a nonempty range exactly in
the long-memory regime `h0 > 3/4`, i.e. the `hlong` hypothesis of the
main theorem): then `R ≥ 1` (always), `R -> ∞`, and the ORDINARY cutoff
`S^(2*(2-2*h0)-2) * card * (2R+1) -> 0`, using the eventual bound
`card ≤ 3 * S` (delivered under the ordinary model by
`localWeightActiveSet_card_ratio_tendsto_two`, since `card / S -> 2`).
Together with `strengthened_cutoff_unsatisfiable` this locates the exact
honest strength of the cutoff input: it may be assumed at its ordinary
strength (jointly with `R -> ∞`), but not at the `* S`-strengthened
strength, for any `R`.  This is the packaging used by the final form of
`actualQ1EigenvaluePowerSums_tendsto_ordinary`. -/
theorem ordinary_cutoff_satisfiable
    (h0 : ℝ) (card : ℕ → ℕ) (S : ℕ → ℝ)
    (hS : Tendsto S atTop atTop)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * S n)
    (hh0 : 3 / 4 < h0) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => (R n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (S n) ^ (2 * (2 - 2 * h0) - 2) *
        (card n : ℝ) * (2 * (R n : ℝ) + 1)) atTop (𝓝 0) := by
  obtain ⟨γ, hγpos, hγlt⟩ : ∃ γ : ℝ, 0 < γ ∧ γ < 4 * h0 - 3 :=
    ⟨(4 * h0 - 3) / 2, by linarith, by linarith⟩
  set R : ℕ → ℕ := fun n => Nat.floor (S n ^ γ) + 1 with hRdef
  refine ⟨R, Eventually.of_forall fun _ => Nat.le_add_left 1 _, ?_, ?_⟩
  · -- R -> ∞, from S^γ -> ∞ and R > S^γ
    have hSγ : Tendsto (fun n : ℕ => S n ^ γ) atTop atTop :=
      (tendsto_rpow_atTop hγpos).comp hS
    rw [Filter.tendsto_atTop_atTop]
    intro β
    obtain ⟨N, hN'⟩ := Filter.eventually_atTop.mp
      (hSγ.eventually_ge_atTop (β : ℝ))
    refine ⟨N, fun a ha => ?_⟩
    have hge : (β : ℝ) ≤ S a ^ γ := hN' a ha
    have hlt := Nat.lt_floor_add_one (S a ^ γ)
    show (β : ℝ) ≤ ((Nat.floor (S a ^ γ) + 1 : ℕ) : ℝ)
    push_cast
    linarith
  · -- the ordinary cutoff, bounded by 15 * S^(γ + 3 - 4*h0), exponent < 0
    have hS1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n := hS.eventually_ge_atTop 1
    have hSγ1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n ^ γ :=
      ((tendsto_rpow_atTop hγpos).comp hS).eventually_ge_atTop 1
    have hRle : ∀ᶠ n in atTop, (R n : ℝ) ≤ S n ^ γ + 1 := by
      filter_upwards [hS1] with n hSn
      show ((Nat.floor (S n ^ γ) + 1 : ℕ) : ℝ) ≤ S n ^ γ + 1
      have hf := Nat.floor_le (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ S n) γ)
      push_cast
      linarith
    have hexp : 2 * (2 - 2 * h0) - 2 + 1 + γ = γ + 3 - 4 * h0 := by ring
    have hsmall := tendsto_rpow_neg_of_atTop S (γ + 3 - 4 * h0)
      (by linarith) hS
    apply squeeze_zero'
    · filter_upwards [hS1] with n hSn
      exact mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ S n) _)
        (Nat.cast_nonneg _)) (by positivity)
    · filter_upwards [hcardub, hRle, hSγ1, hS1] with n hc hr hγ1 hSn
      have hSn' : 0 < S n := lt_of_lt_of_le zero_lt_one hSn
      have hpow0 : 0 ≤ S n ^ (2 * (2 - 2 * h0) - 2) := by positivity
      have hband : (2 * (R n : ℝ) + 1) ≤ 5 * S n ^ γ := by
        have h2 : (2 : ℝ) * (R n : ℝ) ≤ 2 * (S n ^ γ + 1) := by
          exact mul_le_mul_of_nonneg_left hr (by norm_num)
        linarith
      have hkey : (S n) ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ
          = S n ^ (γ + 3 - 4 * h0) := by
        have hsplit : (S n) ^ (2 * (2 - 2 * h0) - 2) * S n
            = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) := by
          rw [Real.rpow_add hSn' (2 * (2 - 2 * h0) - 2) 1, Real.rpow_one]
        have hjoin : (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) * S n ^ γ
            = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1 + γ) := by
          rw [Real.rpow_add hSn' (2 * (2 - 2 * h0) - 2 + 1) γ]
        calc (S n) ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ
            = ((S n) ^ (2 * (2 - 2 * h0) - 2) * S n) * S n ^ γ := by ring
          _ = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1) * S n ^ γ := by rw [hsplit]
          _ = (S n) ^ (2 * (2 - 2 * h0) - 2 + 1 + γ) := hjoin
          _ = S n ^ (γ + 3 - 4 * h0) := by rw [hexp]
      calc (S n) ^ (2 * (2 - 2 * h0) - 2) * (card n : ℝ) *
            (2 * (R n : ℝ) + 1)
          ≤ (S n) ^ (2 * (2 - 2 * h0) - 2) * (3 * S n) * (5 * S n ^ γ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc hpow0) hband
              (by positivity) (by positivity)
        _ = 15 * (S n ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ) := by ring
        _ = 15 * S n ^ (γ + 3 - 4 * h0) := by rw [hkey]
    · simpa using hsmall.const_mul 15

/-! ## The honest chain: ordinary cutoff + direct `hPert` rate -/

/-- **The packaged theorem (honest form).**  This is
`actualQ1EigenvaluePowerSums_tendsto` with its three asymptotic inputs
made explicit at their honest strength, and nothing else:

* `hcut` : the ORDINARY cutoff
  `S^(2ψ-2) * card * (2R+1) -> 0`, jointly satisfiable with `R -> ∞`
  per `ordinary_cutoff_satisfiable` (take `R = ⌊S^γ⌋ + 1` with
  `0 < γ < 4 * f t - 3`, a nonempty range exactly under `hlong`);
* `hPert` : the card-weighted kernel-energy rate, taken DIRECTLY at
  exactly the shape of the `hPert` hypothesis of
  `Hurst.ActualQuadratureConfluence`;
* `henv` is NOT a hypothesis: it is derived inside from `hEfree` (the
  item-1+2 free-envelope-part rate, itself satisfiable per
  `q1_band_cut_envelope_sqrt_card_balance` with the same choice of `R`)
  combined with `card -> ∞` (`localWeightActiveSet_card_tendsto_atTop`)
  and the hypothesis `R -> ∞`.

HISTORY / HONESTY NOTE.  An earlier draft packaged the perturbation
input in an existential bundle
`hres : ∃ R w e U C, ...` whose second-to-last member was the
STRENGTHENED cutoff `S^(2ψ-2) * card * (2R+1) * S -> 0`, consumed to
re-derive `hcut`.  By `strengthened_cutoff_unsatisfiable` that member
holds for NO bandwidths and NO choice of `R` under the ordinary model,
so the bundled theorem was VACUOUS (an unsatisfiable hypothesis carries
no information).  The remaining bundle members do not survive either:
the two weighted band rates are produced from the strengthened cutoff by
the bridges of `kernelEnergy_card_rate`, and the diagonal obstruction
(`A_ii = S^ψ` versus `B_ii = 0` across `~ card` rows) that refutes the
cutoff also blocks any packaging that requires killing the weighted band
term of the comparison-kernel difference.  The honest repair is to let
the theorem consume `hPert` directly, at the exact strength at which it
is stated in `Hurst.ActualQuadratureConfluence`; the trace-power
transfer to the eigenvalues then happens inside
`actualQ1EigenvaluePowerSums_tendsto` (via
`Hurst.ActualMeshTraceTransfer` / `Hurst.TracePowerTransfer`), which
needs only `hPert` and not the strengthened cutoff. -/
theorem actualQ1EigenvaluePowerSums_tendsto_ordinary
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (lam : ℕ → ℝ)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (Bω : ℝ) (hBω : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ Bω)
    (Cref : ℝ)
    (hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤ Cref)
    (hEfree : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      Real.sqrt ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n)) atTop (𝓝 0))
    (R : ℕ → ℕ) (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (hRtop : Tendsto (fun n : ℕ => (R n : ℝ)) atTop atTop)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (hPert : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0))
    (j : ℕ) :
    Tendsto (fun n : ℕ => padRearranged
      (fun i => |(actualQ1Hermitian f hf r n (δ n) t).eigenvalues i|) j)
      atTop (𝓝 (lam j)) := by
  set S : ℕ → ℝ := fun n : ℕ => (n : ℝ) * δ n with hSdef
  set card : ℕ → ℕ :=
    fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card with hcarddef
  have hcardtop : Tendsto card atTop atTop :=
    localWeightActiveSet_card_tendsto_atTop 1 t ht δ hδpos hδ0 hN
  -- the ordinary envelope hypothesis, from the free-part rate and R -> ∞
  have henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) (S n) (R n))
      atTop (𝓝 0) := by
    intro Ccov hCcov Ctail hCtail L hL
    have hsqrt1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ (card n : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp hcardtop).eventually_ge_atTop (1 : ℝ)
    have hsqrt1' : ∀ᶠ n in atTop, (1 : ℝ) ≤ Real.sqrt ((card n : ℝ)) := by
      filter_upwards [hsqrt1] with n h
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt ((card n : ℝ)) := Real.sqrt_le_sqrt h
    have hfree0 : Tendsto (fun n : ℕ =>
        q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n))
        atTop (𝓝 0) := by
      have hscale := hEfree Ccov hCcov Ctail hCtail L hL
      have habsg : Tendsto (fun n : ℕ => |Real.sqrt ((card n : ℝ)) *
          q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n)|)
        atTop (𝓝 0) := by simpa using hscale.abs
      have habs1 : Tendsto (fun n : ℕ =>
          |q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n)|)
        atTop (𝓝 0) := by
        refine squeeze_zero'
          (Eventually.of_forall fun x => abs_nonneg _) ?_ habsg
        filter_upwards [hsqrt1'] with n h1
        have habs : (1 : ℝ) ≤ |Real.sqrt ((card n : ℝ))| := by
          rwa [abs_of_nonneg (Real.sqrt_nonneg (card n))]
        calc |q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n)|
            ≤ |Real.sqrt ((card n : ℝ))| *
              |q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n)| :=
              le_mul_of_one_le_left (abs_nonneg _) habs
          _ = |Real.sqrt ((card n : ℝ)) *
              q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n)| :=
              (abs_mul _ _).symm
      -- the free part is eventually nonnegative (all terms are)
      have hfreepos : ∀ᶠ n : ℕ in atTop, 0 ≤
          q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n) := by
        filter_upwards [hδpos, eventually_ge_atTop 2] with n hδ hn
        unfold q1TailEnvelopeFreePart
        have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by
          have hn1 : (1 : ℕ) ≤ n := by omega
          exact_mod_cast hn1
        have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR1
        have hD : 0 ≤ 2 * L * (1 + M) * δ n := by
          refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
            (le_of_lt hL)) (by linarith)) (le_of_lt hδ)
        have hE : 0 ≤ (2 * L * (1 + M) * δ n) * Real.log (n : ℝ) :=
          mul_nonneg hD hlog
        have hexp : 0 ≤ Real.exp ((2 * L * (1 + M) * δ n) * Real.log (n : ℝ)) :=
          Real.exp_nonneg _
        have hrpow : 0 ≤ (2 * S n) ^ (2 - 2 * f t) := by
          have hSnpos : (0 : ℝ) ≤ 2 * ((n : ℝ) * δ n) :=
            mul_nonneg zero_le_two
              (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hδ))
          have hSn0 : (0 : ℝ) ≤ 2 * S n := by
            rw [hSdef]
            exact hSnpos
          exact Real.rpow_nonneg hSn0 _
        have hgrid : 0 ≤ gridCovarianceError b Ccov n := by
          unfold gridCovarianceError
          have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have h2n : (1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
          refine mul_nonneg
            (mul_nonneg hCcov (add_nonneg zero_le_one (Real.log_nonneg h2n)))
            (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              (Real.rpow_nonneg (Nat.cast_nonneg n) _))
        refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hCtail) hD)
            (add_nonneg zero_le_one (mul_nonneg hexp hE))
        · exact mul_nonneg (mul_nonneg (by norm_num) hexp) hE
        · exact mul_nonneg (by norm_num) hD
        · exact mul_nonneg (mul_nonneg (by norm_num) hrpow) hgrid
      exact squeeze_zero' hfreepos
        (Eventually.of_forall fun x => le_abs_self _) habs1
    have hRterm : Tendsto (fun n : ℕ =>
        16 * ((R n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      have hRinf : Tendsto (fun n : ℕ => ((R n : ℝ) + 1)) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro β
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
          (hRtop.eventually_ge_atTop (β - 1))
        exact ⟨N, fun a ha => by
          have hle : β - 1 ≤ (R a : ℝ) := hN a ha
          linarith⟩
      have hbase : Tendsto (fun n : ℕ => 16 * ((R n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hRinf).const_mul 16
      refine Tendsto.congr (fun n => ?_) hbase
      push_cast
      ring
    have hsum : Tendsto (fun n : ℕ =>
        q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n) (S n) +
          16 * ((R n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using hfree0.add hRterm
    refine Tendsto.congr (fun n => ?_) hsum
    rw [q1ActualLongTailEnvelope_eq]
  exact actualQ1EigenvaluePowerSums_tendsto p a b M r hp ha hb hab hM f hf
    hF t ht hlong δ hδpos hδ0 hN hm lam hlam hRiesz R hR1 hcut henv hPert
    Bω hBω Cref hCref j

end Hurst
