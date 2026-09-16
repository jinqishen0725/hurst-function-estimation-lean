import Hurst.KernelEnergyRate
import Hurst.KernelEnergyRateDischarge
import Hurst.E5BiasEnvelope
import Hurst.LocalWeightSupport

/-!
# The energy-to-rate bridge, final form: polynomial bandwidth, the R-balance,
and the honest joint window

This file assembles the deterministic input set of the dimension-weighted kernel
energy rate `kernelEnergy_card_rate` (`Hurst.KernelEnergyRate`) at the POLYNOMIAL
bandwidth `δ n = n^{-γ}` (`S n = n^{1-γ}`, `card ≍ 2 S`), and lands the honest
joint-window verdict.

## Item 1 (landed, feasible): the R-balance at the unweighted level

With the cutoff-exponent window `0 < γ' < 1 - 2ψ` (where `ψ = 2 - 2 h0`, i.e.
`γ' < 4 h0 - 3`, nonempty exactly for `h0 > 3/4`), the choice `R = ⌊S^{γ'}⌋ + 1`
satisfies BOTH
* the band decay: `S^(2ψ-2) * card * (2R+1) ~ S^{2ψ-1+γ'} -> 0` (the A-side band
  energy decays at this rate by `realScaleMeshBandEnergy_scaled_le`, consumed by
  `hurstHolder_q1_actual_correlation_band_energy_tendsto_zero`), AND
* the tail-envelope decay: `q1ActualLongTailEnvelope -> 0`, term by term — the
  `16/(R+1)` term dies since `R -> ∞`, and the free part dies under the grid
  window `(1-γ) ψ < min(1, 2-2b)` (its grid term is `(2S)^ψ · gridCovarianceError
  ~ n^{(1-γ)ψ} · (1+log 2n) · (n^{-1} + n^{2b-2})`; the log factors are absorbed
  polynomially, the P7RowBound-style mesh domination).

`poly_bandwidth_cut_envelope_balance` is this R-balance, with the free part
discharged CONCRETELY from the polynomial bandwidth (no free-part hypothesis).
`poly_bandwidth_window_nonempty`: the bandwidth window `0 < γ < 1`,
`(1-γ) ψ < min(1, 2-2b)` is nonempty for EVERY `h0 > 3/4`, `b < 1`.

## Item 2 (landed, honest bookkeeping): the card-weighted envelope R-term

The card-weighted envelope square decomposes through the exact identity
`q1ActualLongTailEnvelope_eq` (`envelope = free + 16/(R+1)`, so the `R`-exponent
is `θ = 1`): the R-term contributes `card * (16/(R+1))² ≤ 768 · S^{1-2γ'} -> 0`
iff `γ' > 1/2` (`card_tailEnvelope_Rterm_sq_tendsto`).  Jointly with the band
window `γ' < 1 - 2ψ` this needs `1/2 < 1 - 2ψ`, i.e. `ψ < 1/4`, i.e. `h0 > 7/8`
— the mission's narrowed window.  NOTE the weights, however: the band window is
for the UNWEIGHTED band (`κ = 1`); the interface
`realScaleMeshEnergy_card_sub_tendsto_zero_of_relative` consumes all inputs at a
COMMON `κ`, so the window `1/2 < γ' < 1 - 2ψ` does NOT feed the `κ = card`
chain.

## The verdict (documented, landed as theorems)

For the interface at `κ = card` the band inputs require the card-weighted band
`card · band ≤ 3S · cut` to decay, i.e. the STRENGTHENED cutoff `S · cut -> 0`,
which is refuted for every `R ≥ 1` under the ordinary model (repo finding
`strengthened_cutoff_unsatisfiable`); at the polynomial bandwidth this is
`poly_bandwidth_strengthened_cutoff_unsatisfiable` below: the exponent
bookkeeping is `S·cut ~ S^{2ψ+γ'} -> ∞` for every `γ' > 0`, `h0 < 1` (since
`2ψ = 4 - 4h0 > 0`).  Hence item 3 — producing the `hPert` rate (`κ = card`)
from the ordinary model through `kernelEnergy_card_rate` — is NOT derivable: a
composed theorem with the card-weighted band inputs would be vacuous.  The
honest composition (`poly_bandwidth_kernel_energy_tendsto`) lands the UNWEIGHTED
energy rate at the polynomial bandwidth, consuming the R-balance and the
reference-side (`q1RieszActiveKernel`) bounds, exactly the hypothesis shape of
`hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz`.

Relation to the E5 window (`Hurst.E5BiasEnvelope`, file 24 §E5): the E5
grid-error headroom window is `γ + 2b < 2`; this file's envelope grid window is
`(1-γ) ψ < 2 - 2b`.  The two govern different layers (grid-covariance bias vs.
kernel-tail envelope); each consumer takes its own window as an explicit
hypothesis — no joint nonemptiness is claimed here (near `b -> 1` they pinch
against each other for fixed `ψ > 0`).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter
open scoped Topology

namespace Hurst

/-! ## Polynomial-bandwidth plumbing -/

/-- The `n * n^{-γ} = n^{1-γ}` identity (the `S`-side shape used throughout). -/
theorem natR_mul_rpow_neg (γ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (n : ℝ) ^ (-γ) = (n : ℝ) ^ (1 - γ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) * (n : ℝ) ^ (-γ) = (n : ℝ) ^ ((1 : ℝ)) * (n : ℝ) ^ (-γ) := by
    rw [show (n : ℝ) ^ ((1 : ℝ)) = n from Real.rpow_one n]
  rw [h1, ← Real.rpow_add hn0 1 (-γ),
    show (1 : ℝ) + (-γ) = (1 : ℝ) - γ from by ring]

/-- `S n = n · δ n = n^{1-γ}` diverges at the polynomial bandwidth. -/
theorem natR_mul_rpow_neg_tendsto_atTop (γ : ℝ) (hγpos : 0 < γ) (hγlt : γ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - γ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
      tendsto_natCast_atTop_atTop
  refine Tendsto.congr ?_ h
  intro n
  rcases Nat.eq_zero_or_pos n with hz | hp
  · subst hz
    rw [Nat.cast_zero, show (0 : ℝ) ^ ((1 : ℝ) - γ) = 0 from Real.zero_rpow (by linarith),
      show (0 : ℝ) ^ (-γ) = 0 from Real.zero_rpow (by linarith), mul_zero]
  · rw [natR_mul_rpow_neg γ n (by omega)]

/-! ## Item 1a: the envelope free part under the polynomial bandwidth -/

/-- **The R-free envelope part dies under the polynomial bandwidth.**  With
`δ n = n^{-γ}`, `S n = n^{1-γ}`, `ψ = 2 - 2 h0`: the `D`- and `exp`-terms are
`O(n^{-γ})` up to polynomially-absorbed log factors and die for `γ > 0`; the
grid term `(2S)^ψ · gridCovarianceError b C₀ n` is
`O(n^{(1-γ)ψ} · (1+log 2n) · (n^{-1} + n^{2b-2}))` and dies in the window
`(1-γ) ψ < 1` and `(1-γ) ψ < 2 - 2b` (the P7RowBound-style mesh domination:
`mesh_log_power_rpow_tendsto`). -/
theorem poly_tailEnvelopeFreePart_tendsto_zero
    (b C₀ Ctail L M h0 γ : ℝ) (hb : b < 1) (hC₀ : 0 ≤ C₀) (hCtail : 0 ≤ Ctail)
    (hL : 0 < L) (hM : 0 ≤ M) (hγpos : 0 < γ) (hγlt : γ < 1)
    (hgrid1 : (1 - γ) * (2 - 2 * h0) < 1)
    (hgrid2 : (1 - γ) * (2 - 2 * h0) < 2 - 2 * b) :
    Tendsto (fun n : ℕ => q1TailEnvelopeFreePart b C₀ Ctail L M h0 n
      ((n : ℝ) ^ (-γ)) ((n : ℝ) ^ (1 - γ))) atTop (𝓝 0) := by
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hcL : (0 : ℝ) ≤ 2 * L * (1 + M) :=
    mul_nonneg (mul_nonneg (by norm_num) hL.le) (add_nonneg zero_le_one hM)
  have hD0 : Tendsto (fun n : ℕ => 2 * L * (1 + M) * (n : ℝ) ^ (-γ)) atTop (𝓝 0) := by
    simpa [mul_zero, pow_zero, one_mul] using
      (mesh_log_power_rpow_tendsto (-γ) (by linarith) 0).const_mul (2 * L * (1 + M))
  have hlogle : ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have h2 := Real.log_le_log hn0 (show (n : ℝ) ≤ 2 * n by linarith)
    have h3 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hne]
    linarith
  have hub : Tendsto (fun n : ℕ => 2 * L * (1 + M) *
      ((1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (-γ))) atTop (𝓝 0) := by
    simpa [mul_zero] using
      (mesh_log_power_rpow_tendsto (-γ) (by linarith) 2).const_mul (2 * L * (1 + M))
  have hE0 : Tendsto (fun n : ℕ =>
      2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hub
    · filter_upwards [hn1] with n hn
      have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (-γ) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hlogne : (0 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      exact mul_nonneg (mul_nonneg hcL hrpow) hlogne
    · filter_upwards [hn1] with n hn
      have h1 := hlogle n hn
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hbase : (1 : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
        have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n : ℝ) by linarith)
        linarith
      have hx0 : (0 : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by linarith
      have hZ0 : (0 : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by linarith
      have hX0 : (0 : ℝ) ≤ (n : ℝ) ^ (-γ) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hlog0 : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hle1 : Real.log (n : ℝ) ≤ (1 + Real.log (2 * (n : ℝ))) ^ 2 := by
        refine le_trans (le_mul_of_one_le_right hlog0 hbase) ?_
        refine le_trans (mul_le_mul_of_nonneg_right h1 hZ0) ?_
        rw [pow_two]
      have hstep : 2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)
          ≤ 2 * L * (1 + M) * ((1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (-γ)) := by
        nlinarith [mul_le_mul_of_nonneg_right hle1 hX0,
          mul_le_mul_of_nonneg_left hle1 hcL, hcL, hX0]
      exact hstep
  have hExpE : Tendsto (fun n : ℕ =>
      Real.exp (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ))) atTop
      (𝓝 (Real.exp 0)) :=
    Tendsto.congr (fun _ => rfl) ((Real.continuous_exp.tendsto 0).comp hE0)
  have hExpEE : Tendsto (fun n : ℕ =>
      Real.exp (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)) *
        (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ))) atTop (𝓝 0) := by
    simpa [mul_zero] using hExpE.mul hE0
  -- the four terms of the free part
  have hsrc := hD0.const_mul (18 * Ctail)
  have hDc : Tendsto (fun n : ℕ => 18 * Ctail * (2 * L * (1 + M) * (n : ℝ) ^ (-γ)))
      atTop (𝓝 0) := by
    simpa [mul_zero] using hsrc
  have hterm : Tendsto (fun n : ℕ => 18 * Ctail * (2 * L * (1 + M) * (n : ℝ) ^ (-γ)) *
      (Real.exp (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)) *
        (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)))) atTop (𝓝 0) := by
    simpa [mul_zero] using hDc.mul hExpEE
  have hsrc9 := hExpEE.const_mul 9
  have h9 : Tendsto (fun n : ℕ => 9 * (Real.exp
      (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)) *
      (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)))) atTop (𝓝 0) := by
    simpa [mul_zero] using hsrc9
  have hsrc15 := hD0.const_mul (3 / 2 : ℝ)
  have h15 : Tendsto (fun n : ℕ => (3 / 2 : ℝ) * (2 * L * (1 + M) * (n : ℝ) ^ (-γ)))
      atTop (𝓝 0) := by
    simpa [mul_zero] using hsrc15
  -- the grid term: `(2S)^ψ · gridCovarianceError` in the exponent window
  have hspl : ∀ n : ℕ, (2 * (n : ℝ) ^ (1 - γ)) ^ (2 - 2 * h0)
      = 2 ^ (2 - 2 * h0) * (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0)) := by
    intro n
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _),
      Real.rpow_mul (Nat.cast_nonneg n)]
  have hm1 := (mesh_log_power_rpow_tendsto
    ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ)) (by linarith) 1).const_mul
    (4 * 2 ^ (2 - 2 * h0) * C₀)
  have hm2 := (mesh_log_power_rpow_tendsto
    ((1 - γ) * (2 - 2 * h0) + (2 * b - 2)) (by linarith) 1).const_mul
    (4 * 2 ^ (2 - 2 * h0) * C₀)
  have hA : Tendsto (fun n : ℕ => 4 * 2 ^ (2 - 2 * h0) * C₀ *
      ((1 + Real.log (2 * (n : ℝ))) *
        (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ)))) atTop (𝓝 0) := by
    simpa [pow_one, mul_zero] using hm1
  have hB : Tendsto (fun n : ℕ => 4 * 2 ^ (2 - 2 * h0) * C₀ *
      ((1 + Real.log (2 * (n : ℝ))) *
        (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (2 * b - 2)))) atTop (𝓝 0) := by
    simpa [pow_one, mul_zero] using hm2
  have hsum4 : Tendsto (fun n : ℕ =>
      4 * 2 ^ (2 - 2 * h0) * C₀ * ((1 + Real.log (2 * (n : ℝ))) *
        (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ))) +
      4 * 2 ^ (2 - 2 * h0) * C₀ * ((1 + Real.log (2 * (n : ℝ))) *
        (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (2 * b - 2)))) atTop (𝓝 0) := by
    simpa [add_zero] using hA.add hB
  have h4 : Tendsto (fun n : ℕ => 4 * (2 * (n : ℝ) ^ (1 - γ)) ^ (2 - 2 * h0) *
      gridCovarianceError b C₀ n) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hsum4
    filter_upwards [hn1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hshow1 : (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ)) =
        (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0)) * (n : ℝ) ^ ((-1 : ℝ)) :=
      Real.rpow_add hn0 _ _
    have hshow2 : (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (2 * b - 2)) =
        (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0)) * (n : ℝ) ^ (2 * b - 2) :=
      Real.rpow_add hn0 _ _
    unfold gridCovarianceError
    calc 4 * 2 ^ (2 - 2 * h0) * C₀ * ((1 + Real.log (2 * (n : ℝ))) *
            (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (-1 : ℝ))) +
        4 * 2 ^ (2 - 2 * h0) * C₀ * ((1 + Real.log (2 * (n : ℝ))) *
          (n : ℝ) ^ ((1 - γ) * (2 - 2 * h0) + (2 * b - 2)))
      _ = 4 * 2 ^ (2 - 2 * h0) * C₀ * ((1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ ((1 - γ) * (2 - 2 * h0)) *
              ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)))) := by rw [hshow1, hshow2]; ring
      _ = 4 * (2 * (n : ℝ) ^ (1 - γ)) ^ (2 - 2 * h0) *
            (C₀ * (1 + Real.log (2 * (n : ℝ))) *
              ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))) := by rw [hspl n]; ring
  have hpre := ((hDc.add hterm).add h9).add (h15.add h4)
  have htot : Tendsto (fun n : ℕ => 18 * Ctail * (2 * L * (1 + M) * (n : ℝ) ^ (-γ)) +
      18 * Ctail * (2 * L * (1 + M) * (n : ℝ) ^ (-γ)) *
        (Real.exp (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)) *
          (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ))) +
      9 * (Real.exp (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ)) *
        (2 * L * (1 + M) * (n : ℝ) ^ (-γ) * Real.log (n : ℝ))) +
      ((3 / 2 : ℝ) * (2 * L * (1 + M) * (n : ℝ) ^ (-γ)) +
        4 * (2 * (n : ℝ) ^ (1 - γ)) ^ (2 - 2 * h0) *
          gridCovarianceError b C₀ n)) atTop (𝓝 0) := by
    simpa [add_zero] using hpre
  refine Tendsto.congr' (Eventually.of_forall fun n => ?_) htot
  unfold q1TailEnvelopeFreePart
  ring

/-! ## Item 1b: the R-balance (band decay AND envelope decay) -/

/-- **The polynomial-bandwidth R-balance (item 1 of the bridge).**  Under the
ordinary-model data at `h0 > 3/4` (so the cutoff-exponent window
`0 < γ' < 1 - 2ψ = 4 h0 - 3` is nonempty) and the bandwidth `δ n = n^{-γ}`,
`S n = n^{1-γ}`, there EXISTS a cutoff `R` (the internal choice is
`R n = ⌊S n^{γ'}⌋ + 1` for some `γ' ∈ (0, 4 h0 - 3)`, per
`ordinary_cutoff_satisfiable`) such that ALL FOUR hold: `R ≥ 1` eventually,
`R -> ∞`, the band cutoff `S^(2ψ-2) * card * (2R+1) -> 0` (band decay:
`~ S^{2ψ-1+γ'} -> 0`, i.e. `γ' < 1 - 2ψ`), AND the full tail envelope
`q1ActualLongTailEnvelope -> 0` (concretely discharged: no free-part
hypothesis). -/
theorem poly_bandwidth_cut_envelope_balance
    (b C₀ Ctail L M h0 t γ : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hb : b < 1) (hC₀ : 0 ≤ C₀) (hCtail : 0 ≤ Ctail)
    (hL : 0 < L) (hM : 0 ≤ M) (hh0 : 3 / 4 < h0)
    (hγpos : 0 < γ) (hγlt : γ < 1)
    (hgrid1 : (1 - γ) * (2 - 2 * h0) < 1)
    (hgrid2 : (1 - γ) * (2 - 2 * h0) < 2 - 2 * b) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => (R n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 - γ)) ^ (2 * (2 - 2 * h0) - 2) *
        ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => q1ActualLongTailEnvelope b C₀ Ctail L M h0 n
        ((n : ℝ) ^ (-γ)) ((n : ℝ) ^ (1 - γ)) (R n)) atTop (𝓝 0) := by
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hStop : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - γ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
      tendsto_natCast_atTop_atTop
  have hcardub : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ)
        ≤ 3 * (n : ℝ) ^ (1 - γ) := by
    filter_upwards [hn1] with n hn
    have hn0 : 0 < n := by omega
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn
    have hδ : (0 : ℝ) < (n : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hn0' _
    have hN1 : (1 : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ (-γ) := by
      rw [natR_mul_rpow_neg γ n hn]
      exact Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
    have hcard := localWeightActiveSet_card n 1 hn0 ((n : ℝ) ^ (-γ)) t hδ hN1
    rw [natR_mul_rpow_neg γ n hn] at hcard
    exact hcard
  obtain ⟨R, hR1, hRtop, hcut⟩ :=
    ordinary_cutoff_satisfiable h0
      (fun n => (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card)
      (fun n => (n : ℝ) ^ (1 - γ)) hStop hcardub hh0
  refine ⟨R, hR1, hRtop, hcut, ?_⟩
  -- the envelope: free part (concretely) + 16/(R+1) (from R -> ∞)
  have hRinf : Tendsto (fun n : ℕ => ((R n : ℝ) + 1)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro β
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hRtop.eventually_ge_atTop (β - 1))
    exact ⟨N, fun a ha => by have hle := hN a ha; linarith⟩
  have hbase : Tendsto (fun n : ℕ => 16 * ((R n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hRinf).const_mul 16
  have hRterm : Tendsto (fun n : ℕ => 16 * ((R n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => ?_) hbase
    push_cast
    ring
  have hfree := poly_tailEnvelopeFreePart_tendsto_zero b C₀ Ctail L M h0 γ hb hC₀
    hCtail hL hM hγpos hγlt hgrid1 hgrid2
  have hsum : Tendsto (fun n : ℕ => q1TailEnvelopeFreePart b C₀ Ctail L M h0 n
      ((n : ℝ) ^ (-γ)) ((n : ℝ) ^ (1 - γ)) +
      16 * ((R n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [add_zero] using hfree.add hRterm
  refine Tendsto.congr (fun n => ?_) hsum
  rw [q1ActualLongTailEnvelope_eq]

/-! ## The bandwidth window is nonempty -/

/-- **Nonemptiness of the polynomial-bandwidth window.**  For every long-memory
`h0 > 3/4` and `b < 1` there is a bandwidth exponent `γ ∈ (0, 1)` in the joint
window `(1-γ) (2-2h0) < 1` and `(1-γ) (2-2h0) < 2 - 2b` (the two exponent
conditions of the free-part grid term).  Explicit choice: `γ = 1 - u` with
`u = min(1/2, c/(2ψ))`, `c = min(1, 2-2b)`, so `(1-γ)ψ ≤ c/2 < c`. -/
theorem poly_bandwidth_window_nonempty (h0 b : ℝ) (hh0 : 3 / 4 < h0) (hh0lt : h0 < 1)
    (hb : b < 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
      (1 - γ) * (2 - 2 * h0) < 1 ∧ (1 - γ) * (2 - 2 * h0) < 2 - 2 * b := by
  have hψpos : (0 : ℝ) < 2 - 2 * h0 := by linarith
  have hψne : (2 - 2 * h0) ≠ 0 := ne_of_gt hψpos
  have hyne : (1 - h0) ≠ 0 := by linarith
  have hcpos : (0 : ℝ) < min 1 (2 - 2 * b) := lt_min zero_lt_one (by linarith)
  obtain ⟨u, hu1, hu2, hupos⟩ :
      ∃ u : ℝ, u ≤ 1 / 2 ∧ u ≤ min 1 (2 - 2 * b) / (2 * (2 - 2 * h0)) ∧ 0 < u :=
    ⟨min (1 / 2 : ℝ) (min 1 (2 - 2 * b) / (2 * (2 - 2 * h0))),
      min_le_left _ _,
      min_le_right _ _,
      lt_min (by norm_num) (div_pos hcpos (by linarith))⟩
  have hkey : (1 - (1 - u)) * (2 - 2 * h0) ≤ min 1 (2 - 2 * b) / 2 := by
    have h1 : (1 - (1 - u)) * (2 - 2 * h0) = u * (2 - 2 * h0) := by ring
    rw [h1]
    calc u * (2 - 2 * h0)
        ≤ (min 1 (2 - 2 * b) / (2 * (2 - 2 * h0))) * (2 - 2 * h0) :=
          mul_le_mul_of_nonneg_right hu2 hψpos.le
      _ = min 1 (2 - 2 * b) / 2 := by field_simp
  refine ⟨1 - u, by linarith, by linarith, ?_, ?_⟩
  · have hmin1 : min 1 (2 - 2 * b) ≤ 1 := min_le_left _ _
    linarith
  · have hmin2 : min 1 (2 - 2 * b) ≤ 2 - 2 * b := min_le_right _ _
    linarith

/-! ## Item 2: the card-weighted envelope R-term (θ = 1 bookkeeping) -/

/-- **The card-weighted R-term of the envelope square.**  Through the envelope
identity `q1ActualLongTailEnvelope_eq` the `R`-term has exponent `θ = 1`
(`16/(R+1)`); weighted by an abstract cardinality `card ≤ 3S` and squared it is
bounded by `768 · S^{1-2γ'}` at the explicit cutoff `R = ⌊S^{γ'}⌋ + 1`, i.e.
`card * (16/(R+1))² -> 0` iff `γ' > 1/2`.  Jointly with the UNWEIGHTED band
window `γ' < 1 - 2ψ` this needs `ψ < 1/4` (`h0 > 7/8`) — and note the weights
differ (`κ = 1` band vs `κ = card` envelope), so this window does NOT feed the
common-`κ` interface (see `poly_bandwidth_strengthened_cutoff_unsatisfiable`). -/
theorem card_tailEnvelope_Rterm_sq_tendsto
    (S card : ℕ → ℝ) (γ' : ℝ)
    (hS : Tendsto S atTop atTop) (hS1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n)
    (hcardub : ∀ᶠ n in atTop, card n ≤ 3 * S n)
    (hcardpos : ∀ᶠ n in atTop, 0 ≤ card n)
    (hγ' : 1 / 2 < γ') :
    Tendsto (fun n : ℕ => card n *
      (16 * ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
  have hneg : (-(2 * γ' - 1) : ℝ) < 0 := by linarith
  have hupper : Tendsto (fun n : ℕ => 768 * S n ^ (-(2 * γ' - 1))) atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_neg_of_atTop S (-(2 * γ' - 1)) hneg hS).const_mul 768
  apply squeeze_zero'
  · filter_upwards [hcardpos] with n hcardn
    exact mul_nonneg hcardn (sq_nonneg _)
  · filter_upwards [hS1, hcardub] with n hS1n hcardn
    have hSn : (0 : ℝ) < S n := lt_of_lt_of_le zero_lt_one hS1n
    have ha0 : (0 : ℝ) < S n ^ γ' := Real.rpow_pos_of_pos hSn _
    have hR1c : (1 : ℝ) ≤ ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ) :=
      by exact_mod_cast Nat.le_add_left 1 (Nat.floor (S n ^ γ'))
    have hfloorpos : (0 : ℝ) < ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_one hR1c
    have hfloorlt : S n ^ γ' < ((Nat.floor (S n ^ γ') : ℝ) + 1) :=
      Nat.lt_floor_add_one (S n ^ γ')
    have hge : S n ^ γ' ≤ ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ) := by
      have hfl := Nat.lt_floor_add_one (S n ^ γ')
      push_cast
      linarith
    have hinvle : ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ)⁻¹ ≤ (S n ^ γ')⁻¹ :=
      (inv_le_inv₀ hfloorpos ha0).2 hge
    have hsq : (16 * ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ)⁻¹) ^ 2
        ≤ (16 * (S n ^ γ')⁻¹) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num)
        (inv_nonneg.mpr hfloorpos.le))
        (mul_le_mul_of_nonneg_left hinvle (by norm_num)) 2
    have hsplit : (16 * (S n ^ γ')⁻¹) ^ 2 = 256 * ((S n ^ γ')⁻¹ * (S n ^ γ')⁻¹) := by
      rw [mul_pow, pow_two ((S n ^ γ')⁻¹),
        show (16 : ℝ) ^ 2 = 256 from by norm_num]
    have hjoin : (S n ^ γ')⁻¹ * (S n ^ γ')⁻¹ = ((S n : ℝ) ^ (2 * γ'))⁻¹ := by
      rw [← mul_inv (S n ^ γ') (S n ^ γ'), ← Real.rpow_add hSn γ' γ',
        show γ' + γ' = (2 : ℝ) * γ' from by ring]
    have hc3n : (0 : ℝ) ≤ 3 * S n := by linarith
    have hlast : (S n : ℝ) * (S n : ℝ) ^ (-(2 * γ'))
        = (S n : ℝ) ^ (-(2 * γ' - 1)) := by
      have h1 : (S n : ℝ) * (S n : ℝ) ^ (-(2 * γ'))
          = (S n : ℝ) ^ ((1 : ℝ)) * (S n : ℝ) ^ (-(2 * γ')) := by
        rw [show (S n : ℝ) ^ ((1 : ℝ)) = S n from Real.rpow_one (S n)]
      rw [h1, ← Real.rpow_add hSn 1 (-(2 * γ')),
        show (1 : ℝ) + -(2 * γ') = -(2 * γ' - 1) from by ring]
    calc card n * (16 * ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ)⁻¹) ^ 2
        ≤ (3 * S n) * (16 * ((Nat.floor (S n ^ γ') + 1 : ℕ) : ℝ)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right hcardn (sq_nonneg _)
      _ ≤ (3 * S n) * (16 * (S n ^ γ')⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hc3n
      _ = 768 * (S n * ((S n ^ γ')⁻¹ * (S n ^ γ')⁻¹)) := by rw [hsplit]; ring
      _ = 768 * (S n * ((S n : ℝ) ^ (2 * γ'))⁻¹) := by rw [hjoin]
      _ = 768 * (S n * (S n : ℝ) ^ (-(2 * γ'))) := by
            exact congrArg (fun x => 768 * (S n * x)) (Real.rpow_neg hSn.le (2 * γ')).symm
      _ = 768 * (S n : ℝ) ^ (-(2 * γ' - 1)) := by rw [hlast]
  · exact hupper

/-! ## The verdict: the common-κ = card chain is refuted at the polynomial bandwidth -/

/-- **The strengthened cutoff is unsatisfiable at the polynomial bandwidth.**
For `δ n = n^{-γ}`, `S n = n^{1-γ}`, EVERY cutoff `R` eventually `≥ 1`, and
every `h0 < 1`, the strengthened cutoff `S·cut = S^(2ψ-2) · card · (2R+1) · S`
does NOT tend to zero: `card ≍ 2S` and `2ψ = 4 - 4h0 > 0` give the lower bound
`3 · S^{2ψ} -> ∞`.  Consequently the band bridges
`kernelBandActual_card_tendsto_zero_of_cut` /
`kernelBandRiesz_card_tendsto_zero_of_cut` of `Hurst.KernelEnergyRate` can never
be supplied under the polynomial bandwidth, and the composed `hPert` rate
(item 3, `κ = card`) is not derivable through the common-`κ` interface — the
window bookkeeping (`γ' > 1/2` for the card-weighted envelope R-term,
`γ' < 1 - 2ψ` for the unweighted band, `γ' < -2ψ < 0` for the card-weighted
band) resolves to an EMPTY window in the only configuration the interface
accepts. -/
theorem poly_bandwidth_strengthened_cutoff_unsatisfiable
    (h0 t γ : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hh0 : h0 < 1)
    (hγpos : 0 < γ) (hγlt : γ < 1)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n) :
    ¬ Tendsto (fun n : ℕ => ((n : ℝ) * (n : ℝ) ^ (-γ)) ^ (2 * (2 - 2 * h0) - 2) *
        ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
        (2 * (R n : ℝ) + 1) * ((n : ℝ) * (n : ℝ) ^ (-γ))) atTop (𝓝 0) := by
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
    filter_upwards [hn1] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hδ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_of_atTop (fun n : ℕ => (n : ℝ)) (-γ) (by linarith)
      tendsto_natCast_atTop_atTop
  have hN := natR_mul_rpow_neg_tendsto_atTop γ hγpos hγlt
  exact strengthened_cutoff_unsatisfiable h0 t ht hh0
    (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN R hR

/-! ## Item 3: the honest composed theorem (unweighted energy rate) -/

/-- **The composed kernel-energy rate at the polynomial bandwidth (honest
form).**  The R-balance (`poly_bandwidth_cut_envelope_balance`) supplies, for a
single explicit cutoff `R`, the deterministic cutoff input `hcut` AND the
tail-envelope input `hEnv` of the kernel-energy squeeze
`hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz`; together with the
reference-side bounds (`hBnear`, `hBbound`, quantified over the cutoff, at the
same polynomial data) this yields the (unweighted) energy rate
`realScaleMeshEnergy S (A - B) -> 0`.

This is the maximal non-vacuous composition: the dimension-weighted analogue
(κ = card, the `hPert` shape) is refuted per
`poly_bandwidth_strengthened_cutoff_unsatisfiable`, since the weighted band
inputs of `kernelEnergy_card_rate` require the strengthened cutoff `S·cut -> 0`. -/
theorem poly_bandwidth_kernel_energy_tendsto
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγpos : 0 < γ) (hγlt : γ < 1)
    (hgrid1 : (1 - γ) * (2 - 2 * f t) < 1)
    (hgrid2 : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (Cref : ℝ) (hCref : 0 ≤ Cref)
    (hBnear : ∀ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) →
      Tendsto (fun n : ℕ => realScaleMeshBandEnergy
        ((n : ℝ) * (n : ℝ) ^ (-γ)) (R n)
        (q1RieszActiveKernel n ((n : ℝ) ^ (-γ)) t
          ((n : ℝ) * (n : ℝ) ^ (-γ)) (2 - 2 * f t)
          (f t * (2 * f t - 1)))) atTop (𝓝 0))
    (hBbound : ∀ R : ℕ → ℕ, ∀ᶠ n : ℕ in atTop,
      realScaleMeshEnergy ((n : ℝ) * (n : ℝ) ^ (-γ))
        (q1RieszActiveKernel n ((n : ℝ) ^ (-γ)) t
          ((n : ℝ) * (n : ℝ) ^ (-γ)) (2 - 2 * f t)
          (f t * (2 * f t - 1))) ≤ Cref) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => realScaleMeshEnergy
        ((n : ℝ) * (n : ℝ) ^ (-γ))
        (fun i j => q1ActualLongActiveKernel f hf n ((n : ℝ) ^ (-γ)) t
            ((n : ℝ) * (n : ℝ) ^ (-γ)) (2 - 2 * f t) i j -
          q1RieszActiveKernel n ((n : ℝ) ^ (-γ)) t
            ((n : ℝ) * (n : ℝ) ^ (-γ)) (2 - 2 * f t)
            (f t * (2 * f t - 1)) i j)) atTop (𝓝 0) := by
  obtain ⟨Ccov, hCcov0, Ctail, hCtail0, L, hL0, hchain⟩ :=
    hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz
      p a b M hp ha hb hab hM f hf hF t ht hlong
  obtain ⟨R, hR1, hRtop, hcut, hEnv⟩ :=
    poly_bandwidth_cut_envelope_balance b Ccov Ctail L M (f t) t γ ht hb hCcov0
      hCtail0 hL0 hM hlong hγpos hγlt hgrid1 hgrid2
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
    filter_upwards [hn1] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hN := natR_mul_rpow_neg_tendsto_atTop γ hγpos hγlt
  have hcut' : Tendsto (fun n : ℕ =>
      ((n : ℝ) * (n : ℝ) ^ (-γ)) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hcut
    filter_upwards [hn1] with n hn
    rw [natR_mul_rpow_neg γ n hn]
  have hEnv' : Tendsto (fun n : ℕ => q1ActualLongTailEnvelope b Ccov Ctail L M
      (f t) n ((n : ℝ) ^ (-γ)) ((n : ℝ) * (n : ℝ) ^ (-γ)) (R n)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hEnv
    filter_upwards [hn1] with n hn
    rw [natR_mul_rpow_neg γ n hn]
  exact ⟨R, hR1, hchain (fun n : ℕ => (n : ℝ) ^ (-γ)) R hδpos hN hR1 hcut' hEnv'
    Cref hCref (hBnear R hR1) (hBbound R)⟩

end Hurst
