import Hurst.KernelEnergyRateDischarge
import Hurst.ActualFirstLongHilbertSchmidt
import Hurst.FirstLongRieszEnergy
import Hurst.ActiveWindowGeometry

/-!
# Discharge round, part 2: the parameter balance made formal

This file completes the discharge of the `hPert` hypothesis of
`Hurst.ActualQuadratureConfluence` up to its honest residual, by CHOOSING
the free cutoff `R(n)`.

## The verified balance (against the literal repo definitions)

* The long-tail envelope `q1ActualLongTailEnvelope` (defined in
  `Hurst.ActualFirstLongHilbertSchmidt`) is EXACTLY
  `free part + 16 / (R + 1)`: its explicit `R`-exponent is
  `theta = 1` (`tailEnvelope_decay_of_R` below; the free part carries the
  `n`-decay `18*Ctail*D*(1 + e^E*E) + 9*e^E*E + 1.5*D + 4*(2S)^psi*gridCov
  with `D = 2L(1+M)delta`, `E = D*log n`).
* The relative comparison `|q1A - q1R| <= e * |q1R|`
  (`scaled_tail_error_to_relative_riesz`,
  `Hurst.ActualFirstLongHilbertSchmidt` / `Hurst.ActualFirstLongOffDiagonal`)
  holds ONLY off the band (`R < Nat.dist`): the repo has NO
  relative-on-band extension, so the mission's fallback applies.
* With `R = floor(S^gamma) + 1`, `card <= 3S` (`card ~ 2S`), the ordinary
  cutoff `S^(2psi-2) * card * (2R+1) -> 0` needs `gamma < 4h0 - 3`,
  the weighted envelope rate `card * (envelope/c)^2 -> 0` needs
  `gamma > 1/2` (given the `sqrt card * free -> 0` free-part rate): the
  feasible interval `1/2 < gamma < 4h0 - 3` is NONEMPTY exactly for
  `h0 > 7/8` (`R_balance_exists` below).
* RESIDUAL (the mission's fallback, honestly landed): the band part of the
  card-weighted energy CANNOT be driven to zero by any choice of `R`.
  On the band the comparison entries are `Theta(S^psi)`-scale (the Riesz
  band entry at rank distance `1 <= d <= R` is `c*(S/d)^psi >= c*S^{psi(1-gamma)}`,
  and the actual band carries the diagonal `u_i * S^psi` since the Riesz
  kernel vanishes there), so `card * bandEnergy = Theta(S^{2psi} * R^{1-2psi})`
  up to weight constants: divergent for every `gamma >= 0` when
  `0 < psi < 1/2` and the row weights do not vanish.  This is the same
  diagonal obstruction recorded in
  `strengthened_cutoff_unsatisfiable`
  (`Hurst.KernelEnergyRateDischarge`).  The discharge therefore concludes
  `hPert` from (i) the balance (item 2), (ii) the off-band relative
  comparison (`q1_pair_offband_relative`), and (iii) the single remaining
  explicit band-rate hypothesis `hband`, documented at its exact
  `Theta(S^{2psi} R^{1-2psi})` strength, plus the quantitative
  weight-error rate `card * w^2 -> 0` (the known item-3 upgrade of
  `Hurst.KernelEnergyRateDischarge`).

## Main contents

* `q1BalanceCutoff` + `q1BalanceCutoff_tendsto_atTop` : the explicit
  cutoff choice `R n = floor(S n ^ gamma) + 1` and its `R -> oo` property;
* `tailEnvelope_decay_of_R` : the envelope's explicit `R`-decay at
  exponent `theta = 1`;
* `R_balance_exists` : the joint satisfiability of `1 <= R`, `R -> oo`,
  the ordinary cutoff, and the weighted envelope rate
  `card * (envelope/c)^2 -> 0`, at `gamma in (1/2, 4h0-3)`;
* `q1_pair_offband_relative` : the off-band relative comparison for the
  concrete unweighted comparison pair, in filter form;
* `hPert_discharged` : the `hPert` Tendsto of
  `Hurst.ActualQuadratureConfluence`, concluded from the balance, the
  off-band comparison, the reference-energy constant, and the two
  documented residuals (`hband`, `hκw`).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter
open scoped Topology

namespace Hurst

/-! ## The explicit cutoff choice -/

/-- The parameter-balance cutoff: `R n = floor(S n ^ gamma) + 1`. -/
def q1BalanceCutoff (S : ℕ → ℝ) (γ : ℝ) : ℕ → ℕ :=
  fun n => Nat.floor (S n ^ γ) + 1

theorem q1BalanceCutoff_pos (S : ℕ → ℝ) (γ : ℝ) (n : ℕ) : 1 ≤ q1BalanceCutoff S γ n :=
  Nat.le_add_left 1 _

theorem q1BalanceCutoff_le (S : ℕ → ℝ) (γ : ℝ) (n : ℕ) (hS : 0 ≤ S n) :
    ((q1BalanceCutoff S γ n : ℕ) : ℝ) ≤ S n ^ γ + 1 := by
  have hf := Nat.floor_le (Real.rpow_nonneg hS γ)
  show ((Nat.floor (S n ^ γ) + 1 : ℕ) : ℝ) ≤ S n ^ γ + 1
  push_cast
  linarith

theorem q1BalanceCutoff_gt (S : ℕ → ℝ) (γ : ℝ) (n : ℕ) : S n ^ γ < (q1BalanceCutoff S γ n : ℝ) := by
  have hlt := Nat.lt_floor_add_one (S n ^ γ)
  show S n ^ γ < ((Nat.floor (S n ^ γ) + 1 : ℕ) : ℝ)
  push_cast
  linarith

/-- The cutoff choice diverges along a divergent positive scale. -/
theorem q1BalanceCutoff_tendsto_atTop (S : ℕ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hS : Tendsto S atTop atTop) :
    Tendsto (fun n : ℕ => ((q1BalanceCutoff S γ n : ℕ) : ℝ)) atTop atTop := by
  have hSγ : Tendsto (fun n : ℕ => S n ^ γ) atTop atTop :=
    (tendsto_rpow_atTop hγ).comp hS
  refine (Filter.tendsto_atTop_atTop.mpr ?_)
  intro β
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hSγ.eventually_ge_atTop (β : ℝ))
  refine ⟨N, fun a ha => ?_⟩
  have hge : β ≤ S a ^ γ := hN a ha
  have hlt := q1BalanceCutoff_gt S γ a
  have hlt2 : β < ((q1BalanceCutoff S γ a : ℕ) : ℝ) := by linarith
  exact le_of_lt hlt2

/-! ## Item 1: the envelope's explicit R-decay (theta = 1) -/

/-- **The envelope's explicit `R`-decay.**  From the exact decomposition
`q1ActualLongTailEnvelope_eq`, the `R`-dependence of the long-tail
envelope is the single term `16 * (R+1)^{-1}`: the exponent is
`theta = 1`.  At the balance cutoff this is bounded by the free part
plus `16 * S^{-gamma}`. -/
theorem tailEnvelope_decay_of_R (b Ccov Ctail L M h0 γ : ℝ) (n : ℕ) (δ S : ℝ)
    (hγ : 0 < γ) (hS1 : 1 ≤ S) :
    q1ActualLongTailEnvelope b Ccov Ctail L M h0 n δ S
        (q1BalanceCutoff (fun _ => S) γ n) ≤
      q1TailEnvelopeFreePart b Ccov Ctail L M h0 n δ S + 16 * S ^ (-γ) := by
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS1
  have hγpos : 0 < S ^ γ := Real.rpow_pos_of_pos hSpos γ
  have hinv : ((q1BalanceCutoff (fun _ => S) γ n + 1 : ℕ) : ℝ)⁻¹ ≤ (S ^ γ)⁻¹ := by
    refine (inv_le_inv₀ (by positivity) hγpos).2 ?_
    have hlt := q1BalanceCutoff_gt (fun _ => S) γ n
    show S ^ γ ≤ ((q1BalanceCutoff (fun _ => S) γ n + 1 : ℕ) : ℝ)
    push_cast
    linarith
  have hconv : (S ^ γ)⁻¹ = S ^ (-γ) := by
    rw [← Real.rpow_neg (by linarith) γ]
  calc q1ActualLongTailEnvelope b Ccov Ctail L M h0 n δ S
        (q1BalanceCutoff (fun _ => S) γ n)
      = q1TailEnvelopeFreePart b Ccov Ctail L M h0 n δ S +
          16 * ((q1BalanceCutoff (fun _ => S) γ n + 1 : ℕ) : ℝ)⁻¹ :=
        q1ActualLongTailEnvelope_eq b Ccov Ctail L M h0 n δ S _
    _ ≤ q1TailEnvelopeFreePart b Ccov Ctail L M h0 n δ S + 16 * (S ^ γ)⁻¹ := by
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = q1TailEnvelopeFreePart b Ccov Ctail L M h0 n δ S + 16 * S ^ (-γ) := by
        rw [hconv]

/-! ## Item 2: the parameter balance (joint satisfiability) -/

/-- **The parameter balance (discharge items 1+2).**  At the explicit
cutoff `R n = floor(S n ^ gamma) + 1` with `gamma` in the feasible
interval `1/2 < gamma < 4*h0 - 3` (nonempty exactly when `h0 > 7/8`),
ALL FOUR of the following hold jointly:

1. `1 <= R n` (always),
2. `R n -> oo`,
3. the ordinary band cutoff `S^(2psi-2) * card * (2R+1) -> 0`,
4. the weighted envelope rate `card * (envelope / c)^2 -> 0`
   (with `c > 0` the Riesz constant), given the free-part rate
   `sqrt card * free -> 0`. -/
theorem R_balance_cutoff
    (b Ccov Ctail L M h0 c γ : ℝ) (hc : 0 < c)
    (card : ℕ → ℕ) (δ S : ℕ → ℝ)
    (hS : Tendsto S atTop atTop)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * S n)
    (hγ1 : 1 / 2 < γ) (hγ2 : γ + 3 < 4 * h0)
    (hfree : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
      q1TailEnvelopeFreePart b Ccov Ctail L M h0 n (δ n) (S n)) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, 1 ≤ q1BalanceCutoff S γ n) ∧
      Tendsto (fun n : ℕ => ((q1BalanceCutoff S γ n : ℕ) : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (S n) ^ (2 * (2 - 2 * h0) - 2) *
        (card n : ℝ) * (2 * ((q1BalanceCutoff S γ n : ℕ) : ℝ) + 1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (card n : ℝ) *
        (q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
          (q1BalanceCutoff S γ n) / c) ^ 2)
        atTop (𝓝 0) := by
  refine ⟨Eventually.of_forall fun _ => q1BalanceCutoff_pos S γ _,
    q1BalanceCutoff_tendsto_atTop S γ (by linarith) hS, ?_, ?_⟩
  · -- member 3: the ordinary cutoff, bounded by 15 * S^(gamma + 3 - 4h0)
    have hS1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n := hS.eventually_ge_atTop 1
    have hSγ1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n ^ γ :=
      ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hS).eventually_ge_atTop 1
    have hexp : 2 * (2 - 2 * h0) - 2 + 1 + γ = γ + 3 - 4 * h0 := by ring
    have hsmall := tendsto_rpow_neg_of_atTop S (γ + 3 - 4 * h0)
      (by linarith) hS
    apply squeeze_zero'
    · filter_upwards [hS1] with n hSn
      exact mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ S n) _)
        (Nat.cast_nonneg _)) (by positivity)
    · filter_upwards [hcardub, hS1, hSγ1] with n hc hSn hγ1
      have hRle := q1BalanceCutoff_le S γ n (by linarith)
      have hSn' : 0 < S n := lt_of_lt_of_le zero_lt_one hSn
      have hpow0 : 0 ≤ S n ^ (2 * (2 - 2 * h0) - 2) := by positivity
      have hband : (2 : ℝ) * ((q1BalanceCutoff S γ n : ℕ) : ℝ) + 1 ≤ 5 * S n ^ γ := by
        have h2 : (2 : ℝ) * ((q1BalanceCutoff S γ n : ℕ) : ℝ) ≤ 2 * (S n ^ γ + 1) := by
          exact mul_le_mul_of_nonneg_left hRle (by norm_num)
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
            (2 * ((q1BalanceCutoff S γ n : ℕ) : ℝ) + 1)
          ≤ (S n) ^ (2 * (2 - 2 * h0) - 2) * (3 * S n) * (5 * S n ^ γ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc hpow0) hband
              (by positivity) (by positivity)
        _ = 15 * (S n ^ (2 * (2 - 2 * h0) - 2) * S n * S n ^ γ) := by ring
        _ = 15 * S n ^ (γ + 3 - 4 * h0) := by rw [hkey]
    · simpa using hsmall.const_mul 15
  · -- member 4: card * (envelope / c)^2 -> 0, from sqrt card * env -> 0
    have hS1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ S n := hS.eventually_ge_atTop 1
    have hSγpos : ∀ᶠ n in atTop, 0 < (S n) ^ γ := by
      filter_upwards [hS1] with n hSn
      exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hSn) _
    have hRlt : ∀ᶠ n in atTop, S n ^ γ < ((q1BalanceCutoff S γ n : ℕ) : ℝ) :=
      Eventually.of_forall fun n => q1BalanceCutoff_gt S γ n
    -- sqrt card * 16/(R+1) <= 16 * sqrt 3 * S^(1/2 - gamma) -> 0
    have hinv : Tendsto (fun n : ℕ =>
        (16 : ℝ) * Real.sqrt 3 * S n ^ ((1 : ℝ) / 2 - γ)) atTop (𝓝 0) := by
      have hexpneg : (((1 : ℝ) / 2 - γ)) < 0 := by linarith
      simpa using (tendsto_rpow_neg_of_atTop S ((1 : ℝ) / 2 - γ) hexpneg
        hS).const_mul (16 * Real.sqrt 3)
    have hterm : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
        (16 * ((q1BalanceCutoff S γ n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun n => by positivity
      · filter_upwards [hcardub, hRlt, hSγpos, hS1] with n hc hf hγ hSn
        have hinvle : ((q1BalanceCutoff S γ n + 1 : ℕ) : ℝ)⁻¹ ≤ ((S n) ^ γ)⁻¹ :=
          (inv_le_inv₀ (by positivity) hγ).2 (by push_cast; linarith)
        have hsqrt : Real.sqrt ((card n : ℝ)) ≤ Real.sqrt ((3 : ℝ) * S n) :=
          Real.sqrt_le_sqrt hc
        have hsqrtform : Real.sqrt ((3 : ℝ) * S n)
            = Real.sqrt 3 * (S n) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
            (by linarith : (0 : ℝ) ≤ S n), Real.sqrt_eq_rpow]
        have hjoin' : (S n) ^ ((1 : ℝ) / 2) * ((S n) ^ γ)⁻¹
            = (S n) ^ ((1 : ℝ) / 2 - γ) := by
          have hSn' : 0 < S n := lt_of_lt_of_le zero_lt_one hSn
          rw [← Real.rpow_neg (by linarith : (0 : ℝ) ≤ S n) γ,
            ← Real.rpow_add hSn' ((1 : ℝ) / 2) (-(γ : ℝ)),
            show (((1 : ℝ) / 2 : ℝ) + (-(γ : ℝ))) = ((1 : ℝ) / 2 - γ) by ring]
        calc Real.sqrt ((card n : ℝ)) * (16 * ((q1BalanceCutoff S γ n + 1 : ℕ) : ℝ)⁻¹)
            = 16 * (Real.sqrt ((card n : ℝ)) * ((q1BalanceCutoff S γ n + 1 : ℕ) : ℝ)⁻¹) := by ring
          _ ≤ 16 * (Real.sqrt ((3 : ℝ) * S n) * ((q1BalanceCutoff S γ n + 1 : ℕ) : ℝ)⁻¹) :=
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
          _ = (16 : ℝ) * Real.sqrt 3 * S n ^ ((1 : ℝ) / 2 - γ) := by rw [hjoin']
      · exact hinv
    -- sqrt card * envelope -> 0 (the envelope is free + 16/(R+1) exactly)
    have hsqrtenv : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
        q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
          (q1BalanceCutoff S γ n)) atTop (𝓝 0) := by
      have hsum : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
          q1TailEnvelopeFreePart b Ccov Ctail L M h0 n (δ n) (S n) +
          Real.sqrt ((card n : ℝ)) * (16 * ((q1BalanceCutoff S γ n + 1 : ℕ) : ℝ)⁻¹))
          atTop (𝓝 0) := by
        simpa using hfree.add hterm
      refine Tendsto.congr (fun n => ?_) hsum
      rw [q1ActualLongTailEnvelope_eq]
      ring
    -- card * (env / c)^2 = (sqrt card * env / c)^2 -> 0
    have hsq0 : Tendsto (fun n : ℕ =>
        (Real.sqrt ((card n : ℝ)) *
          q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
            (q1BalanceCutoff S γ n) / c) *
        (Real.sqrt ((card n : ℝ)) *
          q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
            (q1BalanceCutoff S γ n) / c)) atTop (𝓝 0) := by
      have hd : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
          q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
            (q1BalanceCutoff S γ n) / c) atTop (𝓝 0) := by
        simpa using hsqrtenv.div_const c
      simpa using hd.mul hd
    refine Tendsto.congr (fun n => ?_) hsq0
    have hsqrt : Real.sqrt ((card n : ℝ)) ^ 2 = (card n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    calc Real.sqrt ((card n : ℝ)) *
            q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
              (q1BalanceCutoff S γ n) / c *
          (Real.sqrt ((card n : ℝ)) *
            q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
              (q1BalanceCutoff S γ n) / c)
        = Real.sqrt ((card n : ℝ)) ^ 2 *
            (q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
              (q1BalanceCutoff S γ n) / c) ^ 2 := by ring
      _ = (card n : ℝ) *
            (q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n)
              (q1BalanceCutoff S γ n) / c) ^ 2 := by rw [hsqrt]

/-- **The parameter balance (discharge item 2), existential packaging**
of `R_balance_cutoff` at its explicit witness `q1BalanceCutoff S γ`. -/
theorem R_balance_exists
    (b Ccov Ctail L M h0 c γ : ℝ) (hc : 0 < c)
    (card : ℕ → ℕ) (δ S : ℕ → ℝ)
    (hS : Tendsto S atTop atTop)
    (hcardub : ∀ᶠ n in atTop, (card n : ℝ) ≤ 3 * S n)
    (hγ1 : 1 / 2 < γ) (hγ2 : γ + 3 < 4 * h0)
    (hfree : Tendsto (fun n : ℕ => Real.sqrt ((card n : ℝ)) *
      q1TailEnvelopeFreePart b Ccov Ctail L M h0 n (δ n) (S n)) atTop (𝓝 0)) :
    ∃ R : ℕ → ℕ, (∀ᶠ n in atTop, 1 ≤ R n) ∧
      Tendsto (fun n : ℕ => ((R n : ℕ) : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (S n) ^ (2 * (2 - 2 * h0) - 2) *
        (card n : ℝ) * (2 * ((R n : ℕ) : ℝ) + 1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (card n : ℝ) *
        (q1ActualLongTailEnvelope b Ccov Ctail L M h0 n (δ n) (S n) (R n) / c) ^ 2)
        atTop (𝓝 0) := by
  have hbal := R_balance_cutoff b Ccov Ctail L M h0 c γ hc card δ S hS
    hcardub hγ1 hγ2 hfree
  exact ⟨q1BalanceCutoff S γ, hbal.1, hbal.2.1, hbal.2.2.1, hbal.2.2.2⟩

/-! ## Item 3 (a): the off-band relative comparison, concrete pair -/

/-- **Off-band relative comparison for the concrete comparison pair.**
The repo's relative bound `|q1A - q1R| <= e * |q1R|`
(`hurstHolder_q1_active_scaled_actual_tail_error_le_envelope` +
`scaled_tail_error_to_relative_riesz`) in the filter form consumed by
`realScaleMeshEnergy_card_sub_tendsto_zero_of_relative`, with
`e n = envelope / c` (`c = f t * (2 * f t - 1) > 0` under `hlong`).
It holds ONLY off the band (`R n < Nat.dist j i`): there is no
relative-on-band extension in the repo. -/
theorem q1_pair_offband_relative
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n) (R : ℕ → ℕ)
    (hR : ∀ᶠ n in atTop, 1 ≤ R n) :
    ∃ Ccov ≥ 0, ∃ Ctail ≥ 0, ∃ L > 0, ∀ᶠ n in atTop,
      ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        R n < Nat.dist j.val i.val →
        |q1ActualLongActiveKernel f hf n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t) i j -
            q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
              (f t * (2 * f t - 1)) i j| ≤
          (q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
              ((n : ℝ) * δ n) (R n) / (f t * (2 * f t - 1))) *
            |q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
              (f t * (2 * f t - 1)) i j| := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, henvPair⟩ :=
    hurstHolder_q1_active_scaled_actual_tail_error_le_envelope
      p a b M hp ha hb hab hM f hf hF t ht
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  have hc : 0 < f t * (2 * f t - 1) := by
    have hft0 : 0 < f t := by linarith
    have hft1 : 0 < 2 * f t - 1 := by linarith
    exact mul_pos hft0 hft1
  have hsmall : ∀ᶠ n in atTop, gridCovarianceError b Ccov n ≤ 1 / 2 :=
    (gridCovarianceError_tendsto b Ccov hb).eventually_le_const (by norm_num)
  have hn2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [hδpos, hR, hn2, hsmall] with n hδ hRn hn hsm
  have hn0 : 0 < n := by omega
  have hSn : 0 < (n : ℝ) * δ n := by positivity
  intro i j hij
  have hcard : 0 < (localWeightActiveSet n 1 (δ n) t).card := by
    have hi := i.isLt
    omega
  have hij' : R n < Nat.dist
      (localWeightActiveIndex n 1 (δ n) t i).val
      (localWeightActiveIndex n 1 (δ n) t j).val := by
    rw [localWeightActiveIndex_physical_dist_eq_rank_dist
      n 1 hn0 (δ n) t hδ hcard i j]
    rwa [Nat.dist_comm]
  have htail := henvPair n hn (δ n) ((n : ℝ) * δ n) hδ rfl (R n) hRn hsm i j hij'
  have hxNat : 0 < Nat.dist
      (localWeightActiveIndex n 1 (δ n) t i).val
      (localWeightActiveIndex n 1 (δ n) t j).val :=
    lt_of_lt_of_le zero_lt_one (le_trans hRn (le_of_lt hij'))
  have hdistne : Nat.dist
      (localWeightActiveIndex n 1 (δ n) t i).val
      (localWeightActiveIndex n 1 (δ n) t j).val ≠ 0 := ne_of_gt hxNat
  have hx : 0 < (Nat.dist
      (localWeightActiveIndex n 1 (δ n) t i).val
      (localWeightActiveIndex n 1 (δ n) t j).val : ℝ) := by
    exact_mod_cast hxNat
  have hF0 : 0 ≤ q1ActualLongTailEnvelope b Ccov Ctail L M (f t)
      n (δ n) ((n : ℝ) * δ n) (R n) := by
    unfold q1ActualLongTailEnvelope
    dsimp only
    have hgrid0 : 0 ≤ gridCovarianceError b Ccov n := by
      unfold gridCovarianceError
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        linarith)
      positivity
    positivity
  have hrel := scaled_tail_error_to_relative_riesz
    ((n : ℝ) * δ n)
    (Nat.dist
      (localWeightActiveIndex n 1 (δ n) t i).val
      (localWeightActiveIndex n 1 (δ n) t j).val)
    (2 - 2 * f t) (f t * (2 * f t - 1))
    (vectorCorrelation
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
        (localWeightActiveIndex n 1 (δ n) t i))
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
        (localWeightActiveIndex n 1 (δ n) t j)))
    (q1ActualLongTailEnvelope b Ccov Ctail L M (f t)
      n (δ n) ((n : ℝ) * δ n) (R n)) hSn hx hc hF0 htail
  simpa only [q1ActualLongActiveKernel, q1RieszActiveKernel, hdistne,
    if_false] using hrel

/-! ## Item 3 (b): the hPert conclusion from the balance + residuals -/

theorem realScaleMeshBandEnergy_nonneg {m : ℕ} (S : ℝ) (R : ℕ)
    (A : Fin m → Fin m → ℝ) : 0 ≤ realScaleMeshBandEnergy S R A := by
  unfold realScaleMeshBandEnergy
  exact mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **The `hPert` conclusion, discharged up to its two documented
residuals.**  From (i) the parameter balance at the explicit cutoff
`R n = floor(S n ^ gamma) + 1` (which produces the weighted envelope rate
`card * (envelope/c)^2 -> 0`), (ii) the off-band relative comparison
`q1_pair_offband_relative`, and (iii) the reference-energy constant
`hCref`, together with the two residuals —

* `hband` : the card-weighted BAND rate of the unweighted comparison pair
  tends to zero (documented obstruction: on the band the comparison
  entries are `Theta(S^psi)`-scale, so `card * bandEnergy =
  Theta(S^{2 psi} R^{1 - 2 psi})`, divergent for `O(1)` row weights — no
  choice of `R` discharges this);
* `hκw` : the quantitative weight-error rate `card * w^2 -> 0` —

this theorem concludes the exact `hPert` Tendsto of
`Hurst.ActualQuadratureConfluence` for the weighted kernel pair. -/
theorem hPert_discharged
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (γ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ + 3 < 4 * f t)
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (hcardub : ∀ᶠ n in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * ((n : ℝ) * δ n))
    (hEfree : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      Real.sqrt ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n)) atTop (𝓝 0))
    (Cref : ℝ) (hCref0 : 0 ≤ Cref)
    (hCref : ∀ (S : ℝ) (m : ℕ), 1 ≤ S → (m : ℝ) ≤ 3 * S →
      realScaleMeshEnergy S
        (rankRieszKernel S (2 - 2 * f t) (f t * (2 * f t - 1)) :
          Fin m → Fin m → ℝ) ≤ Cref)
    (U : ℝ)
    (hu : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U)
    (w : ℕ → ℝ)
    (huv : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i -
        equivalentKernel r (rieszCycleGridPoint
          (localWeightActiveSet n 1 (δ n) t).card i)| ≤ w n)
    (hκw : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * w n ^ 2) atTop (𝓝 0))
    (hband : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      (realScaleMeshBandEnergy ((n : ℝ) * δ n)
          (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
          (q1ActualLongActiveKernel f hf n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)) +
        realScaleMeshBandEnergy ((n : ℝ) * δ n)
          (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
          (q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
            (f t * (2 * f t - 1))))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0) := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hoff⟩ :=
    q1_pair_offband_relative p a b M r hp ha hb hab hM f hf hF t ht hlong δ
      hδpos (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ)
      (Eventually.of_forall fun _ => q1BalanceCutoff_pos _ _ _)
  have hc : 0 < f t * (2 * f t - 1) := by
    have hft0 : 0 < f t := by linarith
    have hft1 : 0 < 2 * f t - 1 := by linarith
    exact mul_pos hft0 hft1
  obtain ⟨_, _, _, hκe⟩ :=
    R_balance_cutoff b Ccov Ctail L M (f t) (f t * (2 * f t - 1)) γ hc
      (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      δ (fun n : ℕ => (n : ℝ) * δ n) hN hcardub hγ1 hγ2
      (hEfree Ccov hCcov Ctail hCtail L hL)
  -- the band split (single residual hband drives both weighted band rates)
  have hκbandA : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshBandEnergy ((n : ℝ) * δ n)
        (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
        (q1ActualLongActiveKernel f hf n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)))
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hband
    · exact mul_nonneg (Nat.cast_nonneg _) (realScaleMeshBandEnergy_nonneg _ _ _)
    · filter_upwards [] with n
      refine mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right
          (realScaleMeshBandEnergy_nonneg ((n : ℝ) * δ n)
            (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
            (q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
              (f t * (2 * f t - 1)))))
        (Nat.cast_nonneg _)
  have hκbandB : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshBandEnergy ((n : ℝ) * δ n)
        (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
        (q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
          (f t * (2 * f t - 1)))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hband
    · exact mul_nonneg (Nat.cast_nonneg _) (realScaleMeshBandEnergy_nonneg _ _ _)
    · filter_upwards [] with n
      refine mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left
          (realScaleMeshBandEnergy_nonneg ((n : ℝ) * δ n)
            (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
            (q1ActualLongActiveKernel f hf n (δ n) t ((n : ℝ) * δ n)
              (2 - 2 * f t))))
        (Nat.cast_nonneg _)
  -- e >= 0 eventually
  have he0 : ∀ᶠ n in atTop, 0 ≤
      (q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n) (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n) /
        (f t * (2 * f t - 1))) := by
    filter_upwards [hδpos, eventually_ge_atTop 2] with n hδ hn
    refine div_nonneg ?_ hc.le
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by
      have hn1 : (1 : ℕ) ≤ n := by omega
      exact_mod_cast hn1
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR1
    have hD : 0 ≤ 2 * L * (1 + M) * δ n := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hL))
        (by linarith)) (le_of_lt hδ)
    have hE : 0 ≤ (2 * L * (1 + M) * δ n) * Real.log (n : ℝ) := mul_nonneg hD hlog
    have hexp : 0 ≤ Real.exp ((2 * L * (1 + M) * δ n) * Real.log (n : ℝ)) :=
      Real.exp_nonneg _
    have hgrid : 0 ≤ gridCovarianceError b Ccov n := by
      unfold gridCovarianceError
      have h2n : (1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
      refine mul_nonneg (mul_nonneg hCcov
        (add_nonneg zero_le_one (Real.log_nonneg h2n)))
        (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    have h2Sn : 0 ≤ 2 * ((n : ℝ) * δ n) := by positivity
    have hfreepos : 0 ≤ q1TailEnvelopeFreePart b Ccov Ctail L M (f t) n (δ n)
        ((n : ℝ) * δ n) := by
      unfold q1TailEnvelopeFreePart
      refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCtail) hD)
          (add_nonneg zero_le_one (mul_nonneg hexp hE))
      · exact mul_nonneg (mul_nonneg (by norm_num) hexp) hE
      · exact mul_nonneg (by norm_num) hD
      · exact mul_nonneg (mul_nonneg (by norm_num)
          (Real.rpow_nonneg h2Sn _)) hgrid
    rw [q1ActualLongTailEnvelope_eq]
    exact add_nonneg hfreepos (by positivity)
  -- the reference bound for B via the rank bridge
  have hBbound : ∀ᶠ n : ℕ in atTop,
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (fun (i j : Fin (localWeightActiveSet n 1 (δ n) t).card) =>
          q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
            (f t * (2 * f t - 1)) i j) ≤ Cref := by
    filter_upwards [hcardub, hN.eventually_ge_atTop 1, hδpos] with n hc hSn hδ
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [Nat.cast_zero, zero_mul] at hSn
        norm_num at hSn
      · exact hn
    have hSn0 : 0 < (n : ℝ) * δ n := lt_of_lt_of_le zero_lt_one hSn
    have hBr := q1RieszActiveKernel_eq_rankRieszKernel n hn0 (δ n) t
      ((n : ℝ) * δ n) (2 - 2 * f t) (f t * (2 * f t - 1)) hδ hSn0 (hm n)
    show realScaleMeshEnergy ((n : ℝ) * δ n)
      (fun (i j : Fin (localWeightActiveSet n 1 (δ n) t).card) =>
        q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
          (f t * (2 * f t - 1)) i j) ≤ Cref
    simp only [hBr]
    exact hCref ((n : ℝ) * δ n) (localWeightActiveSet n 1 (δ n) t).card hSn hc
  -- the off-band + balance gluing: card * energy(A - B) -> 0
  have hκAB := realScaleMeshEnergy_card_sub_tendsto_zero_of_relative
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ)
    (fun n : ℕ => (n : ℝ) * δ n)
    (fun n : ℕ => ((localWeightActiveSet n 1 (δ n) t).card : ℝ))
    (fun n => q1ActualLongActiveKernel f hf n (δ n) t ((n : ℝ) * δ n)
      (2 - 2 * f t))
    (fun n => q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
      (f t * (2 * f t - 1)))
    (fun n => q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
      ((n : ℝ) * δ n) (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n) /
      (f t * (2 * f t - 1)))
    Cref hCref0
    (Eventually.of_forall fun n => Nat.cast_nonneg
      (localWeightActiveSet n 1 (δ n) t).card)
    hoff he0 hBbound hκbandA hκbandB hκe
  -- the weight step to the weighted pair
  refine Tendsto.congr (fun n => ?_)
    (realScaleMeshEnergy_card_left_weight_sub_tendsto_zero
      (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      (fun n : ℕ => (n : ℝ) * δ n)
      (fun n : ℕ => ((localWeightActiveSet n 1 (δ n) t).card : ℝ))
      (fun n => q1ActualLongActiveKernel f hf n (δ n) t ((n : ℝ) * δ n)
        (2 - 2 * f t))
      (fun n => q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
        (f t * (2 * f t - 1)))
      (fun n => actualQ1ChainWeight f r n (δ n) t)
      (fun n i => equivalentKernel r (rieszCycleGridPoint
        (localWeightActiveSet n 1 (δ n) t).card i)) U Cref w hCref0
      (Eventually.of_forall fun n => Nat.cast_nonneg
        (localWeightActiveSet n 1 (δ n) t).card)
      hu huv hκw hκAB hBbound)
  rfl

/-! ## Item 4: the rewired final theorem (hPert no longer a hypothesis) -/

/-- **The final theorem, rewired (the discharge's item 4).**
`actualQ1EigenvaluePowerSums_tendsto_ordinary`
(`Hurst.KernelEnergyRateDischarge`) with its explicit `hPert` hypothesis
REPLACED by the discharged chain: the cutoff is CHOSEN here
(`R n = floor(S n ^ gamma) + 1`, discharging `R`, `hR1`, `hRtop`, `hcut`
via `R_balance_cutoff`), and `hPert` is produced by `hPert_discharged`
from the two documented residuals (`hband` — the card-weighted band rate
of the unweighted comparison pair, obstructed at
`Theta(S^{2 psi} R^{1 - 2 psi})` for `O(1)` row weights — and `hκw`, the
quantitative weight-error rate).  The envelope's ordinary constants stay
ordinary; the `hEfree` free-part rate is inherited unchanged. -/
theorem actualQ1EigenvaluePowerSums_tendsto_discharged
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
    (γ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ + 3 < 4 * f t)
    (U : ℝ)
    (hu : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U)
    (w : ℕ → ℝ)
    (huv : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i -
        equivalentKernel r (rieszCycleGridPoint
          (localWeightActiveSet n 1 (δ n) t).card i)| ≤ w n)
    (hκw : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * w n ^ 2) atTop (𝓝 0))
    (hband : Tendsto (fun n : ℕ =>
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      (realScaleMeshBandEnergy ((n : ℝ) * δ n)
          (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
          (q1ActualLongActiveKernel f hf n (δ n) t ((n : ℝ) * δ n)
            (2 - 2 * f t)) +
        realScaleMeshBandEnergy ((n : ℝ) * δ n)
          (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n)
          (q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) (2 - 2 * f t)
            (f t * (2 * f t - 1))))) atTop (𝓝 0))
    (j : ℕ) :
    Tendsto (fun n : ℕ => padRearranged
      (fun i => |(actualQ1Hermitian f hf r n (δ n) t).eigenvalues i|) j)
      atTop (𝓝 (lam j)) := by
  obtain ⟨hcardpos, hratio⟩ :=
    localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos hδ0 hN
  have hS1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) * δ n :=
    hN.eventually_ge_atTop 1
  have hcardub : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * ((n : ℝ) * δ n) := by
    filter_upwards [hratio.eventually_lt_const
      (show (2 : ℝ) < 5 / 2 by norm_num), hS1] with n h1 h2
    have hSn : 0 < (n : ℝ) * δ n := lt_of_lt_of_le zero_lt_one h2
    have hlt := (div_lt_iff₀ hSn).mp h1
    linarith
  have hCref0 : 0 ≤ Cref := by
    refine le_trans ?_ (hCref 1 3 (by norm_num) (by norm_num))
    unfold realScaleMeshEnergy
    positivity
  have hR1 : ∀ᶠ n in atTop,
      1 ≤ q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ n :=
    Eventually.of_forall fun _ => q1BalanceCutoff_pos _ _ _
  have hRtop := q1BalanceCutoff_tendsto_atTop
    (fun n : ℕ => (n : ℝ) * δ n) γ (by linarith) hN
  have hcut := (R_balance_cutoff b 0 0 1 M (f t) 1 γ (by norm_num)
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    δ (fun n : ℕ => (n : ℝ) * δ n) hN hcardub hγ1 hγ2
    (hEfree 0 (by norm_num) 0 (by norm_num) 1 (by norm_num))).2.2.1
  have hPert := hPert_discharged p a b M r hp ha hb hab hM f hf hF t ht hlong
    δ hδpos hN γ hγ1 hγ2 hm hcardub hEfree Cref hCref0 hCref U hu w huv hκw
    hband
  exact actualQ1EigenvaluePowerSums_tendsto_ordinary p a b M r hp ha hb hab
    hM f hf hF t ht hlong δ hδpos hδ0 hN hm lam hlam hRiesz Bω hBω Cref
    hCref hEfree
    (q1BalanceCutoff (fun n : ℕ => (n : ℝ) * δ n) γ) hR1 hRtop hcut hPert j

end Hurst
