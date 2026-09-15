import Hurst.ActualKernelBandAsymptotics
import Hurst.FarWordAssembly
import Hurst.BandPowerSum

/-!
# The frozen-vs-Riesz word assembly

This file lands the WORD ASSEMBLY comparing `tr(F_n ^ k)` to `tr(T_n ^ k)` for

* `F_n = actualQ1NormalizedFrozenMatrix f hf r n (δ n) t` — the frozen kernel
  under the verified `S^{ψ-1}` normalization (diagonal `S^{ψ-1} * u_i *
  corr(i,i)` — VANISHING under the normalization, so unlike the unnormalized
  pair no diagonal exclusion is needed; the pure-diagonal-cycle statement is
  `actual_q1_diagonal_trace_contribution_tendsto_zero` of
  `Hurst.ActualKernelBandAsymptotics`), and
* `T_n = actualQ1RieszMatrix f r n (δ n) t` — the Riesz quadrature matrix
  (diagonal `0`),

with `S = n * δ`, `ψ = 2 - 2 * f t`, `c = f t * (2 * f t - 1)`,
`Δ_n = F_n - T_n`.  The route is UNCONDITIONAL on compactness: the only
concentration input enters through the band-predicate cutoff hypothesis
`hcut` (the EXACT hypothesis of
`actual_q1_kernel_band_predicate_tendsto_zero`, instantiated for the
frozen-vs-Riesz difference) and the explicit residual `eps` sequence.

## What is landed here

1. **(D1, per-entry)** `frozenWord_deltaEntry_uniform_le`: the UNIFORM
   all-pairs entry bound `|Δ_n i j| ≤ S^{ψ-1} * (U + B_omega * |c|)` —
   the frozen side uses `|corr| ≤ 1` (the cross-lag correlation is an inner
   product of unit-norm frozen increments) and the Riesz side uses
   `|rankRieszUnitKernel| ≤ 1`; this covers the band AND the diagonal (the
   normalized diagonal difference is `O(S^{ψ-1}) → 0`).
2. **(D1, per-entry, far band)** `frozenWord_deltaEntry_far_le`: on
   `d = dist ≥ 2` the RELATIVE assembly
   `|Δ_n i j| ≤ S^{ψ-1} * ((B_box + B_omega) * eps_pair + 16 * B_omega * d^{-(1+ψ)})`
   — the landed per-entry envelope `frozenQuadFarBandEntry_le` (B2),
   post-processed into the two-constant relative form with the exact
   `16 * d^{-(1+ψ)}` beat (`d^{-(1+ψ)} = d^{-ψ} * d^{-1}`).
3. **(D1, energy)** `frozenWord_frobenius_sq_le_of_cutoff_envelope`: the
   abstract stratified energy bound — if `|Δ i j| ≤ b` on `dist ≤ R`, and
   `|Δ i j| ≤ e + a * d^{-(1+ψ)}` on `dist > R`, then
   `‖Δ‖² ≤ 2 * (R+1) * m * b² + 2 * m² * e² + 4 * m * a² * R^{-(1+2ψ)}`
   (row-distance stratification `sum_row_dist_le` + the tail power sum
   `∑_{d > R} d^{-(2+2ψ)} ≤ R^{-(1+2ψ)}`, obtained from
   `Real.sum_Ioc_inv_sq_le_sub` by `d^{-(2+2ψ)} ≤ R^{-2ψ} * d^{-2}`).
   Instantiated with the `S^{ψ-1}` normalization this gives the EXPLICIT
   S-decay exponents: the `b`- and `a`-terms are `O(S^{2ψ-1})` (vanishing for
   `2ψ < 1`, i.e. `3/4 < f t`), and the `eps`-term is
   `2 * m² * S^{2ψ-2} * eps² = O(S^{2ψ} * eps²)`.
4. **(D2)** `frozenWord_trace_diff_tendsto`: the word-level trace-difference
   theorem — under (i) the cutoff `S^{2ψ-2} * m * (2R+1) → 0` (the band
   predicate, landed shape), (ii) the far-band envelope with residual
   `eps = o(S^{-ψ})`, and (iii) eventual uniform Frobenius bounds on `F_n`,
   `T_n`, the sharp telescope bound `abs_trace_pow_sub_le_frob` (REUSED from
   `Hurst.FarWordAssembly`, not reproved) gives
   `|tr(F_n ^ k) - tr(T_n ^ k)| → 0`, i.e. the `hFarWord` input of
   `Hurst.frozenQuad_hFquad_of_farWord`.

## Honest gap note (the exact residual statement)

The full n-dependent assembly IS landed here: `frozenWord_frobenius_sq_tendsto_zero`
elaborates the three-beat stratified decay of
`frozenWord_frobenius_sq_le_explicit` (near-band beat → 0 via the cutoff
`hcut`; residual beat via `m ≤ 3 * S` from `localWeightActiveSet_card` and
`heps : S^{2ψ} * eps² → 0`; far-tail beat `S^{2ψ-1} → 0` for `2ψ < 1`, `R ≥ 1`,
NO growth condition on `R`), and `frozenWord_trace_diff_of_cutoff` composes it
with `farWord_of_frobeniusSmall` into the trace-difference smallness
`|tr(F_n ^ k) - tr(T_n ^ k)| → 0` — closing the `hFarWord` input of
`Hurst.frozenQuad_hFquad_of_farWord`.

The residual ANALYTIC input is the far-band CLASS precision `eps` in the
relative envelope: the per-fixed-distance class convergence
(`frozenQ1_kernel_class_converges`) and the row-profile bridge
(`frozenQuadRowProfile_tendsto`) give `eps_pair → 0` at each FIXED distance,
but a UNIFORM-in-`d` version (or the word-level relative machinery) is needed
to make the sequence `eps n` decay like `o(S^{-ψ})` — with `card * (S^{ψ-1})²
~ S^{2ψ}`, a fixed `eps > 0` does NOT vanish.  Accordingly `heps` (plus the
nonnegativity `hε0`) is carried as an explicit hypothesis of the assembly,
while the cutoff hypothesis `hcut` closes the `R`-band part (uniformly bounded
entries, `S^{2ψ-2} * m * (2R+1) → 0`) and the `16 * d^{-(1+ψ)}` beat closes
the far tail unconditionally (`S^{2ψ-1} * R^{-(1+2ψ)} → 0` for `2ψ < 1`,
`R ≥ 1` — no growth condition on `R` beyond `≥ 1` is needed).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ### Private helpers -/

/-- Square split: from `|x| ≤ e + a` to `x ^ 2 ≤ 2 * e ^ 2 + 2 * a ^ 2`. -/
private theorem sq_le_two_add_sq {x e a : ℝ} (h : |x| ≤ e + a) :
    x ^ 2 ≤ 2 * e ^ 2 + 2 * a ^ 2 := by
  rcases abs_le.mp h with ⟨h1, h2⟩
  have hpos : (0 : ℝ) ≤ e + a + x := by linarith
  have hpos2 : (0 : ℝ) ≤ e + a - x := by linarith
  have hsq : x ^ 2 ≤ (e + a) ^ 2 := by nlinarith [hpos, hpos2]
  have he2 : (0 : ℝ) ≤ e ^ 2 := sq_nonneg e
  have ha2 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  have h1 : (0 : ℝ) ≤ (e - a) ^ 2 := sq_nonneg (e - a)
  have h2 : (e - a) ^ 2 = e ^ 2 + a ^ 2 - 2 * (e * a) := by ring
  rw [h2] at h1
  calc x ^ 2 ≤ (e + a) ^ 2 := hsq
    _ = e ^ 2 + a ^ 2 + 2 * (e * a) := by ring
    _ ≤ 2 * e ^ 2 + 2 * a ^ 2 := by linarith [h1, he2, ha2]

/-- `|a - b| ≤ |a| + |b|`. -/
private theorem abs_sub_abs_le {a b : ℝ} : |a - b| ≤ |a| + |b| := by
  have h : |a + -b| ≤ |a| + |-b| := abs_add_le a (-b)
  have h2 : a + -b = a - b := by ring
  rw [h2, abs_neg] at h
  exact h

/-- Norm one from squared norm one. -/
private theorem norm_eq_one_of_norm_sq {V : Type*} [NormedAddCommGroup V] (v : V)
    (h : ‖v‖ ^ 2 = 1) : ‖v‖ = 1 := by
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  rw [show ‖v‖ = Real.sqrt (‖v‖ ^ 2) from (Real.sqrt_sq hv).symm, h, Real.sqrt_one]

/-- The fixed-lag cross-lag correlation is an inner product of unit-norm frozen
increments, hence absolutely at most `1` — UNIFORMLY in the lag. -/
private theorem firstIncrementCrossLagCorrelation_abs_le_one {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) (d : ℝ) :
    |firstIncrementCrossLagCorrelation x y d| ≤ 1 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have h := normalizedFrozenIncrement_cross_parameter_lag
    (⟨x, hx1, hx2⟩ : Ioo (0 : ℝ) 1) (⟨y, hy1, hy2⟩ : Ioo (0 : ℝ) 1) 0 1 d (by norm_num)
  rw [show ((0 : ℝ) + d * 1) = d from by ring] at h
  have hcs := abs_real_inner_le_norm (normalizedFrozenIncrement
      (⟨x, hx1, hx2⟩ : Ioo (0 : ℝ) 1) 0 1)
    (normalizedFrozenIncrement (⟨y, hy1, hy2⟩ : Ioo (0 : ℝ) 1) d 1)
  have n1 : ‖normalizedFrozenIncrement (⟨x, hx1, hx2⟩ : Ioo (0 : ℝ) 1) 0 1‖ = 1 :=
    normalizedFrozenIncrement_norm _ 0 1 (by norm_num)
  have n2 : ‖normalizedFrozenIncrement (⟨y, hy1, hy2⟩ : Ioo (0 : ℝ) 1) d 1‖ = 1 :=
    normalizedFrozenIncrement_norm _ d 1 (by norm_num)
  rw [n1, n2, mul_one] at hcs
  have h2 : |firstIncrementCrossLagCorrelation x y d|
      = |⟪normalizedFrozenIncrement (⟨x, hx1, hx2⟩ : Ioo (0 : ℝ) 1) 0 1,
          normalizedFrozenIncrement (⟨y, hy1, hy2⟩ : Ioo (0 : ℝ) 1) d 1⟫| := by
    rw [h]
  rw [h2]
  exact hcs

/-- **Far tail power sum.**  For `R ≥ 1`, `ψ > 0`:
`∑_{d ∈ range m, R < d} d^{-(2+2ψ)} ≤ R^{-(1+2ψ)}` — from the termwise split
`d^{-(2+2ψ)} ≤ R^{-2ψ} * d^{-2}` (valid at `d ≥ R`) and
`Real.sum_Ioc_inv_sq_le_sub`. -/
private theorem sum_range_tail_rpow_le (R m : ℕ) (hR : 1 ≤ R) (psi : ℝ) (hpsi : 0 < psi) :
    (∑ d ∈ Finset.range m, (if R < d then ((d : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)))
      ≤ ((R : ℝ) ^ (-(1 + 2 * psi))) := by
  classical
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  by_cases hmR : R ≤ m
  · have hsum : (∑ d ∈ Finset.range m,
        (if R < d then ((d : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)))
        = (∑ d ∈ (Finset.range m).filter (fun d : ℕ => R < d),
            ((d : ℝ) ^ (-(2 + 2 * psi)))) := by
      rw [Finset.sum_filter]
    rw [hsum]
    have hsub : ((Finset.range m).filter (fun d : ℕ => R < d)) ⊆ Finset.Ioc R m := by
      intro d hd
      have hd2 := Finset.mem_filter.mp hd
      exact Finset.mem_Ioc.mpr ⟨hd2.2,
        Nat.le_of_lt (Finset.mem_range.mp hd2.1)⟩
    have hterm : ∀ d : ℕ, R < d →
        ((d : ℝ) ^ (-(2 + 2 * psi))) ≤ ((R : ℝ) ^ (-(2 * psi))) * (((d : ℝ) ^ 2)⁻¹) := by
      intro d hdR
      have hdn : (0 : ℕ) < d := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hdR)
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdn
      have hsplit2 : ((d : ℝ) ^ (-(2 + 2 * psi)))
          = ((d : ℝ) ^ (-(2 * psi))) * (((d : ℝ) ^ 2)⁻¹) := by
        have h1 : ((d : ℝ) ^ (-(2 + 2 * psi)))
            = ((d : ℝ) ^ (-(2 * psi))) * (d ^ (-(2 : ℝ))) := by
          rw [← Real.rpow_add hdpos (-(2 * psi : ℝ)) (-(2 : ℝ))]
          congr 1
          ring
        rw [h1, Real.rpow_neg hdpos.le 2]
        simp
      have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      rw [hsplit2, Real.rpow_neg hdpos.le (2 * psi), Real.rpow_neg hRnn (2 * psi)]
      have hmono : ((R : ℝ) ^ (2 * psi)) ≤ ((d : ℝ) ^ (2 * psi)) := by
        refine Real.rpow_le_rpow (by exact_mod_cast Nat.zero_le R)
          (by exact_mod_cast Nat.le_of_lt hdR) (by linarith)
      have hinv : ((d : ℝ) ^ (2 * psi))⁻¹ ≤ ((R : ℝ) ^ (2 * psi))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) (2 * psi))
          (Real.rpow_pos_of_pos (by positivity) (2 * psi))).mpr hmono
      exact mul_le_mul_of_nonneg_right hinv (inv_nonneg.2 (sq_nonneg (d : ℝ)))
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)) ?_
    have hkey : (∑ d ∈ Finset.Ioc R m, ((d : ℝ) ^ (-(2 + 2 * psi))))
        ≤ ((R : ℝ) ^ (-(2 * psi))) * (((R : ℝ)⁻¹ - ((m : ℝ)⁻¹))) := by
      calc (∑ d ∈ Finset.Ioc R m, ((d : ℝ) ^ (-(2 + 2 * psi))))
          ≤ ∑ d ∈ Finset.Ioc R m, ((R : ℝ) ^ (-(2 * psi))) * (((d : ℝ) ^ 2)⁻¹) :=
            Finset.sum_le_sum fun d hd => hterm d (Finset.mem_Ioc.mp hd).1
        _ = ((R : ℝ) ^ (-(2 * psi))) * (∑ d ∈ Finset.Ioc R m, (((d : ℝ) ^ 2)⁻¹)) := by
            rw [← Finset.mul_sum]
        _ ≤ ((R : ℝ) ^ (-(2 * psi))) * (((R : ℝ)⁻¹ - ((m : ℝ)⁻¹))) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hRpos.le _)
            exact sum_Ioc_inv_sq_le_sub (α := ℝ) (k := R) (n := m)
              (by omega) hmR
    refine le_trans hkey ?_
    have hm1 : (0 : ℝ) ≤ ((m : ℝ)⁻¹) := inv_nonneg.2 (Nat.cast_nonneg m)
    have hR1 : ((R : ℝ) ^ (-(1 : ℝ))) = ((R : ℝ)⁻¹) := by
      rw [Real.rpow_neg hRpos.le, Real.rpow_one]
    calc ((R : ℝ) ^ (-(2 * psi))) * (((R : ℝ)⁻¹ - ((m : ℝ)⁻¹)))
        ≤ ((R : ℝ) ^ (-(2 * psi))) * ((R : ℝ)⁻¹) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hRpos.le _)
      _ = ((R : ℝ) ^ (-(2 * psi))) * ((R : ℝ) ^ (-(1 : ℝ))) := by rw [hR1]
      _ = ((R : ℝ) ^ (-(1 + 2 * psi))) := by
          rw [← Real.rpow_add hRpos (-(2 * psi : ℝ)) (-(1 : ℝ))]
          congr 1
          ring
  · -- `m < R`: the far part is empty
    have hzero : ∀ d ∈ Finset.range m,
        (if R < d then ((d : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)) = 0 := by
      intro d hd
      have hnd : ¬(R < d) := by have := Finset.mem_range.mp hd; omega
      rw [if_neg hnd]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact Real.rpow_nonneg hRpos.le _

/-- Per-row near-band entry count: at most `2 * (R + 1)` entries of a row lie
within rank distance `R`. -/
private theorem sum_row_near_ind_le {m : ℕ} (R : ℕ) (i : Fin m) :
    (∑ j : Fin m, (if Nat.dist i.val j.val ≤ R then (1 : ℝ) else 0))
      ≤ (2 : ℝ) * ((R + 1 : ℕ) : ℝ) := by
  classical
  have h0 : ∀ d : ℕ, 0 ≤ (if d ≤ R then (1 : ℝ) else 0) := by
    intro d; by_cases h : d ≤ R
    · simp only [if_pos h]; exact zero_le_one
    · simp only [if_neg h]; exact le_refl 0
  have h := sum_row_dist_le (fun d : ℕ => if d ≤ R then (1 : ℝ) else 0) h0 i
  refine le_trans h ?_
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range m)
    (fun d : ℕ => d ≤ R) (fun d : ℕ => (if d ≤ R then (1 : ℝ) else 0))
  have hcard : ((Finset.range m).filter (fun d : ℕ => d ≤ R)).card
      ≤ (Finset.range (R + 1)).card := by
    refine Finset.card_le_card fun d hd => ?_
    have hd2 := Finset.mem_filter.mp hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hd2.2)
  have h1 : (∑ d ∈ (Finset.range m).filter (fun d : ℕ => d ≤ R),
      (if d ≤ R then (1 : ℝ) else 0))
      = ((Finset.range m).filter (fun d : ℕ => d ≤ R)).card := by
    rw [Finset.sum_congr rfl
        (fun d hd => if_pos (Finset.mem_filter.mp hd).2),
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : (∑ d ∈ (Finset.range m).filter (fun d : ℕ => ¬(d ≤ R)),
      (if d ≤ R then (1 : ℝ) else 0)) ≤ 0 :=
    Finset.sum_nonpos fun d hd => (if_neg (Finset.mem_filter.mp hd).2).le
  have hsum : (∑ d ∈ Finset.range m, (if d ≤ R then (1 : ℝ) else 0))
      ≤ ((R + 1 : ℕ) : ℝ) := by
    rw [← hsplit, h1]
    have hc : (((Finset.range m).filter (fun d : ℕ => d ≤ R)).card : ℝ)
        ≤ ((R + 1 : ℕ) : ℝ) := by
      have h3 : ((Finset.range m).filter (fun d : ℕ => d ≤ R)).card
          ≤ (R + 1 : ℕ) := by
        have h4 := hcard
        rwa [Finset.card_range] at h4
      exact_mod_cast h3
    linarith
  calc (2 : ℝ) * (∑ d ∈ Finset.range m, (if d ≤ R then (1 : ℝ) else 0))
      ≤ (2 : ℝ) * ((R + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- Per-row far-band tail weight: at most `2 * R^{-(1+2ψ)}`. -/
private theorem sum_row_far_weight_le {m : ℕ} (R : ℕ) (hR : 1 ≤ R) (psi : ℝ)
    (hpsi : 0 < psi) (i : Fin m) :
    (∑ j : Fin m, (if R < Nat.dist i.val j.val then
        ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)))
      ≤ (2 : ℝ) * ((R : ℝ) ^ (-(1 + 2 * psi))) := by
  classical
  have h0 : ∀ d : ℕ, 0 ≤ (if R < d then ((d : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)) := by
    intro d; by_cases h : R < d
    · simp only [if_pos h]; exact Real.rpow_nonneg (Nat.cast_nonneg d) _
    · simp only [if_neg h]; exact le_refl 0
  have h := sum_row_dist_le
    (fun d : ℕ => if R < d then ((d : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)) h0 i
  refine le_trans h ?_
  refine mul_le_mul_of_nonneg_left (sum_range_tail_rpow_le R m hR psi hpsi) (by norm_num)

/-! ### (D1, energy) the abstract stratified cutoff-envelope bound -/

/-- **The stratified cutoff-envelope Frobenius bound (deliverable 1, abstract
form).**  If every entry of `Δ` is bounded by `b` within rank distance `R` and
by the two-constant relative law `e + a * d^{-(1+ψ)}` beyond `R`, then

`‖Δ‖² ≤ 2 * (R+1) * m * b² + 2 * m² * e² + 4 * m * a² * R^{-(1+2ψ)}`.

The `a`-beat decays like `R^{-(1+2ψ)}` (sharp: `d^{-(2+2ψ)} ≤ R^{-2ψ} * d^{-2}`),
which is what makes the far tail close at any `R ≥ 1` once `S^{2ψ-1} → 0`. -/
theorem frozenWord_frobenius_sq_le_of_cutoff_envelope {m : ℕ}
    (Δ : Matrix (Fin m) (Fin m) ℝ) (psi e a b : ℝ) (R : ℕ)
    (hpsi : 0 < psi) (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 1 ≤ R)
    (hnear : ∀ i j : Fin m, Nat.dist i.val j.val ≤ R → |Δ i j| ≤ b)
    (hfar : ∀ i j : Fin m, R < Nat.dist i.val j.val →
      |Δ i j| ≤ e + a * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi)))) :
    ‖Δ‖ ^ 2 ≤ ((2 : ℝ) * ((R + 1 : ℕ) : ℝ) * (m : ℝ)) * b ^ 2
      + ((2 : ℝ) * (m : ℝ) ^ 2) * e ^ 2
      + ((4 : ℝ) * (m : ℝ)) * a ^ 2 * ((R : ℝ) ^ (-(1 + 2 * psi))) := by
  classical
  have hnormsq : ‖Δ‖ ^ 2 = ∑ i : Fin m, ∑ j : Fin m, |Δ i j| ^ 2 := by
    have h1 : ‖Δ‖ = (∑ i : Fin m, ∑ j : Fin m, |Δ i j| ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [Matrix.frobenius_norm_def]
      refine congrArg (fun x : ℝ => x ^ ((1 : ℝ) / 2)) ?_
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [h1, ← Real.sqrt_eq_rpow, pow_two]
    exact Real.mul_self_sqrt (by positivity)
  -- per-entry split into the near indicator and the far two-constant law
  have hentry : ∀ i j : Fin m, |Δ i j| ^ 2 ≤
      b ^ 2 * (if Nat.dist i.val j.val ≤ R then (1 : ℝ) else 0)
        + (2 * e ^ 2 + 2 * a ^ 2 * (if R < Nat.dist i.val j.val then
              ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ))) := by
    intro i j
    by_cases hd : Nat.dist i.val j.val ≤ R
    · have h1 : |Δ i j| ^ 2 ≤ b ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hnear i j hd) 2
      rw [if_pos hd, if_neg (by omega : ¬(R < Nat.dist i.val j.val))]
      have hpos : (0 : ℝ) ≤ 2 * e ^ 2 := by positivity
      linarith
    · have hd2 : R < Nat.dist i.val j.val := by omega
      have hx := hfar i j hd2
      have hsplit := sq_le_two_add_sq hx
      have hmul : (a * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi)))) ^ 2
          = a ^ 2 * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi))) ^ 2 := by
        rw [mul_pow]
      rw [hmul] at hsplit
      have hdpos : (0 : ℝ) ≤ (Nat.dist i.val j.val : ℝ) := Nat.cast_nonneg _
      have hpow : ((Nat.dist i.val j.val : ℝ) ^ (-(1 + psi))) ^ 2
          = ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos]
        congr 1
        ring
      rw [hpow] at hsplit
      have hsqabs : |Δ i j| ^ 2 = Δ i j ^ 2 := sq_abs _
      rw [hsqabs]
      rw [if_neg hd, if_pos hd2]
      linarith [hsplit]
  -- per-row stratified bound
  have hrow : ∀ i : Fin m, (∑ j : Fin m, |Δ i j| ^ 2)
      ≤ b ^ 2 * ((2 : ℝ) * ((R + 1 : ℕ) : ℝ)) + (2 * e ^ 2) * (m : ℝ)
        + (2 * a ^ 2) * ((2 : ℝ) * ((R : ℝ) ^ (-(1 + 2 * psi)))) := by
    intro i
    have e1 : (∑ j : Fin m, (b ^ 2 *
          (if Nat.dist i.val j.val ≤ R then (1 : ℝ) else 0)))
        = b ^ 2 * (∑ j : Fin m,
            (if Nat.dist i.val j.val ≤ R then (1 : ℝ) else 0)) := by
      rw [← Finset.mul_sum]
    have e2 : (∑ j : Fin m, (2 * e ^ 2 : ℝ)) = (2 * e ^ 2) * (m : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring
    have e3 : (∑ j : Fin m, (2 * a ^ 2 *
          (if R < Nat.dist i.val j.val then
            ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ))))
        = (2 * a ^ 2) * (∑ j : Fin m,
            (if R < Nat.dist i.val j.val then
              ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ))) := by
      rw [← Finset.mul_sum]
    calc (∑ j : Fin m, |Δ i j| ^ 2)
        ≤ ∑ j : Fin m, (b ^ 2 * (if Nat.dist i.val j.val ≤ R then (1 : ℝ) else 0)
            + (2 * e ^ 2 + 2 * a ^ 2 * (if R < Nat.dist i.val j.val then
                ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)))) :=
          Finset.sum_le_sum fun j _ => hentry i j
      _ = (∑ j : Fin m, (b ^ 2 * (if Nat.dist i.val j.val ≤ R then (1 : ℝ) else 0)))
            + (∑ j : Fin m, (2 * e ^ 2 : ℝ)) + (∑ j : Fin m, (2 * a ^ 2 *
              (if R < Nat.dist i.val j.val then
                ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ)))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          ring
      _ = b ^ 2 * (∑ j : Fin m, (if Nat.dist i.val j.val ≤ R then (1 : ℝ) else 0))
            + (2 * e ^ 2) * (m : ℝ) + (2 * a ^ 2) * (∑ j : Fin m,
              (if R < Nat.dist i.val j.val then
                ((Nat.dist i.val j.val : ℝ) ^ (-(2 + 2 * psi))) else (0 : ℝ))) := by
          rw [e1, e2, e3]
      _ ≤ b ^ 2 * ((2 : ℝ) * ((R + 1 : ℕ) : ℝ)) + (2 * e ^ 2) * (m : ℝ)
            + (2 * a ^ 2) * ((2 : ℝ) * ((R : ℝ) ^ (-(1 + 2 * psi)))) := by
          have h1 := sum_row_near_ind_le R i
          have h2 := sum_row_far_weight_le R hR psi hpsi i
          have hb2 : (0 : ℝ) ≤ b ^ 2 := pow_nonneg hb 2
          have ha2 : (0 : ℝ) ≤ a ^ 2 := pow_nonneg ha 2
          have he2 : (0 : ℝ) ≤ e ^ 2 := pow_nonneg he 2
          nlinarith
  calc ‖Δ‖ ^ 2 = ∑ i : Fin m, ∑ j : Fin m, |Δ i j| ^ 2 := hnormsq
    _ ≤ ∑ i : Fin m, (b ^ 2 * ((2 : ℝ) * ((R + 1 : ℕ) : ℝ))
          + (2 * e ^ 2) * (m : ℝ)
          + (2 * a ^ 2) * ((2 : ℝ) * ((R : ℝ) ^ (-(1 + 2 * psi))))) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = ((2 : ℝ) * ((R + 1 : ℕ) : ℝ) * (m : ℝ)) * b ^ 2
          + ((2 : ℝ) * (m : ℝ) ^ 2) * e ^ 2
          + ((4 : ℝ) * (m : ℝ)) * a ^ 2 * ((R : ℝ) ^ (-(1 + 2 * psi))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        ring

/-! ### (D1, per-entry) the uniform band bound and the far-band relative assembly -/

/-- **(D1) The uniform frozen-vs-Riesz entry bound (all pairs, diagonal
included).**  Every entry of `Δ_n = F_n - T_n` is at most
`S^{ψ-1} * (U + B_omega * |c|)`: the frozen side uses the `|corr| ≤ 1`
Cauchy-Schwarz bound (`firstIncrementCrossLagCorrelation_abs_le_one`), the
Riesz side the `|rankRieszUnitKernel| ≤ 1` bound.  In particular the
normalized DIAGONAL difference is `O(S^{ψ-1}) → 0` — the structural
frozen-diagonal `S^ψ * 1` vs Riesz-diagonal `0` asymmetry vanishes under the
`S^{ψ-1}` normalization (the pure-diagonal-cycle trace statement is
`actual_q1_diagonal_trace_contribution_tendsto_zero`), so the word assembly
needs no diagonal exclusion. -/
theorem frozenWord_deltaEntry_uniform_le
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (r n : ℕ) (hn : 0 < n) (δ t' : ℝ) (hδ : 0 < δ)
    (U : ℝ) (hu : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      |actualQ1ChainWeight f r n δ t i| ≤ U)
    (B_omega : ℝ) (homega : ∀ z ∈ Icc (-1 : ℝ) 1, |equivalentKernel r z| ≤ B_omega)
    (hcard : 0 < (localWeightActiveSet n 1 δ t).card)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
        actualQ1RieszMatrix f r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
        * (U + B_omega * |f t * (2 * f t - 1)|) := by
  classical
  have hftbox : f t ∈ Icc a b := hF ht
  have hpsi0 : 0 ≤ 2 - 2 * f t := by linarith [hftbox.2]
  have hS0 : 0 < (n : ℝ) * δ := by positivity
  -- the frozen side: |F| ≤ S^{ψ-1} * U
  have hval : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t k)) : ℝ) ∈ Icc a b := by
    intro k
    have hp : grid n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 δ t k)).val ∈ Ioo (0 : ℝ) 1 :=
      grid_mem n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 δ t k)).val
        (Nat.zero_lt_of_lt (strideFirstLeft n 1
          (localWeightActiveIndex n 1 δ t k)).isLt)
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t k)).isLt
    exact hF hp
  have hxib : (midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ) ∈ Icc a b := hval i
  have hyjb : (midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ) ∈ Icc a b := hval j
  have hxi : (midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [ha, hxib.1], by linarith [hb, hxib.2]⟩
  have hyj : (midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [ha, hyjb.1], by linarith [hb, hyjb.2]⟩
  have hcorr : |firstIncrementCrossLagCorrelation
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)))
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)))
      (Nat.dist (localWeightActiveIndex n 1 δ t i).val
        (localWeightActiveIndex n 1 δ t j).val : ℝ)| ≤ 1 :=
    firstIncrementCrossLagCorrelation_abs_le_one hxi hyj _
  have hFk := frozenQ1_kernel_eq_crossLagCorrelation f hf n hn δ t ((n : ℝ) * δ) i j
  have hscale : ((n : ℝ) * δ)⁻¹ * ((n : ℝ) * δ) ^ (2 - 2 * f t)
      = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) := by
    rw [Real.rpow_sub hS0 (2 - 2 * f t) 1, Real.rpow_one]
    ring
  have hFabsh : |actualQ1NormalizedFrozenMatrix f hf r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U := by
    have hdef : actualQ1NormalizedFrozenMatrix f hf r n δ t i j
        = ((n : ℝ) * δ)⁻¹ *
          (actualQ1ChainWeight f r n δ t i *
            actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j) := rfl
    have h1 : |actualQ1NormalizedFrozenMatrix f hf r n δ t i j|
        = ((n : ℝ) * δ)⁻¹ * (|actualQ1ChainWeight f r n δ t i| *
            |actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j|) := by
      rw [hdef, abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hS0.le)]
    rw [h1, hFk, abs_mul]
    have hrearr : ∀ (v w z : ℝ), ((n : ℝ) * δ)⁻¹ * (v * (w * z))
        = (((n : ℝ) * δ)⁻¹ * w) * v * z := by
      intro v w z
      ring
    rw [hrearr, mul_assoc,
      abs_of_nonneg (Real.rpow_nonneg hS0.le (2 - 2 * f t)), hscale]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hS0.le (2 - 2 * f t - 1))
    have h2 : |actualQ1ChainWeight f r n δ t i| *
        |firstIncrementCrossLagCorrelation
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)))
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)))
          ((Nat.dist (localWeightActiveIndex n 1 δ t i).val
            (localWeightActiveIndex n 1 δ t j).val : ℝ))| ≤
        |actualQ1ChainWeight f r n δ t i| * 1 :=
      mul_le_mul_of_nonneg_left hcorr (abs_nonneg _)
    rw [mul_one] at h2
    linarith [h2, hu i]
  -- the Riesz side: |T| ≤ S^{ψ-1} * B_omega * |c|
  have hTabsh : |actualQ1RieszMatrix f r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * (B_omega * |f t * (2 * f t - 1)|) := by
    have hentry : actualQ1RieszMatrix f r n δ t i j
        = ((n : ℝ) * δ)⁻¹ *
          equivalentKernel r (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i) *
          rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t) (f t * (2 * f t - 1)) i j := by
      simp only [actualQ1RieszMatrix, weightedRieszDiscreteMatrix_apply]
    have hω : |equivalentKernel r
        (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)| ≤ B_omega :=
      homega _ (rieszCycleGridPoint_mem_Icc hcard i)
    have hrk2 : |rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
        (f t * (2 * f t - 1)) i j| ≤ |f t * (2 * f t - 1)| *
          ((n : ℝ) * δ) ^ (2 - 2 * f t) := by
      have hrkdef : rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
          (f t * (2 * f t - 1)) i j
          = (f t * (2 * f t - 1)) * ((n : ℝ) * δ) ^ (2 - 2 * f t) *
            rankRieszUnitKernel (2 - 2 * f t) i j := rfl
      rw [hrkdef, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hS0.le (2 - 2 * f t))]
      refine le_trans (mul_le_mul_of_nonneg_left
        (rankRieszUnitKernel_abs_le_one (2 - 2 * f t) hpsi0 i j)
        (mul_nonneg (abs_nonneg (f t * (2 * f t - 1)))
          (Real.rpow_nonneg hS0.le (2 - 2 * f t)))) ?_
      rw [mul_one]
    have h1t : |actualQ1RieszMatrix f r n δ t i j|
        = ((n : ℝ) * δ)⁻¹ * (|equivalentKernel r
            (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)| *
            |rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
              (f t * (2 * f t - 1)) i j|) := by
      rw [hentry, abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hS0.le)]
      ring
    rw [h1t]
    have hB : |equivalentKernel r
        (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)| *
        |rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
          (f t * (2 * f t - 1)) i j| ≤
        B_omega * (|f t * (2 * f t - 1)| * ((n : ℝ) * δ) ^ (2 - 2 * f t)) := by
      refine le_trans (mul_le_mul_of_nonneg_left hrk2 (abs_nonneg _)) ?_
      exact mul_le_mul_of_nonneg_right hω
        (mul_nonneg (abs_nonneg (f t * (2 * f t - 1)))
          (Real.rpow_nonneg hS0.le (2 - 2 * f t)))
    have hreg : ((n : ℝ) * δ)⁻¹ *
        (B_omega * (|f t * (2 * f t - 1)| * ((n : ℝ) * δ) ^ (2 - 2 * f t)))
        = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * (B_omega * |f t * (2 * f t - 1)|) := by
      rw [← hscale]
      ring
    exact le_trans (mul_le_mul_of_nonneg_left hB (inv_nonneg.2 hS0.le)) (le_of_eq hreg)
  calc |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
        actualQ1RieszMatrix f r n δ t i j| ≤
        |actualQ1NormalizedFrozenMatrix f hf r n δ t i j| +
          |actualQ1RieszMatrix f r n δ t i j| :=
      abs_sub_abs_le (a := actualQ1NormalizedFrozenMatrix f hf r n δ t i j)
        (b := actualQ1RieszMatrix f r n δ t i j)
    _ ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) *
          (U + B_omega * |f t * (2 * f t - 1)|) := by
        have h1 := hFabsh
        have h2 := hTabsh
        have hkey : ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) *
            (U + B_omega * |f t * (2 * f t - 1)|)
            = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U
            + ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * (B_omega * |f t * (2 * f t - 1)|) := by
          rw [mul_add]
        rw [hkey]
        linarith [h1, h2]

/-- **(D1) The far-band relative entry assembly.**  On `d = dist(i, j) ≥ 2`
the frozen-vs-Riesz entry difference obeys the two-constant relative law

`|Δ_n i j| ≤ S^{ψ-1} * ((B_box + B_omega) * eps + 16 * B_omega * d^{-(1+ψ)})`,

where `eps` is the simultaneous precision of the row-profile bridge and of the
per-class convergence, `B_box` the per-lag box bound, and the `16 * d^{-(1+ψ)}`
beat is the landed (B1) envelope `frozenQuadClassSixteen_le` post-processed
from the (B2) shape `d^{-ψ} * d^{-1} = d^{-(1+ψ)}`. -/
theorem frozenWord_deltaEntry_far_le
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r n : ℕ) (hn : 0 < n) (δ t : ℝ) (hS : 0 < (n : ℝ) * δ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card)
    (d : ℕ) (hdij : Nat.dist (localWeightActiveIndex n 1 δ t i).val
        (localWeightActiveIndex n 1 δ t j).val = d)
    (hdrank : Nat.dist i.val j.val = d)
    (hd2 : 2 ≤ d)
    (x y : ℝ)
    (hx : (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ) = x)
    (hy : (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ) = y)
    (eps B_box B_omega : ℝ)
    (hprof : |actualQ1ChainWeight f r n δ t i -
        equivalentKernel r (rieszCycleGridPoint
          (localWeightActiveSet n 1 δ t).card i)| ≤ eps)
    (hcorrB : |firstIncrementCrossLagCorrelation x y (d : ℝ)| ≤ B_box)
    (hclass : |firstIncrementCrossLagCorrelation x y (d : ℝ)
        - firstIncrementLagCorrelation (f t) (d : ℝ)| ≤ eps)
    (homega : ∀ z : ℝ, |equivalentKernel r z| ≤ B_omega)
    (h16 : |((d : ℝ) ^ (2 - 2 * f t)) * firstIncrementLagCorrelation (f t) (d : ℝ)
        - f t * (2 * f t - 1)| ≤ 16 * ((d : ℝ)⁻¹)) :
    |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
        actualQ1RieszMatrix f r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
        * ((B_box + B_omega) * eps
          + 16 * B_omega * ((d : ℝ) ^ (-(1 + (2 - 2 * f t))))) := by
  classical
  have hB2 := frozenQuadFarBandEntry_le f hf r n hn δ t hS i j d hdij hdrank hd2
    x y hx hy eps B_box B_omega hprof hcorrB hclass homega h16
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hexp : ((d : ℝ) ^ (-(2 - 2 * f t))) * ((d : ℝ)⁻¹)
      = ((d : ℝ) ^ (-(1 + (2 - 2 * f t)))) := by
    have h1 : ((d : ℝ)⁻¹ : ℝ) = ((d : ℝ) ^ (-(1 : ℝ))) := by
      rw [Real.rpow_neg_one]
    rw [h1, ← Real.rpow_add hdpos (-(2 - 2 * f t : ℝ)) (-(1 : ℝ))]
    congr 1
    ring
  refine le_trans hB2 (le_of_eq ?_)
  congr 1
  rw [mul_assoc 16 ((d : ℝ) ^ (-(2 - 2 * f t))) ((d : ℝ)⁻¹), hexp]
  ring

/-! ### (D2) the word-level trace-difference assembly -/

/-! ### (D2) the word-level trace-difference assembly -/

/-- **(D2) The frozen-vs-Riesz word assembly: the trace-difference theorem.**
Conditional form landing the word engine of the assembly: eventual uniform
Frobenius bounds on `F_n = actualQ1NormalizedFrozenMatrix` and
`T_n = actualQ1RieszMatrix` plus Frobenius smallness of the difference
`‖F_n - T_n‖_F → 0` give the `hFarWord` shape
`∀ eps > 0, ∀ᶠ n, |tr(F_n ^ k) - tr(T_n ^ k)| < eps` consumed by
`Hurst.frozenQuad_hFquad_of_farWord` — via the sharp telescope bound
`abs_trace_pow_sub_le_frob` of `Hurst.FarWordAssembly` (reused, not reproved).
This packages the WORD-LEVEL endpoint of the assembly; the production of the
Frobenius smallness from the band predicate + far-band envelope inputs is the
documented remaining step (see the module docstring and the gap note). -/
theorem frozenWord_trace_diff_tendsto
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k) (B : ℝ)
    (hFb : ∀ᶠ n in atTop,
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ B)
    (hTb : ∀ᶠ n in atTop, ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ B)
    (hΔ : Tendsto (fun n : ℕ =>
        ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t
            - actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0)) :
    ∀ eps' > 0, ∀ᶠ n in atTop,
      |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| < eps' :=
  farWord_of_frobeniusSmall p M f hf r δ t k hk B hFb hTb hΔ

/-! ### (D2, assembly) the Frobenius smallness from band + far envelope

The following assembly reduces `hΔ` above to the band-predicate cutoff and the
far-band two-constant envelope.  It is LANDED here in full; the two analytic
entry hypotheses are discharged as follows:

* `hband` (the uniform band entry bound) is `frozenWord_deltaEntry_uniform_le`
  with `B_band := U + B_omega * |f t * (2 * f t - 1)|`;
* `hfar` (the far-band two-constant envelope with residual `eps`) is
  `frozenWord_deltaEntry_far_le` normalized, with
  `B_far := 16 * B_omega`, the `eps`-sequence being the uniform-in-`d`
  class/profile precision — the one genuinely remaining analytic input
  (uniform-in-`d` class convergence; see the gap note above). -/

/-- The stratified S-decay bound of `‖F_n - T_n‖²` under the cutoff + envelope
inputs: the `B_band`-beat is `O(S^{2ψ-2} * m * (2R+1))` (vanishing under the
cutoff hypothesis of `actual_q1_kernel_band_predicate_tendsto_zero`), the
`eps`-beat is `O(m² * S^{2ψ-2} * eps²) = O(S^{2ψ} * eps²)` (vanishing for
`eps = o(S^{-ψ})`), and the `B_far`-beat is `O(S^{2ψ-2} * m * R^{-(1+2ψ)})`
(vanishing for `2ψ < 1` and `R ≥ 1`, NO growth condition on `R` needed). -/
theorem frozenWord_frobenius_sq_le_explicit
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) (t' : ℝ)
    (R : ℕ) (hR : 1 ≤ R)
    (B_band : ℝ) (hBband : 0 ≤ B_band)
    (hband : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      Nat.dist i.val j.val ≤ R →
        |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
            actualQ1RieszMatrix f r n δ t i j|
          ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_band)
    (B_far : ℝ) (hBfar : 0 ≤ B_far) (eps : ℝ) (heps : 0 ≤ eps)
    (hfar : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      R < Nat.dist i.val j.val →
        |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
            actualQ1RieszMatrix f r n δ t i j|
          ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) *
            (eps + B_far * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + (2 - 2 * f t)))))) :
    ‖actualQ1NormalizedFrozenMatrix f hf r n δ t -
        actualQ1RieszMatrix f r n δ t‖ ^ 2
      ≤ ((2 : ℝ) * ((R + 1 : ℕ) : ℝ) * (localWeightActiveSet n 1 δ t).card) *
          (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_band) ^ 2
        + ((2 : ℝ) * ((localWeightActiveSet n 1 δ t).card : ℝ) ^ 2) *
          (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * eps) ^ 2
        + ((4 : ℝ) * (localWeightActiveSet n 1 δ t).card) *
          (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_far) ^ 2 *
          ((R : ℝ) ^ (-(1 + 2 * (2 - 2 * f t)))) := by
  classical
  have hS0 : 0 < (n : ℝ) * δ := by positivity
  have hftbox : f t ∈ Icc a b := hF ht
  have hpsi0 : 0 < 2 - 2 * f t := by linarith [hftbox.2]
  exact frozenWord_frobenius_sq_le_of_cutoff_envelope
    (actualQ1NormalizedFrozenMatrix f hf r n δ t -
        actualQ1RieszMatrix f r n δ t)
    (2 - 2 * f t) (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * eps)
    (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_far)
    (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_band) R
    hpsi0
    (mul_nonneg (Real.rpow_nonneg hS0.le _) heps)
    (mul_nonneg (Real.rpow_nonneg hS0.le _) hBfar)
    (mul_nonneg (Real.rpow_nonneg hS0.le _) hBband) hR
    (fun i j hd => hband i j hd)
    (fun i j hd => by
      have h := hfar i j hd
      have hsplit : ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) *
          (eps + B_far * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + (2 - 2 * f t)))))
        = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * eps +
          (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_far) *
            ((Nat.dist i.val j.val : ℝ) ^ (-(1 + (2 - 2 * f t)))) := by ring
      rw [hsplit] at h
      exact h)

/-! ### (D2, assembly) the n-dependent Frobenius smallness — LANDED -/

/-- rpow/pow bridge: `(x ^ a * c) ^ 2 = x ^ b * c ^ 2` whenever `2 * a = b`
and `0 ≤ x` — normalizes the squared envelope terms of the stratified bound. -/
private theorem sq_rpow_mul_const {x : ℝ} (c : ℝ) (hx : 0 ≤ x) (a b : ℝ)
    (hab : 2 * a = b) : (x ^ a * c) ^ 2 = x ^ b * c ^ 2 := by
  have key : (x ^ a) ^ 2 = x ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    have hex : (a * 2 : ℝ) = b := by rw [mul_comm a 2]; exact hab
    have hcast : (a * ((2 : ℕ) : ℝ)) = a * 2 := by norm_num
    rw [hcast, hex]
  rw [mul_pow, key]

/-- **(D2, assembly) the n-dependent Frobenius smallness (the documented
remaining step, LANDED).**  Under (i) the band-predicate cutoff `hcut` (the
EXACT hypothesis of `actual_q1_kernel_band_predicate_tendsto_zero`), (ii) the
near-band uniform entry bound with constant `B_band`
(`frozenWord_deltaEntry_uniform_le`), (iii) the far-band two-constant envelope
with residual sequence `eps` (`frozenWord_deltaEntry_far_le`), and (iv) the
residual decay `S^{2ψ} * eps² → 0` (i.e. `eps = o(S^{-ψ})`), the squared
Frobenius norm of the frozen-vs-Riesz difference tends to `0`.  The three
beats are exactly the stratified decay of
`frozenWord_frobenius_sq_le_explicit`: the near-band beat is
`2 * B_band² * S^{2ψ-2} * m * (2R+1) → 0` by `hcut`; the residual beat is
`2 * m² * S^{2ψ-2} * eps² ≤ 18 * S^{2ψ} * eps² → 0` by `heps` (using
`m ≤ 3 * S` from `localWeightActiveSet_card`); and the far-tail beat is
`12 * B_far² * S^{2ψ-1} → 0` for `2ψ < 1` (i.e. `3/4 < f t`) and `R ≥ 1`,
with NO growth condition on `R` (again using `m ≤ 3 * S`). -/
theorem frozenWord_frobenius_sq_tendsto_zero
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (B_band B_far : ℝ) (hBband : 0 ≤ B_band) (hBfar : 0 ≤ B_far)
    (eps : ℕ → ℝ)
    (hband : ∀ᶠ n in atTop, ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      Nat.dist i.val j.val ≤ R n →
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j -
            actualQ1RieszMatrix f r n (δ n) t i j|
          ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) * B_band)
    (hfar : ∀ᶠ n in atTop, ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      R n < Nat.dist i.val j.val →
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j -
            actualQ1RieszMatrix f r n (δ n) t i j|
          ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) *
            (eps n + B_far * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + (2 - 2 * f t))))))
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (heps : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t)) * (eps n) ^ 2) atTop (𝓝 0))
    (hε0 : ∀ᶠ n in atTop, 0 ≤ eps n) :
    Tendsto (fun n : ℕ =>
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t -
          actualQ1RieszMatrix f r n (δ n) t‖ ^ 2) atTop (𝓝 0) := by
  classical
  have hftbox : f t ∈ Icc a b := hF ht
  -- `S^{2ψ-1} → 0` since `2ψ - 1 = 3 - 4 * f t < 0` under `3/4 < f t`
  have hS21 : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1)) atTop (𝓝 0) := by
    have hneg : (2 * (2 - 2 * f t) - 1 : ℝ) < 0 := by linarith
    have hpos : (0 : ℝ) < -(2 * (2 - 2 * f t) - 1) := by linarith
    have hgrow : Tendsto (fun n : ℕ =>
        ((n : ℝ) * δ n) ^ (-(2 * (2 - 2 * f t) - 1))) atTop atTop :=
      (tendsto_rpow_atTop hpos).comp hN
    have hinv : Tendsto (fun n : ℕ =>
        (((n : ℝ) * δ n) ^ (-(2 * (2 - 2 * f t) - 1)))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hgrow
    have hcongr : (fun n : ℕ =>
          (((n : ℝ) * δ n) ^ (-(2 * (2 - 2 * f t) - 1)))⁻¹)
        =ᶠ[atTop] (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1)) := by
      filter_upwards [hδpos, eventually_gt_atTop 0] with n hδ hn
      have hSn : 0 < (n : ℝ) * δ n := mul_pos (by exact_mod_cast hn) hδ
      have hkey := Real.rpow_neg hSn.le (-(2 * (2 - 2 * f t) - 1))
      rw [neg_neg] at hkey
      exact hkey.symm
    exact Tendsto.congr' hcongr hinv
  -- the three-beat eventual bound
  have hnEv : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hS1ev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * δ n := hN.eventually_ge_atTop 1
  have hbnd : ∀ᶠ n in atTop,
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t -
          actualQ1RieszMatrix f r n (δ n) t‖ ^ 2
        ≤ (2 : ℝ) * B_band ^ 2 * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
          + ((18 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t)) * (eps n) ^ 2)
          + (12 : ℝ) * B_far ^ 2 *
              ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1)) := by
    filter_upwards [hδpos, hnEv, hS1ev, hR, hband, hfar, hε0] with n hδ hn hS1 hRn hband hfar hε0
    have hS0 : 0 < (n : ℝ) * δ n := mul_pos (by exact_mod_cast hn) hδ
    have hcard := localWeightActiveSet_card n 1 hn (δ n) t hδ hS1
    -- the stratified bound with the squared envelope terms normalized
    have hkey := frozenWord_frobenius_sq_le_explicit p a b M r hp ha hb hab hM f hf hF t
      ht hlong n hn (δ n) hδ 0 (R n) hRn B_band hBband hband B_far hBfar (eps n)
      hε0 hfar
    rw [sq_rpow_mul_const B_band hS0.le (2 - 2 * f t - 1)
          (2 * (2 - 2 * f t) - 2) (by ring),
      sq_rpow_mul_const (eps n) hS0.le (2 - 2 * f t - 1)
        (2 * (2 - 2 * f t) - 2) (by ring),
      sq_rpow_mul_const B_far hS0.le (2 - 2 * f t - 1)
        (2 * (2 - 2 * f t) - 2) (by ring)] at hkey
    -- the shared nonnegativity facts
    have hP : (0 : ℝ) ≤ ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) :=
      Real.rpow_nonneg hS0.le _
    have hm : (0 : ℝ) ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) :=
      Nat.cast_nonneg _
    have hE2 : (0 : ℝ) ≤ (eps n) ^ 2 := sq_nonneg (eps n)
    have hB2 : (0 : ℝ) ≤ B_band ^ 2 := pow_nonneg hBband 2
    have hB2f : (0 : ℝ) ≤ B_far ^ 2 := pow_nonneg hBfar 2
    -- beat 1: near band, closed by the cutoff
    have hT1 : ((2 : ℝ) * ((R n + 1 : ℕ) : ℝ) *
            ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
          (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * B_band ^ 2)
        ≤ (2 : ℝ) * B_band ^ 2 * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
            ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1)) := by
      have hRle : ((R n + 1 : ℕ) : ℝ) ≤ 2 * (R n : ℝ) + 1 := by
        have he : ((R n + 1 : ℕ) : ℝ) = (R n : ℝ) + 1 := by push_cast; ring
        rw [he]
        linarith
      have hPm : (0 : ℝ) ≤ ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 (δ n) t).card : ℝ) := mul_nonneg hP hm
      have hc : (0 : ℝ) ≤ (2 : ℝ) * B_band ^ 2 * (((n : ℝ) * δ n) ^
            (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) :=
        mul_nonneg (mul_nonneg (by norm_num) hB2) hPm
      calc ((2 : ℝ) * ((R n + 1 : ℕ) : ℝ) *
              ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
            (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * B_band ^ 2)
          = (2 : ℝ) * B_band ^ 2 * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
              ((R n + 1 : ℕ) : ℝ) := by ring
        _ ≤ (2 : ℝ) * B_band ^ 2 * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
              (2 * (R n : ℝ) + 1) := mul_le_mul_of_nonneg_left hRle hc
        _ = (2 : ℝ) * B_band ^ 2 * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
              (2 * (R n : ℝ) + 1)) := by ring
    -- beat 2: the residual `eps` sequence, closed by `heps` via `m ≤ 3 * S`
    have hS2 : ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t))
        = ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
            ((n : ℝ) * δ n) ^ ((2 : ℝ)) := by
      rw [← Real.rpow_add hS0 (2 * (2 - 2 * f t) - 2) 2]
      congr 1
      ring
    have hSnat : ((n : ℝ) * δ n) ^ ((2 : ℝ)) = ((n : ℝ) * δ n) ^ 2 :=
      Real.rpow_natCast ((n : ℝ) * δ n) 2
    have hT2 : ((2 : ℝ) * ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 2) *
          (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * (eps n) ^ 2)
        ≤ (18 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t)) * (eps n) ^ 2) := by
      have hm2 : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 2
          ≤ (3 * ((n : ℝ) * δ n)) ^ 2 := pow_le_pow_left₀ hm hcard 2
      have hPeps : (0 : ℝ) ≤ (2 : ℝ) * (((n : ℝ) * δ n) ^
            (2 * (2 - 2 * f t) - 2) * (eps n) ^ 2) :=
        mul_nonneg (by norm_num) (mul_nonneg hP hE2)
      calc ((2 : ℝ) * ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 2) *
            (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * (eps n) ^ 2)
          = (2 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * (eps n) ^ 2) *
              ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ^ 2 := by ring
        _ ≤ (2 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * (eps n) ^ 2) *
              (3 * ((n : ℝ) * δ n)) ^ 2 := mul_le_mul_of_nonneg_left hm2 hPeps
        _ = (18 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              ((n : ℝ) * δ n) ^ 2 * (eps n) ^ 2) := by ring
        _ = (18 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              ((n : ℝ) * δ n) ^ ((2 : ℝ)) * (eps n) ^ 2) := by rw [hSnat]
        _ = (18 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t)) * (eps n) ^ 2) := by
            rw [hS2]
    -- beat 3: the far tail, closed for `2ψ < 1` and `R ≥ 1` (no growth on `R`)
    have hRinv0 : (0 : ℝ) ≤ (R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t))) :=
      Real.rpow_nonneg (Nat.cast_nonneg (R n)) _
    have hRinv : (R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t))) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ (R n : ℝ) ^ (1 + 2 * (2 - 2 * f t)) :=
        Real.one_le_rpow (by exact_mod_cast hRn) (by linarith [hftbox.2])
      rw [Real.rpow_neg (Nat.cast_nonneg (R n)) (1 + 2 * (2 - 2 * f t))]
      exact inv_le_one_iff₀.2 (Or.inr h1)
    have hS1p : ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1)
        = ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * ((n : ℝ) * δ n) := by
      rw [← Real.rpow_add_one hS0.ne' (2 * (2 - 2 * f t) - 2)]
      congr 1
      ring
    have hT3 : (((4 : ℝ) * ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
            (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * B_far ^ 2) *
            ((R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t)))))
        ≤ (12 : ℝ) * B_far ^ 2 * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1) := by
      have h4 : (0 : ℝ) ≤ (4 : ℝ) * B_far ^ 2 * ((n : ℝ) * δ n) ^
            (2 * (2 - 2 * f t) - 2) :=
        mul_nonneg (mul_nonneg (by norm_num) hB2f) hP
      have h1 : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          ((R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t)))) ≤ 3 * ((n : ℝ) * δ n) := by
        calc ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
              ((R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t))))
            ≤ 3 * ((n : ℝ) * δ n) * ((R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t)))) :=
              mul_le_mul_of_nonneg_right hcard hRinv0
          _ ≤ 3 * ((n : ℝ) * δ n) * 1 :=
              mul_le_mul_of_nonneg_left hRinv (by linarith)
          _ = 3 * ((n : ℝ) * δ n) := by ring
      calc (((4 : ℝ) * ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) *
              (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) * B_far ^ 2) *
              ((R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t)))))
          = (4 : ℝ) * B_far ^ 2 * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
                ((R n : ℝ) ^ (-(1 + 2 * (2 - 2 * f t))))) := by ring
        _ ≤ (4 : ℝ) * B_far ^ 2 * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              (3 * ((n : ℝ) * δ n)) := mul_le_mul_of_nonneg_left h1 h4
        _ = (12 : ℝ) * B_far ^ 2 * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
              ((n : ℝ) * δ n)) := by ring
        _ = (12 : ℝ) * B_far ^ 2 * ((n : ℝ) * δ n) ^
              (2 * (2 - 2 * f t) - 1) := by rw [hS1p]
    linarith [hT1, hT2, hT3]
  -- squeeze against the vanishing three-beat bound
  have hzero : Tendsto (fun n : ℕ =>
      (2 : ℝ) * B_band ^ 2 * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
            ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
        + ((18 : ℝ) * (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t)) * (eps n) ^ 2)
        + (12 : ℝ) * B_far ^ 2 *
            ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1))) atTop (𝓝 0) := by
    have h1 := hcut.const_mul ((2 : ℝ) * B_band ^ 2)
    have h2 := heps.const_mul ((18 : ℝ))
    have h3 := hS21.const_mul ((12 : ℝ) * B_far ^ 2)
    simpa only [mul_zero, add_zero] using h1.add (h2.add h3)
  exact squeeze_zero'
    (Eventually.of_forall fun n => sq_nonneg
      (‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t -
          actualQ1RieszMatrix f r n (δ n) t‖)) hbnd hzero

/-- **(D2, assembly) Frobenius (unsquared) smallness.**  The norm form of
`frozenWord_frobenius_sq_tendsto_zero`, obtained by the square root (the norm
is nonnegative). -/
theorem frozenWord_frobenius_tendsto_zero
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (B_band B_far : ℝ) (hBband : 0 ≤ B_band) (hBfar : 0 ≤ B_far)
    (eps : ℕ → ℝ)
    (hband : ∀ᶠ n in atTop, ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      Nat.dist i.val j.val ≤ R n →
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j -
            actualQ1RieszMatrix f r n (δ n) t i j|
          ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) * B_band)
    (hfar : ∀ᶠ n in atTop, ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      R n < Nat.dist i.val j.val →
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j -
            actualQ1RieszMatrix f r n (δ n) t i j|
          ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) *
            (eps n + B_far * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + (2 - 2 * f t))))))
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (heps : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t)) * (eps n) ^ 2) atTop (𝓝 0))
    (hε0 : ∀ᶠ n in atTop, 0 ≤ eps n) :
    Tendsto (fun n : ℕ =>
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t -
          actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0) := by
  have hsq := frozenWord_frobenius_sq_tendsto_zero p a b M r hp ha hb hab hM f hf hF t
    ht hlong δ hδpos hN R hR B_band B_far hBband hBfar eps hband hfar hcut heps hε0
  have h1 := hsq.sqrt
  rw [Real.sqrt_zero] at h1
  have h2 : (fun n : ℕ => ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t -
        actualQ1RieszMatrix f r n (δ n) t‖)
      = (fun n : ℕ => Real.sqrt (‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t -
          actualQ1RieszMatrix f r n (δ n) t‖ ^ 2)) := by
    funext n
    exact ((Real.sqrt_sq_eq_abs
      (‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t -
          actualQ1RieszMatrix f r n (δ n) t‖)).trans
        (abs_of_nonneg (norm_nonneg _))).symm
  rw [h2]
  exact h1

/-! ### (D2) the frozen-vs-Riesz trace-difference theorem, full assembly -/

/-- **(D2) The frozen-vs-Riesz trace-difference theorem (full assembly).**
This CLOSES the word assembly of this file: under the ordinary model +
bandwidth hypotheses (Holder class, box image, `δ → 0` with `S = n * δ → ∞`,
`3/4 < f t` so that `2ψ < 1`), the eventual uniform Frobenius bounds on the
two normalized matrices, and the three analytic inputs

* `hcut` — the band-predicate cutoff `S^{2ψ-2} * m * (2R+1) → 0` (the EXACT
  hypothesis of `actual_q1_kernel_band_predicate_tendsto_zero`),
* `hband`/`hfar` — the near-band uniform entry bound
  (`frozenWord_deltaEntry_uniform_le`, `B_band := U + B_omega * |c|`) and the
  far-band two-constant envelope (`frozenWord_deltaEntry_far_le`,
  `B_far := 16 * B_omega`),
* `heps` — the explicit residual decay `S^{2ψ} * eps² → 0` (i.e.
  `eps = o(S^{-ψ})`; the uniform-in-`d` class/profile precision, the one
  genuinely remaining analytic input documented in the gap note),

the trace-difference smallness holds:
`∀ eps' > 0, ∀ᶠ n in atTop, |tr(F_n ^ k) - tr(T_n ^ k)| < eps'` — the
`hFarWord` input of `Hurst.frozenQuad_hFquad_of_farWord`, via
`farWord_of_frobeniusSmall` (sharp telescope `abs_trace_pow_sub_le_frob`). -/
theorem frozenWord_trace_diff_of_cutoff
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k) (B : ℝ)
    (hFb : ∀ᶠ n in atTop,
      ‖actualQ1NormalizedFrozenMatrix f hf r n (δ n) t‖ ≤ B)
    (hTb : ∀ᶠ n in atTop, ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ B)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (B_band B_far : ℝ) (hBband : 0 ≤ B_band) (hBfar : 0 ≤ B_far)
    (eps : ℕ → ℝ)
    (hband : ∀ᶠ n in atTop, ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      Nat.dist i.val j.val ≤ R n →
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j -
            actualQ1RieszMatrix f r n (δ n) t i j|
          ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) * B_band)
    (hfar : ∀ᶠ n in atTop, ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      R n < Nat.dist i.val j.val →
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j -
            actualQ1RieszMatrix f r n (δ n) t i j|
          ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) *
            (eps n + B_far * ((Nat.dist i.val j.val : ℝ) ^ (-(1 + (2 - 2 * f t))))))
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (heps : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t)) * (eps n) ^ 2) atTop (𝓝 0))
    (hε0 : ∀ᶠ n in atTop, 0 ≤ eps n) :
    ∀ eps' > 0, ∀ᶠ n in atTop,
      |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| < eps' := by
  refine farWord_of_frobeniusSmall p M f hf r δ t k hk B hFb hTb ?_
  exact frozenWord_frobenius_tendsto_zero p a b M r hp ha hb hab hM f hf hF t ht
    hlong δ hδpos hN R hR B_band B_far hBband hBfar eps hband hfar hcut heps hε0

end Hurst
