import Mathlib
import Hurst.PowerSumBound

/-!
# Sharp weighted band power-sums (the `2 * psi < 1` decay)

For `0 < psi < 1/2` we land the sharp weighted band power-sum estimates used to
make Predicate-2 band terms vanish:

* `band_rpow_sum_le`: `∑_{d ∈ range D} ((d + 1 : ℝ)) ^ (-2 psi) ≤ (1 / (1 - 2 psi)) *
  D ^ (1 - 2 psi)` — `Hurst.sum_range_rpow_neg_le'` at `β = 2 * psi` (sharp, no `+ 1`).
  (`((d + 1 : ℝ))` is `↑d + 1`; `band_rpow_sum_le_cast` is the `↑(d + 1)` form.)
* `sum_range_rpow_neg_shift_le`: the unshifted variant `∑_{d ∈ range D} d ^ (-β) ≤
  D ^ (1 - β) / (1 - β)` (the `d = 0` term vanishes since `β > 0`).
* `band_weighted_le`: the scaled form
  `∑_{d ∈ range D} ((2 / m) * d) ^ (-2 psi) ≤ (2 / m) ^ (-2 psi) * (1 / (1 - 2 psi)) *
  D ^ (1 - 2 psi)` (the `d = 0` term contributes `0`, so no constant is lost).
* `band_cutoff_weighted_le`: the cutoff-capped m-normalized cousin, sharp form:
  `∑_{d ∈ range D} (max cutoff ((2 / m) * d)) ^ (-2 psi) ≤ cutoff ^ (-2 psi) +
  (2 / m) ^ (-2 psi) * (1 / (1 - 2 psi)) * D ^ (1 - 2 psi)`
  (one exceptional term `d = 0` at the cap, the rest decay sharply).
* `band_cutoff_sum_trivial`: the trivial count-times-cap bound
  `∑_{d ∈ range D} (max cutoff ((2 / m) * d)) ^ (-2 psi) ≤ D * cutoff ^ (-2 psi)`.
* `band_cutoff_weighted_le_min`: the combined `min` of the two bounds above —
  the single form a consumer can combine directly.
* `band_cutoff_square_le_of_card`: the band-Frobenius-square count-times-cap
  corollary for an arbitrary finite band of indices with `s.card ≤ K`.

The engine is `Hurst.sum_range_rpow_neg_le'` from `Hurst.PowerSumBound`.
-/

namespace Hurst

/-! ### Antitone helpers for capped negative powers -/

/-- For positive bases, `t ↦ t ^ (-psi)` is antitone. -/
private theorem rpow_neg_antitone {x y psi : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hpsi : 0 < psi) (h : x ≤ y) : y ^ (-psi) ≤ x ^ (-psi) := by
  have h1 : x ^ psi ≤ y ^ psi := Real.rpow_le_rpow hx.le h hpsi.le
  have hp1 : 0 < x ^ psi := Real.rpow_pos_of_pos hx _
  have hp2 : 0 < y ^ psi := Real.rpow_pos_of_pos hy _
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  exact (inv_le_inv₀ hp2 hp1).mpr h1

/-- The capped negative power is maximized at the cutoff:
`(max cutoff t) ^ (-psi) ≤ cutoff ^ (-psi)` for `cutoff > 0`, `psi > 0`. -/
private theorem max_rpow_neg_le_cutoff' {cutoff t psi : ℝ} (hcut : 0 < cutoff)
    (hpsi : 0 < psi) : (max cutoff t) ^ (-psi) ≤ cutoff ^ (-psi) :=
  rpow_neg_antitone hcut (hcut.trans_le (le_max_left cutoff t)) hpsi (le_max_left cutoff t)

/-- For `t > 0`, the capped negative power is at most the uncapped one:
`(max cutoff t) ^ (-psi) ≤ t ^ (-psi)`. -/
private theorem max_rpow_neg_le_rpow_neg {cutoff t psi : ℝ} (_hcut : 0 < cutoff)
    (ht : 0 < t) (hpsi : 0 < psi) : (max cutoff t) ^ (-psi) ≤ t ^ (-psi) :=
  rpow_neg_antitone ht (ht.trans_le (le_max_right cutoff t)) hpsi (le_max_right cutoff t)

/-- The capped negative power at the square exponent `(-2 * psi)` is maximized at
the cutoff: `(max cutoff t) ^ (-2 * psi) ≤ cutoff ^ (-2 * psi)` for `cutoff > 0`,
`psi > 0`. Stated at the `(-2 * psi)` exponent form used in all band statements. -/
private theorem max_rpow_neg_two_le_cutoff' {cutoff t psi : ℝ} (hcut : 0 < cutoff)
    (hpsi : 0 < psi) : (max cutoff t) ^ (-2 * psi) ≤ cutoff ^ (-2 * psi) := by
  have h := max_rpow_neg_le_cutoff' (t := t) hcut (show (0 : ℝ) < 2 * psi from by linarith)
  rw [show (-(2 * psi)) = (-2 * psi) from by ring] at h
  exact h

/-- Termwise cap step for `d ≥ 1`: the cutoff-capped negative square power is at
most the uncapped one, factored as a constant times `d ^ (-2 * psi)`. -/
private theorem cap_termwise (m : ℕ) (hm : 0 < m) {cutoff psi : ℝ} (hcut : 0 < cutoff)
    (hpsi : 0 < psi) (d : ℕ) (hd : 0 < d) :
    (max cutoff (((2 : ℝ) / m) * d) ^ (-2 * psi))
      ≤ ((2 : ℝ) / m) ^ (-2 * psi) * (d ^ (-2 * psi)) := by
  have hpos : 0 < ((2 : ℝ) / m) * d :=
    mul_pos (div_pos (by norm_num) (by exact_mod_cast hm)) (by exact_mod_cast hd)
  have hmax := max_rpow_neg_le_rpow_neg hcut hpos
    (show (0 : ℝ) < 2 * psi from by linarith)
  rw [show (-(2 * psi)) = (-2 * psi) from by ring] at hmax
  refine le_trans hmax ?_
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) / m)
    (by positivity : (0 : ℝ) ≤ d)]

/-! ### The sharp band power-sum -/

/-- **Sharp band power-sum.** For `0 < psi` with `2 * psi < 1`,
`∑_{d ∈ range D} ((d + 1 : ℝ)) ^ (-2 psi) ≤ (1 / (1 - 2 psi)) * D ^ (1 - 2 psi)`.
This is `Hurst.sum_range_rpow_neg_le'` at `β = 2 * psi`, with the division
displayed as multiplication by the reciprocal. -/
theorem band_rpow_sum_le (D : ℕ) (psi : ℝ) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1) :
    (∑ d ∈ Finset.range D, ((d + 1 : ℝ)) ^ (-2 * psi))
      ≤ (1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi)) := by
  have hβ1 : 0 < 2 * psi := by linarith
  have h := sum_range_rpow_neg_le' hβ1 hpsi2 D
  rw [show (-(2 * psi)) = (-2 * psi) from by ring] at h
  have hc : ∀ d ∈ Finset.range D, ((d + 1 : ℕ) : ℝ) = ((d + 1 : ℝ)) := by
    intro d _
    push_cast
    rfl
  rw [Finset.sum_congr rfl (fun d hd => by rw [← hc d hd]), one_div_mul_eq_div]
  exact h

/-- The `↑(d + 1)`-cast form of the sharp band power-sum, matching the exact term
shape of `Hurst.sum_range_rpow_neg_le'`. -/
theorem band_rpow_sum_le_cast (D : ℕ) (psi : ℝ) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1) :
    (∑ d ∈ Finset.range D, ((d + 1 : ℕ) : ℝ) ^ (-2 * psi))
      ≤ (1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi)) := by
  have hβ1 : 0 < 2 * psi := by linarith
  have h := sum_range_rpow_neg_le' hβ1 hpsi2 D
  rw [show (-(2 * psi)) = (-2 * psi) from by ring] at h
  rw [one_div_mul_eq_div]
  exact h

/-- Unshifted variant: for `0 < β < 1`,
`∑_{d ∈ range D} d ^ (-β) ≤ D ^ (1 - β) / (1 - β)`. The `d = 0` term vanishes
since `β > 0`, and the shift `d ↦ d + 1` costs only the last term `D ^ (-β) ≥ 0`. -/
theorem sum_range_rpow_neg_shift_le {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1) (D : ℕ) :
    (∑ d ∈ Finset.range D, ((d : ℝ) ^ (-β))) ≤ ((D : ℝ) ^ (1 - β)) / (1 - β) := by
  have hne : (-β : ℝ) ≠ 0 := by linarith
  have hzero : (((0 : ℕ) : ℝ) ^ (-β)) = 0 := by
    have hc0 : (((0 : ℕ) : ℝ) = (0 : ℝ)) := Nat.cast_zero
    rw [hc0]
    exact Real.zero_rpow hne
  have hcomm : (∑ d ∈ Finset.range (D + 1), ((d : ℝ) ^ (-β)))
      = (∑ d ∈ Finset.range D, (((d + 1 : ℕ) : ℝ) ^ (-β))) + (((0 : ℕ) : ℝ) ^ (-β)) :=
    Finset.sum_range_succ' (fun d : ℕ => ((d : ℝ) ^ (-β))) D
  rw [hzero] at hcomm
  have hsucc : (∑ d ∈ Finset.range (D + 1), ((d : ℝ) ^ (-β)))
      = ∑ d ∈ Finset.range D, ((d : ℝ) ^ (-β)) + ((D : ℝ) ^ (-β)) :=
    Finset.sum_range_succ (fun d : ℕ => ((d : ℝ) ^ (-β))) D
  rw [hsucc] at hcomm
  have h1 := sum_range_rpow_neg_le' hβ1 hβ2 D
  have hDpos : 0 ≤ ((D : ℝ) ^ (-β)) := Real.rpow_nonneg (Nat.cast_nonneg D) (-β)
  calc (∑ d ∈ Finset.range D, ((d : ℝ) ^ (-β)))
      ≤ ∑ d ∈ Finset.range D, ((d : ℝ) ^ (-β)) + ((D : ℝ) ^ (-β)) := by linarith
    _ = (∑ d ∈ Finset.range D, (((d + 1 : ℕ) : ℝ) ^ (-β))) + 0 := hcomm
    _ ≤ ((D : ℝ) ^ (1 - β)) / (1 - β) := by rwa [add_zero]

/-! ### The scaled (m-normalized) form used downstream -/

/-- **Scaled band power-sum.** For `m > 0`, `0 < psi`, `2 * psi < 1`,
`∑_{d ∈ range D} ((2 / m) * d) ^ (-2 psi)
  ≤ (2 / m) ^ (-2 psi) * (1 / (1 - 2 psi)) * D ^ (1 - 2 psi)`.
The `d = 0` term contributes `0`, so the constant is sharp. -/
theorem band_weighted_le (m D : ℕ) (hm : 0 < m) (psi : ℝ) (hpsi1 : 0 < psi)
    (hpsi2 : 2 * psi < 1) :
    (∑ d ∈ Finset.range D, (((2 : ℝ) / m * d) ^ (-2 * psi)))
      ≤ ((2 : ℝ) / m) ^ (-2 * psi) * (1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi)) := by
  have hβ1 : 0 < 2 * psi := by linarith
  have hbase : 0 ≤ (2 : ℝ) / m := by positivity
  have hterm : ∀ d : ℕ, (((2 : ℝ) / m * (d : ℝ)) ^ (-2 * psi))
      = ((2 : ℝ) / m) ^ (-2 * psi) * ((d : ℝ) ^ (-2 * psi)) := fun d =>
    Real.mul_rpow hbase (Nat.cast_nonneg d)
  have hsum : (∑ d ∈ Finset.range D, (((2 : ℝ) / m * (d : ℝ)) ^ (-2 * psi)))
      = ((2 : ℝ) / m) ^ (-2 * psi) * ∑ d ∈ Finset.range D, ((d : ℝ) ^ (-2 * psi)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => hterm d)
  rw [hsum]
  have h2 := sum_range_rpow_neg_shift_le hβ1 hpsi2 D
  rw [show (-(2 * psi)) = (-2 * psi) from by ring] at h2
  calc ((2 : ℝ) / m) ^ (-2 * psi) * ∑ d ∈ Finset.range D, ((d : ℝ) ^ (-2 * psi))
      ≤ ((2 : ℝ) / m) ^ (-2 * psi) * (((D : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hbase (-2 * psi))
    _ = ((2 : ℝ) / m) ^ (-2 * psi) * (1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi)) := by
        ring

/-! ### The cutoff-capped m-normalized cousin (both bounds) -/

/-- **Sharp cutoff-capped band power-sum.** For `m > 0`, `0 < psi`, `2 * psi < 1`
and `cutoff > 0`,
`∑_{d ∈ range D} (max cutoff ((2 / m) * d)) ^ (-2 psi)
  ≤ cutoff ^ (-2 psi) + (2 / m) ^ (-2 psi) * (1 / (1 - 2 psi)) * D ^ (1 - 2 psi)`.
The single exceptional term `d = 0` contributes the cap `cutoff ^ (-2 psi)`;
every other term is bounded sharply. -/
theorem band_cutoff_weighted_le (m D : ℕ) (hm : 0 < m) (cutoff psi : ℝ)
    (hcut : 0 < cutoff) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1) :
    (∑ d ∈ Finset.range D, (max cutoff (((2 : ℝ) / m) * d) ^ (-2 * psi)))
      ≤ cutoff ^ (-2 * psi)
        + ((2 : ℝ) / m) ^ (-2 * psi) * (1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi)) := by
  have hm2 : (0 : ℝ) < (2 : ℝ) / (m : ℝ) := div_pos (by norm_num) (by exact_mod_cast hm)
  have hβ1 : 0 < 2 * psi := by linarith
  rcases Nat.eq_zero_or_pos D with hD | hD
  · -- D = 0: empty sum
    subst hD
    have hcap : 0 ≤ cutoff ^ (-2 * psi) := Real.rpow_nonneg hcut.le (-2 * psi)
    have hne : (1 - 2 * psi : ℝ) ≠ 0 := by linarith
    have hexp0 : (((0 : ℕ) : ℝ) ^ (1 - 2 * psi)) = 0 := by
      have hc0 : (((0 : ℕ) : ℝ) = (0 : ℝ)) := Nat.cast_zero
      rw [hc0]
      exact Real.zero_rpow hne
    have hrest0 : (((2 : ℝ) / m) ^ (-2 * psi) * (1 / (1 - 2 * psi))
          * (((0 : ℕ) : ℝ) ^ (1 - 2 * psi))) = 0 := by
      rw [hexp0, mul_zero]
    have hsum0 : (∑ d ∈ Finset.range 0,
        (max cutoff (((2 : ℝ) / m) * d) ^ (-2 * psi))) = 0 := by simp
    rw [hsum0, hrest0]
    linarith
  · -- D ≥ 1: peel off the `d = 0` term at the cap, bound the rest sharply
    have hD1 : (D - 1) + 1 = D := by omega
    have hbase : 0 ≤ (2 : ℝ) / m := hm2.le
    have hpsi1' : 0 < psi := hpsi1
    set g : ℕ → ℝ := fun d => (max cutoff (((2 : ℝ) / m) * (d : ℝ)) ^ (-2 * psi)) with hg
    have hcomm : (∑ d ∈ Finset.range D, g d)
        = (∑ d ∈ Finset.range (D - 1), g ((d : ℕ) + 1)) + g 0 := by
      have h := Finset.sum_range_succ' g (D - 1)
      rwa [show (D - 1 + 1) = D from hD1] at h
    have hzero_term : g 0 = cutoff ^ (-2 * psi) := by
      have h0 : (((2 : ℝ) / m) * ((0 : ℕ) : ℝ)) = 0 := by ring
      show (max cutoff (((2 : ℝ) / m) * ((0 : ℕ) : ℝ)) ^ (-2 * psi)) = cutoff ^ (-2 * psi)
      rw [h0, max_eq_left hcut.le]
    have hdist : ∀ d : ℕ, 0 < ((2 : ℝ) / m) * (((d + 1 : ℕ) : ℝ)) := by
      intro d
      exact mul_pos hm2 (by positivity)
    have htail : (∑ d ∈ Finset.range (D - 1), g ((d : ℕ) + 1))
        ≤ ((2 : ℝ) / m) ^ (-2 * psi) * ((1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi))) := by
      have hsub : (∑ d ∈ Finset.range (D - 1), g ((d : ℕ) + 1))
          ≤ ∑ d ∈ Finset.range (D - 1),
              (((2 : ℝ) / m) ^ (-2 * psi) * (((d + 1 : ℕ) : ℝ) ^ (-2 * psi))) := by
        simp only [hg]
        exact Finset.sum_le_sum (fun d _ =>
          cap_termwise m hm hcut hpsi1' ((d : ℕ) + 1) (Nat.succ_pos d))
      have hshift : (∑ d ∈ Finset.range (D - 1), (((d + 1 : ℕ) : ℝ) ^ (-2 * psi))
          ) ≤ ∑ d ∈ Finset.range D, (((d + 1 : ℕ) : ℝ) ^ (-2 * psi)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => ?_)
        · have hdlt : d < D - 1 := Finset.mem_range.1 hd
          exact Finset.mem_range.2 (by omega)
        · exact Real.rpow_nonneg (by positivity) (-2 * psi)
      have hsharp := band_rpow_sum_le_cast D psi hpsi1' hpsi2
      have hnonneg : 0 ≤ ((2 : ℝ) / m) ^ (-2 * psi) := Real.rpow_nonneg hbase (-2 * psi)
      calc (∑ d ∈ Finset.range (D - 1), g ((d : ℕ) + 1))
          ≤ ∑ d ∈ Finset.range (D - 1),
              (((2 : ℝ) / m) ^ (-2 * psi) * (((d + 1 : ℕ) : ℝ) ^ (-2 * psi))) := hsub
        _ = ((2 : ℝ) / m) ^ (-2 * psi) * ∑ d ∈ Finset.range (D - 1),
              (((d + 1 : ℕ) : ℝ) ^ (-2 * psi)) := (Finset.mul_sum _ _ _).symm
        _ ≤ ((2 : ℝ) / m) ^ (-2 * psi) * ((1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi))) :=
              mul_le_mul_of_nonneg_left (le_trans hshift hsharp) hnonneg
    rw [hcomm, hzero_term]
    have hcap : 0 ≤ cutoff ^ (-2 * psi) := Real.rpow_nonneg hcut.le (-2 * psi)
    linarith

/-- **Trivial count-times-cap bound.** For `cutoff > 0`, `psi > 0`,
`∑_{d ∈ range D} (max cutoff ((2 / m) * d)) ^ (-2 psi) ≤ D * cutoff ^ (-2 psi)`
(each term is capped at `cutoff ^ (-2 psi)`). -/
theorem band_cutoff_sum_trivial (m D : ℕ) (cutoff psi : ℝ) (hcut : 0 < cutoff)
    (hpsi : 0 < psi) :
    (∑ d ∈ Finset.range D, (max cutoff (((2 : ℝ) / m) * d) ^ (-2 * psi)))
      ≤ (D : ℝ) * cutoff ^ (-2 * psi) := by
  have hterm : ∀ d ∈ Finset.range D,
      (max cutoff (((2 : ℝ) / m) * d) ^ (-2 * psi)) ≤ cutoff ^ (-2 * psi) :=
    fun d _ => max_rpow_neg_two_le_cutoff' hcut hpsi
  have h := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range] at h
  exact h

/-- **Combined band power-sum bound (both forms at once).** The consumer-facing
single statement: the cutoff-capped sum is bounded by the `min` of the trivial
count-times-cap bound and the sharp `2 * psi`-decay bound (plus one cap term).
This is the form downstream consumers can combine directly: the trivial side is
useful when `m * cutoff` is small, the sharp side exhibits the `2 * psi < 1`
decay `(2 / m) ^ (-2 psi) * D ^ (1 - 2 psi) = (m / 2) ^ (2 psi) * D ^ (1 - 2 psi)`. -/
theorem band_cutoff_weighted_le_min (m D : ℕ) (hm : 0 < m) (cutoff psi : ℝ)
    (hcut : 0 < cutoff) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1) :
    (∑ d ∈ Finset.range D, (max cutoff (((2 : ℝ) / m) * d) ^ (-2 * psi)))
      ≤ min ((D : ℝ) * cutoff ^ (-2 * psi))
          (cutoff ^ (-2 * psi)
            + ((2 : ℝ) / m) ^ (-2 * psi) * (1 / (1 - 2 * psi)) * ((D : ℝ) ^ (1 - 2 * psi))) := by
  exact le_min (band_cutoff_sum_trivial m D cutoff psi hcut hpsi1)
    (band_cutoff_weighted_le m D hm cutoff psi hcut hpsi1 hpsi2)

/-! ### Band-Frobenius-square corollary (count × cap) -/

/-- **Band Frobenius square, count-times-cap form.** For any finite band `s` of
indices with `s.card ≤ K` and any distance profile `Df : ι → ℕ`,
`∑_{j ∈ s} (max cutoff ((2 / m) * Df j)) ^ (-2 psi) ≤ K * cutoff ^ (-2 psi)`.
The consumer plugs in its own band set together with a count bound such as
`2 * (m * cutoff + 2)` for `K`. -/
theorem band_cutoff_square_le_of_card {ι : Type*} (s : Finset ι) (Df : ι → ℕ)
    (K : ℕ) (hK : s.card ≤ K) (m : ℕ) (cutoff psi : ℝ) (hcut : 0 < cutoff)
    (hpsi : 0 < psi) :
    (∑ j ∈ s, (max cutoff (((2 : ℝ) / m) * (Df j : ℝ)) ^ (-2 * psi)))
      ≤ (K : ℝ) * cutoff ^ (-2 * psi) := by
  have hterm : ∀ j ∈ s, (max cutoff (((2 : ℝ) / m) * (Df j : ℝ)) ^ (-2 * psi))
      ≤ cutoff ^ (-2 * psi) := fun j _ => max_rpow_neg_two_le_cutoff' hcut hpsi
  have h := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at h
  have hcast : ((s.card : ℝ) ≤ (K : ℝ)) := Nat.cast_le.2 hK
  exact le_trans h
    (mul_le_mul_of_nonneg_right hcast (Real.rpow_nonneg hcut.le (-2 * psi)))
