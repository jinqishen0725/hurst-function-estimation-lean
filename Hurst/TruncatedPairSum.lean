import Mathlib
import Hurst.TruncatedRieszCycleBridge
import Hurst.PowerSumBound
import Hurst.EdgeComparison

/-!
# Uniform two-step pair-sum bound for the S⁻¹-normalized truncated Riesz kernel

With the normalized entry magnitude

`entryMag m R S psi c B_omega a j = S⁻¹ * |c| * B_omega *
  (max (rieszCycleCutoff R) ((2/m) * Nat.dist a.val j.val)) ^ (-psi)`,

i.e. the magnitude of the `(a, j)`-entry of the `S⁻¹`-normalized truncated
Riesz matrix
`fun i j => S⁻¹ * omega (rieszCycleGridPoint m i) *
  truncatedRieszKernel R psi c (rieszCycleGridPoint m i) (rieszCycleGridPoint m j)`
with the row's `ω`-factor replaced by the bound `B_omega` (using
`|rieszCycleGridPoint m i - rieszCycleGridPoint m j| = (2/m) * Nat.dist i.val j.val`),
we prove the **uniform two-step pair-sum bound**, uniform in `a b : Fin m`:

* `pairSum_entryMag_le`:
  `∑ j, entryMag a j * entryMag b j ≤ (m / S^2) * ((|c| * B_omega)^2 *
    (rieszCycleCutoff R) ^ (-2 * psi))`.

The `m`-dependence is entirely through the `m / S^2` factor; the constant
`(|c| * B_omega)^2 * (rieszCycleCutoff R)^(-2 * psi) = (|c| * B_omega)^2 * (R+1)^(2*psi)`
is explicit, finite, uniform in `a b` (and in `m`), and only grows in `R`
(which is fixed at the point of use).  The bound in fact holds for *every*
`psi > 0` (no `psi < 1` needed); a `psi < 1` hypothesis is carried for
downstream compatibility.

The engine is the elementary observation that for `cutoff > 0` and `psi > 0`,
`max cutoff t ^ (-psi) ≤ cutoff ^ (-psi)` for all `t ≥ 0`, so every entry is at
most `S⁻¹ * |c| * B_omega * cutoff^(-psi)`.

A sharper, distance-sensitive refinement is also provided:

* `pairSum_entryMag_le_dist`: for every `j`, the triangle inequality on
  `Nat.dist` gives `D_ab ≤ D_aj + D_jb`, hence one of the two distances from
  `j` is at least `D_ab / 2`, so
  `∑ j, entryMag a j * entryMag b j ≤ (m / S^2) * ((|c| * B_omega)^2 *
    cutoff ^ (-psi) * (max cutoff ((2/m) * D_ab / 2)) ^ (-psi))`,
  which decays polynomially in `Nat.dist a.val b.val / m` and improves
  `pairSum_entryMag_le` whenever `a ≠ b` (the last factor is at most
  `cutoff ^ (-psi)`).
-/

open Real

namespace Hurst

/-! ### Negative-power helper lemmas -/

/-- Antitone nature of `t ↦ t ^ (-psi)` in the base, for positive bases. -/
private theorem rpow_neg_le_rpow_neg' {x y psi : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hpsi : 0 < psi) (h : x ≤ y) : y ^ (-psi) ≤ x ^ (-psi) := by
  have h1 : x ^ psi ≤ y ^ psi := Real.rpow_le_rpow hx.le h hpsi.le
  have hp1 : 0 < x ^ psi := Real.rpow_pos_of_pos hx _
  have hp2 : 0 < y ^ psi := Real.rpow_pos_of_pos hy _
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  exact (inv_le_inv₀ hp2 hp1).mpr h1

/-- The capped negative power is maximized at the cutoff: for `t ≥ 0`,
`max cutoff t ^ (-psi) ≤ cutoff ^ (-psi)`. -/
theorem max_rpow_neg_le_cutoff {cutoff t psi : ℝ} (hcut : 0 < cutoff)
    (hpsi : 0 < psi) : (max cutoff t) ^ (-psi) ≤ cutoff ^ (-psi) :=
  rpow_neg_le_rpow_neg' hcut (hcut.trans_le (le_max_left _ _)) hpsi (le_max_left _ _)

private theorem max_eq_right' {a b : ℝ} (h : a ≤ b) : max a b = b :=
  le_antisymm (max_le h (le_refl b)) (le_max_right a b)

private theorem max_eq_left' {a b : ℝ} (h : b ≤ a) : max a b = a :=
  le_antisymm (max_le (le_refl a) h) (le_max_left a b)

/-! ### The normalized entry magnitude -/

/-- **Normalized entry magnitude**: the magnitude of the `(a, j)`-entry of the
`S⁻¹`-normalized truncated Riesz matrix, with the row's `ω`-factor bounded by
`B_omega`. -/
noncomputable def entryMag (m R : ℕ) (S psi c B_omega : ℝ) (a j : Fin m) : ℝ :=
  (S : ℝ)⁻¹ * |c| * B_omega *
    (max (rieszCycleCutoff R)
      ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))) ^ (-psi)

theorem entryMag_nonneg (m R : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S)
    (hB : 0 ≤ B_omega) (a j : Fin m) : 0 ≤ entryMag m R S psi c B_omega a j := by
  unfold entryMag
  exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (abs_nonneg c)) hB)
    (Real.rpow_nonneg (le_trans (rieszCycleCutoff_pos R).le (le_max_left _ _)) (-psi))

/-- Each normalized entry magnitude is at most `S⁻¹ * |c| * B_omega *
cutoff^(-psi)`, uniformly in the column index. -/
theorem entryMag_le_cutoff (m R : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S)
    (hpsi : 0 < psi) (hB : 0 ≤ B_omega) (a j : Fin m) :
    entryMag m R S psi c B_omega a j
      ≤ (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) := by
  unfold entryMag
  exact mul_le_mul_of_nonneg_left (max_rpow_neg_le_cutoff (rieszCycleCutoff_pos R) hpsi)
    (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (abs_nonneg c)) hB)

/-! ### The uniform two-step pair-sum bound -/

/-- **Uniform two-step pair-sum bound.** For `S > 0`, `psi > 0`, `B_omega ≥ 0`,
uniformly in `a b : Fin m`,
`∑ j, entryMag a j * entryMag b j ≤ (m / S^2) * ((|c| * B_omega)^2 *
  (rieszCycleCutoff R) ^ (-2 * psi))`.

The `m`-dependence is entirely through the factor `m / S^2` times the explicit
constant `(|c| * B_omega)^2 * (R + 1) ^ (2 * psi)`, which is finite and fixed
once `R`, `psi`, `c`, `B_omega` are fixed (it grows in `R`, which is fine since
`R` is fixed at the point of use). -/
theorem pairSum_entryMag_le (m R : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S)
    (hpsi : 0 < psi) (_hpsi1 : psi < 1) (hB : 0 ≤ B_omega) (a b : Fin m) :
    (∑ j : Fin m, entryMag m R S psi c B_omega a j * entryMag m R S psi c B_omega b j)
      ≤ ((m : ℝ) / S ^ 2) * ((|c| * B_omega) ^ 2 *
        (rieszCycleCutoff R) ^ (-2 * psi)) := by
  set u : ℝ := (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) with hudef
  have hu0 : 0 ≤ u := by
    rw [hudef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (abs_nonneg c)) hB)
      (Real.rpow_nonneg (rieszCycleCutoff_pos R).le (-psi))
  have hx0 : ∀ j : Fin m, 0 ≤ entryMag m R S psi c B_omega a j :=
    fun j => entryMag_nonneg m R S psi c B_omega hS hB a j
  have hy0 : ∀ j : Fin m, 0 ≤ entryMag m R S psi c B_omega b j :=
    fun j => entryMag_nonneg m R S psi c B_omega hS hB b j
  have hterm : ∀ j : Fin m,
      entryMag m R S psi c B_omega a j * entryMag m R S psi c B_omega b j
        ≤ u * u := by
    intro j
    have h1 := entryMag_le_cutoff m R S psi c B_omega hS hpsi hB a j
    have h2 := entryMag_le_cutoff m R S psi c B_omega hS hpsi hB b j
    exact le_trans (mul_le_mul_of_nonneg_right h1 (hy0 j))
      (mul_le_mul_of_nonneg_left h2 hu0)
  have hsum : (∑ j : Fin m,
      entryMag m R S psi c B_omega a j * entryMag m R S psi c B_omega b j)
      ≤ (m : ℝ) * (u * u) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
      hterm j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  have hrpow : (rieszCycleCutoff R) ^ (-psi) * (rieszCycleCutoff R) ^ (-psi)
      = (rieszCycleCutoff R) ^ (-2 * psi) := by
    rw [← Real.rpow_add (rieszCycleCutoff_pos R),
      show (-psi) + (-psi) = (-2 : ℝ) * psi by ring]
  have hA : (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) *
      ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi))
      = ((S : ℝ)⁻¹ * |c| * B_omega) ^ 2 *
        ((rieszCycleCutoff R) ^ (-psi) * (rieszCycleCutoff R) ^ (-psi)) := by
    rw [pow_two]
    ring
  have hexp : u * u = (S : ℝ)⁻¹ ^ 2 * (|c| * B_omega) ^ 2 *
      (rieszCycleCutoff R) ^ (-2 * psi) := by
    rw [hudef, hA, hrpow]
    ring
  refine le_trans hsum ?_
  rw [hexp]
  exact le_of_eq (by ring)

/-! ### Distance-sensitive refinement -/

/-- For every column `j`, the pair of normalized entries satisfies the joint
geometric bound `entryMag a j * entryMag b j ≤ (S⁻¹ * |c| * B_omega)² *
cutoff^(-psi) * (max cutoff ((2/m) * D_ab / 2)) ^ (-psi)`, using
`D_ab ≤ D_aj + D_jb` (triangle inequality for `Nat.dist`): one of the two
distances from `j` is at least `D_ab / 2`. -/
theorem entryMag_mul_le_dist (m R : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S)
    (hpsi : 0 < psi) (hB : 0 ≤ B_omega) (a b j : Fin m) :
    entryMag m R S psi c B_omega a j * entryMag m R S psi c B_omega b j
      ≤ ((S : ℝ)⁻¹ * |c| * B_omega) ^ 2 * (rieszCycleCutoff R) ^ (-psi) *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi) := by
  classical
  have hcut : 0 < rieszCycleCutoff R := rieszCycleCutoff_pos R
  have hdelta0 : 0 ≤ (2 : ℝ) / (m : ℝ) := div_nonneg (by norm_num) (by positivity)
  -- triangle inequality: D_ab ≤ D_aj + D_jb
  have htri : ((Nat.dist a.val b.val : ℕ) : ℝ)
      ≤ ((Nat.dist a.val j.val : ℕ) : ℝ) + ((Nat.dist b.val j.val : ℕ) : ℝ) := by
    have h := Nat.dist.triangle_inequality a.val j.val b.val
    rw [Nat.dist_comm j.val b.val] at h
    exact_mod_cast h
  -- W := (2/m) * D_ab / 2 ≤ max ((2/m) * D_aj) ((2/m) * D_bj)
  have hWle : (2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2)
      ≤ max ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))
        ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ)) := by
    have hprod : (2 : ℝ) / (m : ℝ) * ((Nat.dist a.val b.val : ℕ) : ℝ)
        ≤ (2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ)
          + (2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ) := by
      refine (mul_le_mul_of_nonneg_left htri hdelta0).trans ?_
      rw [mul_add]
    have hM1 : (2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ)
        ≤ max ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ)) := le_max_left _ _
    have hM2 : (2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ)
        ≤ max ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ)) := le_max_right _ _
    linarith
  have hpos : ∀ t : ℝ, 0 < max (rieszCycleCutoff R) t :=
    fun t => hcut.trans_le (le_max_left _ _)
  -- the joint per-column bound
  have key : (max (rieszCycleCutoff R)
        ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))) ^ (-psi) *
      (max (rieszCycleCutoff R)
        ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ))) ^ (-psi)
      ≤ (rieszCycleCutoff R) ^ (-psi) *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi) := by
    rcases le_total ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))
        ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ)) with hXY | hYX
    · -- X ≤ Y: the Y-capped base dominates the W-capped base
      have hu0 : 0 ≤ (rieszCycleCutoff R) ^ (-psi) :=
        Real.rpow_nonneg hcut.le (-psi)
      have hfb0 : 0 ≤ (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ))) ^ (-psi) :=
        Real.rpow_nonneg (le_trans hcut.le (le_max_left _ _)) (-psi)
      have hWY : (2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2)
          ≤ (2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ) :=
        hWle.trans (by rw [max_eq_right' hXY])
      have hXle : (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))) ^ (-psi)
          ≤ (rieszCycleCutoff R) ^ (-psi) := max_rpow_neg_le_cutoff hcut hpsi
      have hYge : (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ))) ^ (-psi)
          ≤ (max (rieszCycleCutoff R)
            ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi) :=
        rpow_neg_le_rpow_neg' (hpos _) (hpos _) hpsi (max_le_max (le_refl _) hWY)
      refine le_trans (mul_le_mul_of_nonneg_right hXle hfb0) ?_
      refine le_trans (le_of_eq (mul_comm ((rieszCycleCutoff R) ^ (-psi))
        ((max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ))) ^ (-psi)))) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hYge hu0) ?_
      exact le_of_eq (mul_comm ((max (rieszCycleCutoff R)
        ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi))
        ((rieszCycleCutoff R) ^ (-psi)))
    · -- Y ≤ X: symmetric
      have hu0 : 0 ≤ (rieszCycleCutoff R) ^ (-psi) :=
        Real.rpow_nonneg hcut.le (-psi)
      have hfa0 : 0 ≤ (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))) ^ (-psi) :=
        Real.rpow_nonneg (le_trans hcut.le (le_max_left _ _)) (-psi)
      have hWX : (2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2)
          ≤ (2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ) :=
        hWle.trans (by rw [max_eq_left' hYX])
      have hYle : (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ))) ^ (-psi)
          ≤ (rieszCycleCutoff R) ^ (-psi) := max_rpow_neg_le_cutoff hcut hpsi
      have hXge : (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))) ^ (-psi)
          ≤ (max (rieszCycleCutoff R)
            ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi) :=
        rpow_neg_le_rpow_neg' (hpos _) (hpos _) hpsi (max_le_max (le_refl _) hWX)
      refine le_trans (mul_le_mul_of_nonneg_left hYle hfa0) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hXge hu0) ?_
      exact le_of_eq (mul_comm ((max (rieszCycleCutoff R)
        ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi))
        ((rieszCycleCutoff R) ^ (-psi)))
  -- assemble
  unfold entryMag
  have hK0 : 0 ≤ (S : ℝ)⁻¹ * |c| * B_omega :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (abs_nonneg c)) hB
  calc (S : ℝ)⁻¹ * |c| * B_omega *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))) ^ (-psi) *
        ((S : ℝ)⁻¹ * |c| * B_omega *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ))) ^ (-psi))
      = (S : ℝ)⁻¹ * |c| * B_omega *
        ((S : ℝ)⁻¹ * |c| * B_omega *
        ((max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist a.val j.val : ℕ) : ℝ))) ^ (-psi) *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * ((Nat.dist b.val j.val : ℕ) : ℝ))) ^ (-psi))) := by ring
    _ ≤ (S : ℝ)⁻¹ * |c| * B_omega *
        ((S : ℝ)⁻¹ * |c| * B_omega *
        ((rieszCycleCutoff R) ^ (-psi) *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hK0) hK0
    _ = ((S : ℝ)⁻¹ * |c| * B_omega) ^ 2 * (rieszCycleCutoff R) ^ (-psi) *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi) := by ring

/-- **Distance-sensitive uniform pair-sum bound.** For `S > 0`, `psi > 0`,
`B_omega ≥ 0`, uniformly in `a b : Fin m`,
`∑ j, entryMag a j * entryMag b j ≤ (m / S^2) * ((|c| * B_omega)^2 *
  cutoff ^ (-psi) * (max cutoff ((2/m) * D_ab / 2)) ^ (-psi))` where
`D_ab = Nat.dist a.val b.val`.  This refines `pairSum_entryMag_le` (the last
factor is at most `cutoff ^ (-psi)`) and decays polynomially in `D_ab / m`,
i.e. in the mesh distance between the two rows. -/
theorem pairSum_entryMag_le_dist (m R : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S)
    (hpsi : 0 < psi) (_hpsi1 : psi < 1) (hB : 0 ≤ B_omega) (a b : Fin m) :
    (∑ j : Fin m, entryMag m R S psi c B_omega a j * entryMag m R S psi c B_omega b j)
      ≤ ((m : ℝ) / S ^ 2) * ((|c| * B_omega) ^ 2 * (rieszCycleCutoff R) ^ (-psi) *
        (max (rieszCycleCutoff R)
          ((2 : ℝ) / (m : ℝ) * (((Nat.dist a.val b.val : ℕ) : ℝ) / 2))) ^ (-psi)) := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    entryMag_mul_le_dist m R S psi c B_omega hS hpsi hB a b j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  refine le_trans h ?_
  exact le_of_eq (by ring)

end Hurst
