import Mathlib
import Hurst.LatticeReindex
import Hurst.DiscreteRieszCycleBridge
import Hurst.TruncatedRieszCycleBridge
import Hurst.MeshFactorizationLimit

/-!
# Per-edge comparison between the untruncated discrete Riesz kernel and the
mesh-scaled truncated Riesz cycle kernel

Fix the grid `Fin m` with right-endpoint grid points `rieszCycleGridPoint m i`,
so the grid distance between `i` and `j` is `(2 : ℝ) / m * D` for the integer
distance `D = Nat.dist i.val j.val` (by `abs_sub_rieszCycleGridPoint_eq`).
Write `rieszCycleCutoff R = ((R + 1 : ℕ) : ℝ)⁻¹` for the truncation strip and
`rho = (2 * S / m) ^ psi` for the mesh correction factor of
`Hurst.MeshFactorizationLimit`.

Main results:

* `rpowMeshFactor`, `scaledUnitMeshMaxEq`: off band
  (`rieszCycleCutoff R ≤ (2/m) * D`) the untruncated scaled unit edge
  `S ^ psi * D ^ (-psi)` equals `rho` times the capped-distance value
  `max (rieszCycleCutoff R) ((2/m) * D) ^ (-psi)`, exactly.
* `rankRieszKernelEqRhoMulTruncated`: the matrix-entry identity
  `rankRieszKernel S psi c i j = rho * truncatedRieszKernel R psi c (g i) (g j)`
  off band.
* `bandExcessNonnegLe`, `bandExcessAbsLe`: on band
  (`(2/m) * D < rieszCycleCutoff R`) the excess of the untruncated edge over
  `rho * c * cutoff^(-psi)` is nonnegative (for `0 < c`) and, for arbitrary
  signed `c`, has absolute value at most `|c| * S^psi * D^(-psi)`.
* `rieszCycleBandCardLe`: the band `j ≠ i` with `(2/m) * Nat.dist i j < cutoff`
  contains at most `2 * (m * cutoff + 2)` columns.
* `rankRieszKernelTruncatedComparison`: the combined per-edge comparison with
  the band indicator.
-/

noncomputable section

namespace Hurst

/-! ### Elementary power identities -/

private theorem max_eq_right'' {a b : ℝ} (h : a ≤ b) : max a b = b :=
  le_antisymm (max_le h (le_refl b)) (le_max_right a b)

private theorem max_eq_left'' {a b : ℝ} (h : b ≤ a) : max a b = a :=
  le_antisymm (max_le (le_refl a) h) (le_max_left a b)

/-- Splitting a negative power between two bases: `a ^ x * b ^ (-x) = (a/b)^x`. -/
private theorem rpow_mul_neg_rpow_eq {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a ^ x * b ^ (-x) = (a / b) ^ x := by
  rw [Real.rpow_neg hb.le, Real.div_rpow ha hb.le, div_eq_inv_mul]
  ring

/-- The mesh factorization at the level of a single unit edge: the untruncated
value `S ^ psi * D ^ (-psi)` factors as the mesh correction factor
`(2*S/m)^psi` times the capped-distance value at the mesh distance
`(2/m) * D`. -/
theorem rpowMeshFactor {S psi m D : ℝ} (hS : 0 < S) (hm : 0 < m) (hD : 0 < D) :
    S ^ psi * D ^ (-psi) = (2 * S / m) ^ psi * ((2 / m) * D) ^ (-psi) := by
  have h2SD : 0 < 2 * S / m := div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hS) hm
  have h2mD : 0 < (2 / m) * D := mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) hm) hD
  rw [rpow_mul_neg_rpow_eq hS.le hD, rpow_mul_neg_rpow_eq h2SD.le h2mD]
  congr 1
  field_simp [hD.ne', hm.ne']

/-! ### Deliverable 1: off-band exact equality -/

/-- **Off-band exact equality (scalar form)**: for a unit edge whose mesh
distance `(2/m) * D` exceeds the cutoff, the untruncated scaled edge
`S ^ psi * D ^ (-psi)` equals the mesh correction factor `(2*S/m)^psi` times
the capped value `max (rieszCycleCutoff R) ((2/m)*D) ^ (-psi)`. -/
theorem scaledUnitMeshMaxEq {R : ℕ} {psi S m D : ℝ} (hS : 0 < S) (hm : 0 < m)
    (hD : 0 < D) (hfar : rieszCycleCutoff R ≤ (2 / m) * D) :
    S ^ psi * D ^ (-psi) =
      (2 * S / m) ^ psi *
        (max (rieszCycleCutoff R) ((2 / m) * D)) ^ (-psi) := by
  rw [max_eq_right'' hfar]
  exact rpowMeshFactor hS hm hD

/-- **Off-band exact equality (matrix-entry form)**: away from the cutoff
strip, a `rankRieszKernel` entry equals the mesh correction factor
`(2*S/m)^psi` times the corresponding `truncatedRieszKernel` grid entry. -/
theorem rankRieszKernelEqRhoMulTruncated {m : ℕ} {S psi c : ℝ} {R : ℕ}
    (hS : 0 < S) (hm : 0 < m) (i j : Fin m)
    (hfar : rieszCycleCutoff R ≤
      (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ)) :
    rankRieszKernel S psi c i j =
      (2 * S / (m : ℝ)) ^ psi *
        truncatedRieszKernel R psi c (rieszCycleGridPoint m i)
          (rieszCycleGridPoint m j) := by
  have hD0 : Nat.dist i.val j.val ≠ 0 := by
    intro h
    rw [h] at hfar
    simp only [Nat.cast_zero, mul_zero] at hfar
    linarith [rieszCycleCutoff_pos R]
  have hDpos : 0 < ((Nat.dist i.val j.val : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hD0
  have hgrid : |rieszCycleGridPoint m i - rieszCycleGridPoint m j|
      = (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) := by
    rw [abs_sub_rieszCycleGridPoint_eq]
    ring
  have hkey := scaledUnitMeshMaxEq (R := R) (psi := psi) (m := (m : ℝ))
    (D := ((Nat.dist i.val j.val : ℕ) : ℝ)) hS (by exact_mod_cast hm) hDpos hfar
  unfold rankRieszKernel rankRieszUnitKernel
  rw [if_neg hD0]
  unfold truncatedRieszKernel
  rw [hgrid, mul_assoc, hkey]
  ring

/-! ### Deliverable 2: on-band excess bounds -/

/-- On band the capped distance is the cutoff, so the cutoff value dominates
the mesh-distance value after taking negative powers. -/
theorem bandCutoffRpowLe {R : ℕ} {psi m D : ℝ} (hm : 0 < m) (hD : 0 < D)
    (hpsi : 0 < psi) (hband : (2 / m) * D < rieszCycleCutoff R) :
    (rieszCycleCutoff R) ^ (-psi) ≤ ((2 / m) * D) ^ (-psi) := by
  have h2mD : 0 < (2 / m) * D := mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) hm) hD
  have hcut : 0 < rieszCycleCutoff R := rieszCycleCutoff_pos R
  have hmono : ((2 / m) * D) ^ psi ≤ (rieszCycleCutoff R) ^ psi :=
    Real.rpow_le_rpow h2mD.le hband.le hpsi.le
  rw [Real.rpow_neg hcut.le, Real.rpow_neg h2mD.le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hcut psi)
    (Real.rpow_pos_of_pos h2mD psi)).2 hmono

/-- **On-band excess bound (absolute form, signed `c`)**: with
`rho = (2*S/m)^psi` and `D` the unit edge distance, on band
`|c * S^psi * D^(-psi) - rho * c * cutoff^(-psi)| ≤ |c| * S^psi * D^(-psi)`. -/
theorem bandExcessAbsLe {R : ℕ} {psi S c m D : ℝ} (hS : 0 < S) (hm : 0 < m)
    (hD : 0 < D) (hpsi : 0 < psi)
    (hband : (2 / m) * D < rieszCycleCutoff R) :
    |c * S ^ psi * D ^ (-psi) -
        (2 * S / m) ^ psi * c * (rieszCycleCutoff R) ^ (-psi)|
      ≤ |c| * S ^ psi * D ^ (-psi) := by
  have hf := rpowMeshFactor (psi := psi) hS hm hD
  have hcutoff := bandCutoffRpowLe hm hD hpsi hband
  have hrho : 0 < (2 * S / m) ^ psi :=
    Real.rpow_pos_of_pos (div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hS) hm) psi
  have hdiff : c * S ^ psi * D ^ (-psi) -
      (2 * S / m) ^ psi * c * (rieszCycleCutoff R) ^ (-psi)
      = (2 * S / m) ^ psi * c *
          (((2 / m) * D) ^ (-psi) - (rieszCycleCutoff R) ^ (-psi)) := by
    linear_combination c * hf
  rw [hdiff, abs_mul, abs_mul, abs_of_nonneg hrho.le,
    abs_of_nonneg (sub_nonneg.mpr hcutoff), mul_assoc]
  calc (2 * S / m) ^ psi * (|c| *
        (((2 / m) * D) ^ (-psi) - (rieszCycleCutoff R) ^ (-psi)))
      ≤ (2 * S / m) ^ psi * (|c| * ((2 / m) * D) ^ (-psi)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by
            linarith [Real.rpow_nonneg (le_of_lt (rieszCycleCutoff_pos R)) (-psi)])
            (abs_nonneg c)) hrho.le
    _ = |c| * ((2 * S / m) ^ psi * ((2 / m) * D) ^ (-psi)) := by ring
    _ = |c| * S ^ psi * D ^ (-psi) := by linear_combination |c| * hf.symm

/-- **On-band excess bound (signed form, `0 < c`)**: on band the excess of the
untruncated edge over the mesh-scaled truncated edge is nonnegative and at
most the untruncated edge itself. -/
theorem bandExcessNonnegLe {R : ℕ} {psi S c m D : ℝ} (hS : 0 < S) (hm : 0 < m)
    (hD : 0 < D) (hpsi : 0 < psi) (hc : 0 < c)
    (hband : (2 / m) * D < rieszCycleCutoff R) :
    0 ≤ c * S ^ psi * D ^ (-psi) -
        (2 * S / m) ^ psi * c * (rieszCycleCutoff R) ^ (-psi) ∧
      c * S ^ psi * D ^ (-psi) -
        (2 * S / m) ^ psi * c * (rieszCycleCutoff R) ^ (-psi)
          ≤ c * S ^ psi * D ^ (-psi) := by
  have hf := rpowMeshFactor (psi := psi) hS hm hD
  have hcutoff := bandCutoffRpowLe hm hD hpsi hband
  have hrho : 0 < (2 * S / m) ^ psi :=
    Real.rpow_pos_of_pos (div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hS) hm) psi
  have hB : (2 * S / m) ^ psi * c * (rieszCycleCutoff R) ^ (-psi)
      ≤ c * S ^ psi * D ^ (-psi) := by
    calc (2 * S / m) ^ psi * c * (rieszCycleCutoff R) ^ (-psi)
        = ((2 * S / m) ^ psi * c) * (rieszCycleCutoff R) ^ (-psi) := rfl
      _ ≤ ((2 * S / m) ^ psi * c) * ((2 / m) * D) ^ (-psi) :=
          mul_le_mul_of_nonneg_left hcutoff (mul_nonneg hrho.le hc.le)
      _ = c * ((2 * S / m) ^ psi * ((2 / m) * D) ^ (-psi)) := by ring
      _ = c * S ^ psi * D ^ (-psi) := by linear_combination c * hf.symm
  refine ⟨sub_nonneg.mpr hB, ?_⟩
  have hBnn : 0 ≤ (2 * S / m) ^ psi * c * (rieszCycleCutoff R) ^ (-psi) := by
    rw [mul_assoc]
    exact mul_nonneg hrho.le
      (mul_nonneg hc.le (Real.rpow_nonneg (le_of_lt (rieszCycleCutoff_pos R)) _))
  linarith

/-! ### Deliverable 3: band count -/

/-- **Band count**: for a fixed row `i` and cutoff `> 0`, the off-diagonal
band `{j : j ≠ i ∧ (2/m) * Nat.dist i j < cutoff}` contains at most
`2 * (m * cutoff + 2)` columns: each admissible integer distance `d` occurs
for at most the two columns `i ± d`, and `d < m * cutoff / 2`. -/
theorem rieszCycleBandCardLe (m : ℕ) (i : Fin m) (cutoff : ℝ) (hcut : 0 < cutoff) :
    (Finset.univ.filter (fun j : Fin m => j ≠ i ∧
      (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) < cutoff)).card
      ≤ 2 * ((m : ℝ) * cutoff + 2) := by
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) i.isLt
  set B : ℝ := (m : ℝ) * cutoff / 2 with hBdef
  have hBpos : 0 < B := div_pos (mul_pos hm hcut) (by norm_num : (0 : ℝ) < 2)
  have hKle : ((Nat.ceil B : ℕ) : ℝ) ≤ B + 1 := by
    have h1 : Nat.ceil B ≤ Nat.floor B + 1 := Nat.ceil_le_floor_add_one B
    have h2 : ((Nat.ceil B : ℕ) : ℝ) ≤ (Nat.floor B : ℝ) + 1 := by
      exact_mod_cast h1
    have h3 : ((Nat.floor B : ℕ) : ℝ) ≤ B := Nat.floor_le hBpos.le
    linarith
  have hmeshof : ∀ d : ℕ, (2 : ℝ) / (m : ℝ) * ((d : ℕ) : ℝ) < cutoff →
      ((d : ℕ) : ℝ) < B := by
    intro d hd
    rw [div_mul_eq_mul_div, div_lt_iff₀ hm] at hd
    rw [hBdef, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [mul_comm (2 : ℝ) (d : ℕ), mul_comm (m : ℝ) cutoff]
  set s : Finset (Fin m) := Finset.univ.filter
    (fun j : Fin m => j ≠ i ∧
      (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) < cutoff) with hsdef
  set f : Fin m → ℕ × Bool :=
    fun j => (Nat.dist i.val j.val, decide (j.val ≤ i.val)) with hfdef
  have hinj : Set.InjOn f (s : Set (Fin m)) := by
    intro a ha b hb hab
    simp only [hsdef, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    simp only [hfdef, Prod.mk.injEq] at hab
    obtain ⟨hdab, hsgn⟩ := hab
    have hsign : (a.val ≤ i.val) ↔ (b.val ≤ i.val) := by
      by_cases h : a.val ≤ i.val
      · have ht : decide (b.val ≤ i.val) = true := by rw [← hsgn]; simp [h]
        simpa [h] using ht
      · have hf' : decide (b.val ≤ i.val) = false := by rw [← hsgn]; simp [h]
        simpa [h] using hf'
    by_cases hale : a.val ≤ i.val
    · have hble : b.val ≤ i.val := hsign.mp hale
      have h1 : Nat.dist i.val a.val = i.val - a.val := by
        rw [Nat.dist_comm]
        exact Nat.dist_eq_sub_of_le hale
      have h2 : Nat.dist i.val b.val = i.val - b.val := by
        rw [Nat.dist_comm]
        exact Nat.dist_eq_sub_of_le hble
      rw [h1, h2] at hdab
      exact Fin.val_injective (by omega)
    · have hbgt : i.val < b.val := by
        have hnb := hsign.not.mp hale
        omega
      have h1 : Nat.dist i.val a.val = a.val - i.val :=
        Nat.dist_eq_sub_of_le (by omega)
      have h2 : Nat.dist i.val b.val = b.val - i.val :=
        Nat.dist_eq_sub_of_le (by omega)
      rw [h1, h2] at hdab
      exact Fin.val_injective (by omega)
  have hsub : s.image f ⊆
      Finset.range (Nat.ceil B) ×ˢ (Finset.univ : Finset Bool) := by
    rintro ⟨d, b⟩ hjmem
    obtain ⟨j, hj, hjfb⟩ := Finset.mem_image.mp hjmem
    simp only [hfdef, Prod.mk.injEq] at hjfb
    obtain ⟨rfl, rfl⟩ := hjfb
    simp only [hsdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_univ _⟩
    exact Nat.lt_ceil.2 (hmeshof _ hj.2)
  have hcard1 : s.card ≤ 2 * Nat.ceil B := by
    refine le_trans (Finset.card_image_of_injOn hinj).symm.le
      (le_trans (Finset.card_le_card hsub) ?_)
    rw [Finset.card_product, Finset.card_range, Finset.card_univ]
    simp
    omega
  have hfinal : ((s.card : ℕ) : ℝ) ≤ 2 * ((m : ℝ) * cutoff + 2) := by
    have e1 : ((s.card : ℕ) : ℝ) ≤ (2 : ℝ) * ((Nat.ceil B : ℕ) : ℝ) := by
      exact_mod_cast hcard1
    linarith
  exact_mod_cast hfinal

/-! ### Deliverable 4: combined per-edge comparison with band indicator -/

/-- **Combined per-edge comparison**: for `D = Nat.dist i.val j.val ≥ 1` and
`rho = (2*S/m)^psi`, the untruncated edge and `rho` times the truncated grid
edge differ (in absolute value) by at most `|c| * S^psi * D^(-psi)` times the
band indicator: off band the difference vanishes exactly (Deliverable 1), on
band the excess is controlled (Deliverable 2). -/
theorem rankRieszKernelTruncatedComparison {m : ℕ} {S psi c : ℝ} {R : ℕ}
    (hS : 0 < S) (hm : 0 < m) (hpsi : 0 < psi) (i j : Fin m)
    (hD : 1 ≤ Nat.dist i.val j.val) :
    |rankRieszKernel S psi c i j -
        (2 * S / (m : ℝ)) ^ psi *
          truncatedRieszKernel R psi c (rieszCycleGridPoint m i)
            (rieszCycleGridPoint m j)|
      ≤ |c| * S ^ psi * ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi) *
          (if (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) <
              rieszCycleCutoff R then (1 : ℝ) else 0) := by
  have hD0 : Nat.dist i.val j.val ≠ 0 := ne_of_gt hD
  have hDpos : 0 < ((Nat.dist i.val j.val : ℕ) : ℝ) := by exact_mod_cast hD
  have hgrid : |rieszCycleGridPoint m i - rieszCycleGridPoint m j|
      = (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) := by
    rw [abs_sub_rieszCycleGridPoint_eq]
    ring
  by_cases hband : (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) <
      rieszCycleCutoff R
  · -- On band: the truncated entry is `c * cutoff^(-psi)` and Deliverable 2 applies.
    have key := bandExcessAbsLe (R := R) (m := (m : ℝ))
      (D := ((Nat.dist i.val j.val : ℕ) : ℝ)) (c := c) hS
      (by exact_mod_cast hm) hDpos hpsi hband
    have hrk : rankRieszKernel S psi c i j
        = c * S ^ psi * ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi) := by
      unfold rankRieszKernel rankRieszUnitKernel
      rw [if_neg hD0]
    have htr : truncatedRieszKernel R psi c (rieszCycleGridPoint m i)
        (rieszCycleGridPoint m j) = c * (rieszCycleCutoff R) ^ (-psi) := by
      unfold truncatedRieszKernel
      rw [hgrid, max_eq_left'' hband.le]
    rw [hrk, htr, if_pos hband, mul_one]
    have hrearr : c * S ^ psi * ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi)
        - (2 * S / (m : ℝ)) ^ psi * (c * (rieszCycleCutoff R) ^ (-psi))
        = c * S ^ psi * ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi)
        - (2 * S / (m : ℝ)) ^ psi * c * (rieszCycleCutoff R) ^ (-psi) := by
      ring
    rw [hrearr]
    exact key
  · -- Off band: the difference vanishes exactly (Deliverable 1).
    have hfar : rieszCycleCutoff R ≤
        (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) := not_lt.mp hband
    have hzero := rankRieszKernelEqRhoMulTruncated (R := R) (psi := psi)
      (c := c) hS hm i j hfar
    rw [hzero, sub_self, abs_zero, if_neg hband]
    positivity

end Hurst
