import Hurst.BandRemovalSharp
import Hurst.BandPowerSum

/-!
# Complete assembly: uniform discrete Riesz cutoff removal

This file completes the assembly of `Hurst.HasUniformDiscreteRieszCutoffRemoval`
along the route prepared in `Hurst.BandRemovalSharp` (cyclic trace engine) and
`Hurst.BandRemovalAssembly` (mesh-difference matrix), combining the sharp
weighted band power-sums of `Hurst.BandPowerSum`:

* `abs_rieszCycleGridPoint_dist`: the grid distance is exactly
  `(2/m) * Nat.dist i j`, which turns the capped kernel into a function of the
  row distance and unlocks the row-distance stratification `sum_row_dist_le`.
* `abs_rieszMeshDiffMatrix_diag_le`: the diagonal of the mesh-difference matrix
  is the mesh correction `meshRho * (S⁻¹ * B_omega * |c| * cutoff^(-psi))` (the
  untruncated kernel vanishes on the diagonal, the truncated one is the cap).
* `frobenius_rieszMeshDiff_le` (for `2 ≤ m * cutoff`): the sharp cutoff decay
  `‖Dg‖_F ≤ B_omega*|c|*((√m/S)*rho*cutoff^(-psi)
    + √2*(1-2psi)^(-1/2)*(m/S)^(1-psi)*cutoff^((1-2psi)/2))`,
  the band part decaying in the cutoff via the sharp power sum at `β = 2ψ` over
  the band `d < m*cutoff/2`, and the diagonal part dying with `√m/S → 0`.
* `frobenius_truncated_le`:
  `‖T‖_F ≤ B_omega*|c|*(√2*(√m/S)*cutoff^(-ψ)
    + √2*2^(-ψ)*(1-2ψ)^(-1/2)*(m/S))`,
  bounded in `n` (the `(√m/S)`-pieces die with `√m/S → 0`; the `(m/S)`-piece is
  uniformly bounded).  Documented deviation from the originally sketched
  `√2*(m/S)*cutoff^(1/2-ψ)` decay: the true per-row sum
  `∑_d (max cutoff (2d/m))^(-2ψ)` converges to `m * 2^(-2ψ)/(1-2ψ)` as
  `cutoff → 0` (the capped strip shrinks but the uncapped tail `∑ d^(-2ψ)` over
  `[m*cutoff/2, m)` stays `≈ m/(2^{2ψ}(1-2ψ))`), so no cutoff decay of the
  `(m/S)`-piece holds.  Boundedness in `n` is exactly what the ε-assembly
  needs: the bracket `‖Dg‖ + rho*‖T‖` stays bounded by an explicit
  `n`-independent constant while `‖Dg‖ → 0` in the cutoff.
* `hasUniformDiscreteRieszCutoffRemoval`: the full uniform removal, from the
  ordinary hypotheses `m n → ∞`, `m n / S n → 2`, eventually positive `S n, m n`,
  `0 < psi < 1/2`, and `|omega| ≤ B_omega` on `[-1,1]`, via
  `abs_cycleValue_diff_le_cyclic` and `tendsto_mesh_correction_rpow`.
-/

noncomputable section

open Set Filter Matrix
open scoped Matrix.Norms.Frobenius Topology

namespace Hurst

/-! ### Small helpers -/

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
private theorem sqrt_add_le_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h2 : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have e1 : Real.sqrt a ^ 2 = a := by rw [pow_two, Real.mul_self_sqrt ha]
  have e2 : Real.sqrt b ^ 2 = b := by rw [pow_two, Real.mul_self_sqrt hb]
  have hs : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have hnn : 0 ≤ Real.sqrt a * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    have hsq := sq_nonneg (Real.sqrt a + Real.sqrt b)
    rw [add_sq, e1, e2] at hsq
    linarith
  have h := Real.sqrt_le_sqrt hs
  rwa [Real.sqrt_sq h2] at h

/-- The grid distance is exactly `(2/m) * Nat.dist i j`. -/
theorem abs_rieszCycleGridPoint_dist (m : ℕ) (hm : 0 < m) (i j : Fin m) :
    |rieszCycleGridPoint m i - rieszCycleGridPoint m j|
      = (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) := by
  have h1 : rieszCycleGridPoint m i - rieszCycleGridPoint m j
      = (2 : ℝ) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) / (m : ℝ) := by
    unfold rieszCycleGridPoint
    push_cast
    ring
  rw [h1, abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
    abs_of_pos (show (0 : ℝ) < (m : ℝ) by exact_mod_cast hm)]
  by_cases hij : i.val ≤ j.val
  · have hde' : Nat.dist i.val j.val = j.val - i.val := by
      have hde : Nat.dist i.val j.val = (i.val - j.val) + (j.val - i.val) := rfl
      omega
    rw [abs_of_nonpos (sub_nonpos.2 (by exact_mod_cast hij)), hde',
      Nat.cast_sub hij]
    push_cast
    ring
  · have hji : j.val ≤ i.val := by omega
    have hde' : Nat.dist i.val j.val = i.val - j.val := by
      have hde : Nat.dist i.val j.val = (i.val - j.val) + (j.val - i.val) := rfl
      omega
    rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hji)), hde',
      Nat.cast_sub hji]
    push_cast
    ring

/-- The diagonal of the mesh-difference matrix: the untruncated kernel
vanishes there and the truncated one equals the cap, so the entry is at most
the mesh-correction scale `meshRho * (S⁻¹ * B_omega * |c| * cutoff^(-ψ))`. -/
theorem abs_rieszMeshDiffMatrix_diag_le {m R : ℕ} {S psi c B_omega : ℝ}
    (hS : 0 < S) (hm : 0 < m) (omega : ℝ → ℝ)
    (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (i : Fin m) :
    |rieszMeshDiffMatrix m R S psi c omega i i|
      ≤ meshRho m S psi * ((S : ℝ)⁻¹ * B_omega * |c| * (rieszCycleCutoff R) ^ (-psi)) := by
  have hcut : 0 < rieszCycleCutoff R := rieszCycleCutoff_pos R
  have hrho0 : 0 ≤ meshRho m S psi := by
    unfold meshRho
    exact Real.rpow_nonneg (by positivity) psi
  have hunit : rankRieszUnitKernel psi i i = 0 := by
    unfold rankRieszUnitKernel
    simp
  have hkr : rankRieszKernel S psi c i i = 0 := by
    unfold rankRieszKernel
    rw [hunit, mul_zero]
  have htr : truncatedRieszKernel R psi c (rieszCycleGridPoint m i)
        (rieszCycleGridPoint m i)
      = c * (rieszCycleCutoff R) ^ (-psi) := by
    unfold truncatedRieszKernel
    rw [sub_self, abs_zero, max_eq_left hcut.le]
  have hgi : rieszCycleGridPoint m i ∈ Icc (-1 : ℝ) 1 := rieszCycleGridPoint_mem_Icc hm i
  have hw : |omega (rieszCycleGridPoint m i)| ≤ B_omega := homegaB _ hgi
  have hB0 : 0 ≤ B_omega := by linarith [abs_nonneg (omega (rieszCycleGridPoint m i))]
  have hrpow : 0 ≤ (rieszCycleCutoff R) ^ (-psi) := Real.rpow_nonneg hcut.le (-psi)
  rw [rieszMeshDiffMatrix_apply, hkr, htr, zero_sub, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hS.le), abs_neg, abs_mul, abs_of_nonneg hrho0,
    abs_mul, abs_of_nonneg hrpow]
  have hstep1 : |omega (rieszCycleGridPoint m i)| * (meshRho m S psi
        * (|c| * (rieszCycleCutoff R) ^ (-psi)))
      ≤ B_omega * (meshRho m S psi * (|c| * (rieszCycleCutoff R) ^ (-psi))) :=
    mul_le_mul_of_nonneg_right hw (mul_nonneg hrho0 (mul_nonneg (abs_nonneg c) hrpow))
  have hstep2 : (S : ℝ)⁻¹ * (|omega (rieszCycleGridPoint m i)| * (meshRho m S psi
        * (|c| * (rieszCycleCutoff R) ^ (-psi))))
      ≤ (S : ℝ)⁻¹ * (B_omega * (meshRho m S psi * (|c| * (rieszCycleCutoff R) ^ (-psi)))) :=
    mul_le_mul_of_nonneg_left hstep1 (inv_nonneg.2 hS.le)
  exact le_trans (le_of_eq (by ring)) (le_trans hstep2 (le_of_eq (by field_simp)))

/-! ### Step 1: the sharp cutoff-decaying bound for the mesh-difference matrix -/

set_option maxHeartbeats 1000000 in
theorem frobenius_rieszMeshDiff_le (m R : ℕ) (S psi c B_omega : ℝ)
    (hS : 0 < S) (hm : 0 < m) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (omega : ℝ → ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (hcut2 : 2 ≤ (m : ℝ) * rieszCycleCutoff R) :
    ‖rieszMeshDiffMatrix m R S psi c omega‖
      ≤ (B_omega * |c|) * ((Real.sqrt (m : ℝ) / S)
            * (meshRho m S psi) * (rieszCycleCutoff R) ^ (-psi)
          + Real.sqrt 2 * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ)))
            * (((m : ℝ) / S) ^ (1 - psi))
            * (rieszCycleCutoff R) ^ ((1 - 2 * psi) / 2)) := by
  classical
  have hS0 : (S : ℝ) ≠ 0 := ne_of_gt hS
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set cc : ℝ := rieszCycleCutoff R with hccdef
  have hcc : 0 < cc := rieszCycleCutoff_pos R
  set rho : ℝ := meshRho m S psi with hrhodef
  have hrho0 : 0 ≤ rho := by
    rw [hrhodef]
    exact Real.rpow_nonneg (by positivity) psi
  set BC : ℝ := B_omega * |c| with hBCdef
  have hB0 : 0 ≤ B_omega := by
    have hb := homegaB 0 (Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩)
    linarith [abs_nonneg (omega 0)]
  have hBC0 : 0 ≤ BC := mul_nonneg hB0 (abs_nonneg c)
  set a : ℝ := rho * ((S : ℝ)⁻¹ * B_omega * |c| * cc ^ (-psi)) with hadef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    refine mul_nonneg hrho0 (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) hB0)
      (abs_nonneg c)) (Real.rpow_nonneg hcc.le (-psi)))
  set bb : ℝ := ((S : ℝ)⁻¹ * B_omega * |c|) * S ^ psi with hbbdef
  have hbb0 : 0 ≤ bb := by
    rw [hbbdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) hB0)
      (abs_nonneg c)) (Real.rpow_nonneg hS.le psi)
  set fb : ℕ → ℝ := fun d => if (2 : ℝ) / (m : ℝ) * ((d : ℝ)) < cc then
    ((d : ℝ)) ^ (-(2 * psi)) else 0 with hfbdef
  have hfbnn : ∀ d : ℕ, 0 ≤ fb d := by
    intro d
    simp only [hfbdef]
    split_ifs with h
    · exact Real.rpow_nonneg (Nat.cast_nonneg d) (-(2 * psi))
    · exact le_refl 0
  -- power bridges
  have htwo : ∀ x : ℝ, x ^ ((2 : ℝ)) = x ^ 2 := Real.rpow_two
  have hsqrw : ∀ (x : ℝ), 0 < x → (x ^ (-psi)) ^ 2 = x ^ (-(2 * psi)) := by
    intro x hx
    rw [pow_two, ← Real.rpow_add hx (-(psi : ℝ)) (-(psi : ℝ)),
      show (-(psi : ℝ) + -(psi : ℝ)) = -(2 * psi) from by ring]
  have hmul2 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x * y) ^ ((2 : ℝ)) = x ^ 2 * y ^ 2 := by
    intro x y hx hy
    rw [Real.mul_rpow hx hy, htwo, htwo]
  -- per-entry bounds: `a` on the diagonal, `bb * d^(-psi)` off the diagonal
  have hdiagEntry : ∀ i : Fin m, ‖rieszMeshDiffMatrix m R S psi c omega i i‖ ^ ((2 : ℝ))
      ≤ a ^ 2 := by
    intro i
    rw [Real.norm_eq_abs, ← htwo a]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    exact abs_rieszMeshDiffMatrix_diag_le hS hm omega homegaB i
  have hoffEntry : ∀ (i j : Fin m), j ≠ i →
      ‖rieszMeshDiffMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
      ≤ bb ^ 2 * fb (Nat.dist i.val j.val) := by
    intro i j hjne
    have hd1 : 1 ≤ Nat.dist i.val j.val := by
      have hne : Nat.dist i.val j.val ≠ 0 := by
        intro h
        apply hjne
        ext
        have hdd : Nat.dist i.val j.val = (i.val - j.val) + (j.val - i.val) := rfl
        rw [h] at hdd
        omega
      exact Nat.one_le_iff_ne_zero.mpr hne
    have hd0 : (0 : ℝ) < ((Nat.dist i.val j.val : ℕ) : ℝ) := by exact_mod_cast hd1
    by_cases hbandm : (2 : ℝ) / (m : ℝ) * (((Nat.dist i.val j.val : ℕ) : ℝ)) < cc
    · have hb : |rieszMeshDiffMatrix m R S psi c omega i j|
          ≤ ((S : ℝ)⁻¹ * B_omega * |c|) * S ^ psi
            * (((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi)) :=
      abs_rieszMeshDiffMatrix_le_of_dist' hS hpsi1 hm omega homegaB i j hd1
      have hbbd : bb * (((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi))
          = ((S : ℝ)⁻¹ * B_omega * |c|) * S ^ psi
            * (((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi)) := by rw [hbbdef]
      have h1 : |rieszMeshDiffMatrix m R S psi c omega i j| ^ ((2 : ℝ))
          ≤ (bb * (((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi))) ^ ((2 : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hb (by norm_num)
      refine le_trans h1 ?_
      have hfb : fb (Nat.dist i.val j.val)
          = ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-(2 * psi)) := by
        rw [hfbdef]
        exact if_pos hbandm
      rw [hmul2 bb _ hbb0 (Real.rpow_nonneg hd0.le (-psi)), hsqrw _ hd0, hfb]
    · have hz : rieszMeshDiffMatrix m R S psi c omega i j = 0 :=
        rieszMeshDiffMatrix_apply_of_not_band hS hm omega i j
          hd1 (le_of_not_gt hbandm)
      rw [hz, Real.norm_eq_abs, abs_zero, Real.zero_rpow (by norm_num : ((2 : ℝ)) ≠ 0)]
      have hfbn : 0 ≤ bb ^ 2 * fb (Nat.dist i.val j.val) :=
        mul_nonneg (sq_nonneg bb) (hfbnn _)
      linarith
  -- row stratification and the sharp band power sum through the ceiling
  set D : ℕ := Nat.ceil ((m : ℝ) * cc / 2) with hDdef
  have hDlt : ((D : ℝ)) < (m : ℝ) * cc := by
    have h2p : (0 : ℝ) < 2 := by norm_num
    have hge : (1 : ℝ) ≤ (m : ℝ) * cc / 2 := by
      rw [le_div_iff₀ h2p]
      exact_mod_cast hcut2
    have h21 : (2 : ℝ)⁻¹ < (m : ℝ) * cc / 2 := by
      have : (2 : ℝ)⁻¹ < 1 := by norm_num
      linarith
    have ht := Nat.ceil_lt_two_mul (K := ℝ) (a := (m : ℝ) * cc / 2) h21
    rwa [show (2 : ℝ) * ((m : ℝ) * cc / 2) = (m : ℝ) * cc from by ring] at ht
  have hbandD : ∀ d : ℕ, (2 : ℝ) / (m : ℝ) * ((d : ℝ)) < cc → d < D := by
    intro d hd
    refine Nat.lt_ceil.mpr ?_
    have hpos : (0 : ℝ) < (m : ℝ) / 2 := by positivity
    have h1 := mul_lt_mul_of_pos_left hd hpos
    have h2' : (m : ℝ) / 2 * ((2 : ℝ) / (m : ℝ) * ((d : ℝ))) = ((d : ℝ)) := by
      field_simp
    have h3 : (m : ℝ) / 2 * cc = (m : ℝ) * cc / 2 := by ring
    rwa [h2', h3] at h1
  have hsumband : ∑ d ∈ Finset.range m, fb d
      ≤ ((m : ℝ) * cc) ^ ((1 : ℝ) - 2 * psi) / (1 - 2 * psi) := by
    have h1 : ∑ d ∈ Finset.range m, fb d
        = ∑ d ∈ (Finset.range m).filter
            (fun d : ℕ => (2 : ℝ) / (m : ℝ) * ((d : ℝ)) < cc),
            ((d : ℝ)) ^ (-(2 * psi)) := by
      simp only [hfbdef]
      exact (Finset.sum_filter _ _).symm
    have h2' : ∑ d ∈ Finset.range D, ((d : ℝ)) ^ (-(2 * psi))
        ≤ ((D : ℝ)) ^ ((1 : ℝ) - 2 * psi) / (1 - 2 * psi) :=
      sum_range_rpow_neg_shift_le (show (0 : ℝ) < 2 * psi from by linarith) hpsi2 D
    have h3 : ((D : ℝ)) ^ ((1 : ℝ) - 2 * psi)
        ≤ ((m : ℝ) * cc) ^ ((1 : ℝ) - 2 * psi) :=
      Real.rpow_le_rpow (Nat.cast_nonneg D) hDlt.le (by linarith)
    rw [h1]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg d) (-(2 * psi)))) (le_trans h2' ?_)
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd
      exact Finset.mem_range.mpr (hbandD d hd.2)
    · have hdnn : 0 ≤ ((D : ℝ)) ^ ((1 : ℝ) - 2 * psi) :=
        Real.rpow_nonneg (Nat.cast_nonneg D) ((1 : ℝ) - 2 * psi)
      have hcnn : 0 ≤ ((m : ℝ) * cc) ^ ((1 : ℝ) - 2 * psi) :=
        Real.rpow_nonneg (mul_nonneg hmR.le hcc.le) ((1 : ℝ) - 2 * psi)
      have hpos' : 0 < (1 - 2 * psi : ℝ) := by linarith
      refine (div_le_div_iff₀ hpos' hpos').mpr ?_
      exact mul_le_mul_of_nonneg_right h3 (by linarith)
  set Ssum : ℝ := ∑ d ∈ Finset.range m, fb d with hSsumdef
  -- assemble the Frobenius norm
  have hrow : ∀ i : Fin m, ∑ j : Fin m,
      ‖rieszMeshDiffMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
      ≤ a ^ 2 + 2 * bb ^ 2 * Ssum := by
    classical
    intro i
    have h1 : ∑ j : Fin m, fb ((i : ℕ).dist (j : ℕ)) ≤ 2 * Ssum :=
      sum_row_dist_le fb hfbnn i
    have hsplit : ∑ j : Fin m, ‖rieszMeshDiffMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
        = ‖rieszMeshDiffMatrix m R S psi c omega i i‖ ^ ((2 : ℝ))
          + ∑ j ∈ Finset.univ.erase i,
            ‖rieszMeshDiffMatrix m R S psi c omega i j‖ ^ ((2 : ℝ)) := by
      classical
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
      ring
    have hrest : ∑ j ∈ Finset.univ.erase i,
        ‖rieszMeshDiffMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
        ≤ bb ^ 2 * ∑ j : Fin m, fb ((i : ℕ).dist (j : ℕ)) := by
      have hA : ∑ j ∈ Finset.univ.erase i,
          ‖rieszMeshDiffMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
          ≤ ∑ j ∈ Finset.univ.erase i, (bb ^ 2 * fb ((i : ℕ).dist (j : ℕ))) :=
        Finset.sum_le_sum (fun j hj => hoffEntry i j (fun h => (Finset.mem_erase.mp hj).1 h))
      have hB : ∑ j ∈ Finset.univ.erase i, (bb ^ 2 * fb ((i : ℕ).dist (j : ℕ)))
          ≤ bb ^ 2 * ∑ j : Fin m, fb ((i : ℕ).dist (j : ℕ)) := by
        rw [Finset.mul_sum (Finset.univ) (fun j : Fin m => fb ((i : ℕ).dist (j : ℕ)))
          (bb ^ 2)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => mul_nonneg (sq_nonneg bb) (hfbnn (Nat.dist i.val j.val)))
      exact le_trans hA hB
    rw [hsplit]
    have h3 : bb ^ 2 * ∑ j : Fin m, fb ((i : ℕ).dist (j : ℕ)) ≤ 2 * bb ^ 2 * Ssum := by
      have h3' := mul_le_mul_of_nonneg_left h1 (sq_nonneg bb)
      have hcomm : bb ^ 2 * (2 * Ssum) = 2 * bb ^ 2 * Ssum := by ring
      rwa [hcomm] at h3'
    have hd := hdiagEntry i
    linarith [hrest, h3, hd]
  have hsqsum : ∑ i : Fin m, ∑ j : Fin m,
      ‖rieszMeshDiffMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
      ≤ (m : ℝ) * (a ^ 2 + 2 * bb ^ 2 * Ssum) := by
    refine le_trans (Finset.sum_le_sum (fun i _ => hrow i)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Matrix.frobenius_norm_def]
  refine le_trans (Real.rpow_le_rpow (by positivity) hsqsum (by norm_num)) ?_
  rw [← Real.sqrt_eq_rpow]
  have hP1 : Real.sqrt ((m : ℝ) * a ^ 2)
      ≤ BC * ((Real.sqrt ((m : ℝ)) / S) * rho * cc ^ (-psi)) := by
    have he : Real.sqrt ((m : ℝ) * a ^ 2)
        = BC * ((Real.sqrt ((m : ℝ)) / S) * rho * cc ^ (-psi)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (m : ℝ)) (a ^ 2), Real.sqrt_sq ha0,
        hadef, hBCdef, hrhodef]
      unfold meshRho
      field_simp
    rw [he]
  have hP2 : Real.sqrt ((m : ℝ) * (2 * bb ^ 2 * Ssum))
      ≤ BC * (Real.sqrt 2 * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ)))
        * (((m : ℝ) / S) ^ ((1 : ℝ) - psi)) * cc ^ (((1 : ℝ) - 2 * psi) / 2)) := by
    have hsqrtband : Real.sqrt Ssum
        ≤ ((m : ℝ) * cc) ^ (((1 : ℝ) - 2 * psi) / 2)
          * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ))) := by
      have hsum' : Ssum ≤ ((1 - 2 * psi) ^ ((-1 : ℝ)))
          * (((m : ℝ) * cc) ^ ((1 : ℝ) - 2 * psi)) := by
        have h := hsumband
        rw [div_eq_inv_mul] at h
        rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ (1 - 2 * psi : ℝ)) 1, Real.rpow_one]
        exact h
      have hsq1 : (((m : ℝ) * cc) ^ (((1 : ℝ) - 2 * psi) / 2)) ^ 2
          = ((m : ℝ) * cc) ^ ((1 : ℝ) - 2 * psi) := by
        rw [pow_two, ← Real.rpow_add (by positivity) (((1 : ℝ) - 2 * psi) / 2)
          (((1 : ℝ) - 2 * psi) / 2),
          show (((1 : ℝ) - 2 * psi) / 2 + ((1 : ℝ) - 2 * psi) / 2) = ((1 : ℝ) - 2 * psi)
            from by ring]
      have hsq2 : (((1 - 2 * psi : ℝ)) ^ (-(1 / 2 : ℝ))) ^ 2
          = ((1 - 2 * psi : ℝ)) ^ ((-1 : ℝ)) := by
        rw [pow_two, ← Real.rpow_add (by linarith : (0 : ℝ) < (1 - 2 * psi : ℝ))
          (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ)),
          show (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) = (-1 : ℝ) from by ring]
      refine le_trans (Real.sqrt_le_sqrt hsum') ?_
      rw [Real.sqrt_mul (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (1 - 2 * psi : ℝ))
        ((-1 : ℝ))) _, ← hsq2, Real.sqrt_sq (Real.rpow_nonneg (by linarith)
        (-(1 / 2 : ℝ))), ← hsq1,
        Real.sqrt_sq (Real.rpow_nonneg (mul_nonneg hmR.le hcc.le) _), mul_comm]
    have hsplit : Real.sqrt ((m : ℝ) * (2 * bb ^ 2 * Ssum))
        = Real.sqrt ((m : ℝ)) * (Real.sqrt 2 * (bb * Real.sqrt Ssum)) := by
      rw [Real.sqrt_mul hmR.le, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * bb ^ 2) Ssum,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (bb ^ 2), Real.sqrt_sq hbb0]
      ring
    have hstep : Real.sqrt 2 * (bb * Real.sqrt Ssum)
        ≤ Real.sqrt 2 * (bb * (((m : ℝ) * cc) ^ (((1 : ℝ) - 2 * psi) / 2)
          * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrtband hbb0)
        (by positivity : (0 : ℝ) ≤ Real.sqrt 2)
    refine le_trans (le_of_eq hsplit) (le_trans (mul_le_mul_of_nonneg (le_refl (Real.sqrt (m : ℝ))) hstep
      (Real.sqrt_nonneg (m : ℝ))
      (mul_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2)
        (mul_nonneg hbb0 (mul_nonneg (Real.rpow_nonneg (mul_nonneg hmR.le hcc.le) _)
          (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (1 - 2 * psi : ℝ))
            (-(1 / 2 : ℝ))))))) ?_)
    · -- monomial comparison over common atoms
      have e1 : ((m : ℝ) * cc) ^ (((1 : ℝ) - 2 * psi) / 2)
          = ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2) * (cc ^ (((1 : ℝ) - 2 * psi) / 2)) :=
        Real.mul_rpow hmR.le hcc.le
      have e2 : Real.sqrt ((m : ℝ)) = ((m : ℝ)) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      have e3 : ((m : ℝ)) ^ ((1 : ℝ) / 2) * ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2)
          = ((m : ℝ)) ^ ((1 : ℝ) - psi) := by
        rw [← Real.rpow_add hmR ((1 : ℝ) / 2) (((1 : ℝ) - 2 * psi) / 2),
          show ((1 : ℝ) / 2 + ((1 : ℝ) - 2 * psi) / 2) = ((1 : ℝ) - psi) from by ring]
      have e5 : (S : ℝ)⁻¹ * (S : ℝ) ^ psi = (S : ℝ) ^ (psi - 1) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hS (-(1 : ℝ)) psi,
          show ((-(1 : ℝ)) + psi) = psi - 1 from by ring]
      have e4 : ((m : ℝ) / S) ^ ((1 : ℝ) - psi)
          = ((m : ℝ)) ^ ((1 : ℝ) - psi) * (S : ℝ) ^ (psi - 1) := by
        rw [Real.div_rpow hmR.le hS.le, div_eq_inv_mul,
          ← Real.rpow_neg hS.le ((1 : ℝ) - psi), mul_comm]
        congr 1
        ring
      rw [e1, e2, e4, ← e3, ← e5, hbbdef, hBCdef]
      ring_nf
      first
        | exact le_refl _
        | exact le_rfl
        | ring
  calc Real.sqrt ((m : ℝ) * (a ^ 2 + 2 * bb ^ 2 * Ssum))
      = Real.sqrt ((m : ℝ) * a ^ 2 + (m : ℝ) * (2 * bb ^ 2 * Ssum)) := by rw [mul_add]
    _ ≤ Real.sqrt ((m : ℝ) * a ^ 2) + Real.sqrt ((m : ℝ) * (2 * bb ^ 2 * Ssum)) :=
        sqrt_add_le_sqrt_add (by positivity) (by positivity)
    _ ≤ BC * ((Real.sqrt ((m : ℝ)) / S) * rho * cc ^ (-psi))
          + BC * (Real.sqrt 2 * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ)))
            * (((m : ℝ) / S) ^ ((1 : ℝ) - psi)) * cc ^ (((1 : ℝ) - 2 * psi) / 2)) :=
        add_le_add hP1 hP2
    _ = BC * ((Real.sqrt ((m : ℝ)) / S) * rho * cc ^ (-psi)
          + Real.sqrt 2 * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ)))
            * (((m : ℝ) / S) ^ ((1 : ℝ) - psi)) * cc ^ (((1 : ℝ) - 2 * psi) / 2)) := by
        ring

/-! ### Step 2: the n-uniform bound for the truncated matrix -/

set_option maxHeartbeats 1000000 in
theorem frobenius_truncated_le (m R : ℕ) (S psi c B_omega : ℝ)
    (hS : 0 < S) (hm : 0 < m) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (omega : ℝ → ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖
      ≤ (B_omega * |c|) * (Real.sqrt 2 * (Real.sqrt (m : ℝ) / S)
            * (rieszCycleCutoff R) ^ (-psi)
          + Real.sqrt 2 * ((2 : ℝ) ^ (-psi)) * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ)))
            * ((m : ℝ) / S)) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set cc : ℝ := rieszCycleCutoff R with hccdef
  have hcc : 0 < cc := rieszCycleCutoff_pos R
  set BC : ℝ := B_omega * |c| with hBCdef
  have hB0 : 0 ≤ B_omega := by
    have hb := homegaB 0 (Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩)
    linarith [abs_nonneg (omega 0)]
  have hBC0 : 0 ≤ BC := mul_nonneg hB0 (abs_nonneg c)
  set u : ℝ := (S : ℝ)⁻¹ * BC with hudef
  have hu0 : 0 ≤ u := mul_nonneg (inv_nonneg.2 hS.le) hBC0
  set f2 : ℕ → ℝ := fun d => (max cc (((2 : ℝ) / (m : ℝ)) * ((d : ℝ)))) ^ (-2 * psi)
    with hf2def
  have hf2nn : ∀ d : ℕ, 0 ≤ f2 d := fun d => by
    simp only [hf2def]
    exact Real.rpow_nonneg (by positivity) (-2 * psi)
  have htwo : ∀ x : ℝ, x ^ ((2 : ℝ)) = x ^ 2 := Real.rpow_two
  have hsqcap : ∀ (x : ℝ), 0 < x → (x ^ (-psi)) ^ 2 = x ^ (-2 * psi) := by
    intro x hx
    rw [pow_two, ← Real.rpow_add hx (-(psi : ℝ)) (-(psi : ℝ)),
      show (-(psi : ℝ) + -(psi : ℝ)) = (-2 * psi) from by ring]
  -- entry bound
  have hentry : ∀ (i j : Fin m),
      |weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j|
        ≤ u * ((max cc (((2 : ℝ) / (m : ℝ)) * (((Nat.dist i.val j.val : ℕ) : ℝ))))
          ^ (-psi)) := by
    intro i j
    have hdkey := abs_rieszCycleGridPoint_dist m hm i j
    have hbase : (0 : ℝ) < max cc
        |rieszCycleGridPoint m i - rieszCycleGridPoint m j| :=
      hcc.trans_le (le_max_left _ _)
    have hgi : rieszCycleGridPoint m i ∈ Icc (-1 : ℝ) 1 := rieszCycleGridPoint_mem_Icc hm i
    have hw : |omega (rieszCycleGridPoint m i)| ≤ B_omega := homegaB _ hgi
    unfold weightedTruncatedRieszDiscreteMatrix truncatedRieszKernel
    rw [← hdkey]
    calc |(S : ℝ)⁻¹ * omega (rieszCycleGridPoint m i) *
          (c * (max cc |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi))|
        = (S : ℝ)⁻¹ * (|omega (rieszCycleGridPoint m i)| *
          (|c| * (max cc |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi))) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hS.le),
            abs_of_nonneg (Real.rpow_nonneg hbase.le (-psi))]
          ring
      _ ≤ (S : ℝ)⁻¹ * (B_omega * (|c| * (max cc
            |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hw
              (mul_nonneg (abs_nonneg c) (Real.rpow_nonneg hbase.le (-psi))))
            (inv_nonneg.2 hS.le)
      _ = u * (max cc |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi) := by
          rw [hudef, hBCdef]; ring
  -- row sums
  have hrow : ∀ i : Fin m, ∑ j : Fin m,
      ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
      ≤ 2 * u ^ 2 * (∑ d ∈ Finset.range m, f2 d) := by
    intro i
    have h1 : ∑ j : Fin m, f2 ((i : ℕ).dist (j : ℕ))
        ≤ 2 * ∑ d ∈ Finset.range m, f2 d := sum_row_dist_le f2 hf2nn i
    have h2' : ∑ j : Fin m, ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
        ≤ ∑ j : Fin m, (u ^ 2 * f2 ((i : ℕ).dist (j : ℕ))) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [Real.norm_eq_abs]
      have hbd := hentry i j
      have hcap : (0 : ℝ) < max cc
          (((2 : ℝ) / (m : ℝ)) * (((Nat.dist i.val j.val : ℕ) : ℝ))) :=
        hcc.trans_le (le_max_left _ _)
      have h1' : |weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j| ^ ((2 : ℝ))
          ≤ (u * ((max cc (((2 : ℝ) / (m : ℝ))
              * (((Nat.dist i.val j.val : ℕ) : ℝ)))) ^ (-psi))) ^ ((2 : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hbd (by norm_num)
      refine le_trans h1' ?_
      rw [Real.mul_rpow hu0 (Real.rpow_nonneg hcap.le (-psi)), htwo, htwo,
        hsqcap _ hcap]
    rw [← Finset.mul_sum] at h2'
    have h3 : u ^ 2 * ∑ j : Fin m, f2 ((i : ℕ).dist (j : ℕ))
        ≤ u ^ 2 * (2 * ∑ d ∈ Finset.range m, f2 d) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg u)
    linarith
  have hsqsum : ∑ i : Fin m, ∑ j : Fin m,
      ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j‖ ^ ((2 : ℝ))
      ≤ (m : ℝ) * (2 * u ^ 2 * (∑ d ∈ Finset.range m, f2 d)) := by
    refine le_trans (Finset.sum_le_sum (fun i _ => hrow i)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  set Ssum2 : ℝ := ∑ d ∈ Finset.range m, f2 d with hSsum2def
  have hinv : (1 / (1 - 2 * psi : ℝ)) = ((1 - 2 * psi : ℝ)) ^ ((-1 : ℝ)) := by
    symm
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ (1 - 2 * psi : ℝ)) 1, Real.rpow_one,
      one_div]
  have hbound2 : Ssum2 ≤ cc ^ (-2 * psi)
      + ((2 : ℝ) / (m : ℝ)) ^ (-2 * psi) * ((1 - 2 * psi : ℝ)) ^ ((-1 : ℝ))
        * ((m : ℝ)) ^ ((1 : ℝ) - 2 * psi) := by
    have h := band_cutoff_weighted_le m m hm cc psi hcc hpsi1 hpsi2
    rwa [hinv] at h
  have hsqA : (cc ^ (-psi)) ^ 2 = cc ^ (-2 * psi) := by
    rw [pow_two, ← Real.rpow_add hcc (-(psi : ℝ)) (-(psi : ℝ)),
      show (-(psi : ℝ) + -(psi : ℝ)) = (-2 * psi) from by ring]
  have hsqrtA : Real.sqrt (cc ^ (-2 * psi)) = cc ^ (-psi) := by
    rw [← hsqA, Real.sqrt_sq (Real.rpow_nonneg hcc.le (-psi))]
  have h2m : (0 : ℝ) < (2 : ℝ) / (m : ℝ) := by positivity
  have hsqB : (((2 : ℝ) / (m : ℝ)) ^ (-psi)) ^ 2 = ((2 : ℝ) / (m : ℝ)) ^ (-2 * psi) := by
    rw [pow_two, ← Real.rpow_add h2m (-(psi : ℝ)) (-(psi : ℝ)),
      show (-(psi : ℝ) + -(psi : ℝ)) = (-2 * psi) from by ring]
  have hsqrtB : Real.sqrt (((2 : ℝ) / (m : ℝ)) ^ (-2 * psi))
      = ((2 : ℝ) / (m : ℝ)) ^ (-psi) := by
    rw [← hsqB, Real.sqrt_sq (Real.rpow_nonneg h2m.le (-psi))]
  have hsqZ : (((1 - 2 * psi : ℝ)) ^ (-(1 / 2 : ℝ))) ^ 2
      = ((1 - 2 * psi : ℝ)) ^ ((-1 : ℝ)) := by
    rw [pow_two, ← Real.rpow_add (by linarith : (0 : ℝ) < (1 - 2 * psi : ℝ))
      (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ)),
      show (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) = (-1 : ℝ) from by ring]
  have hsqrtZ : Real.sqrt (((1 - 2 * psi : ℝ)) ^ ((-1 : ℝ)))
      = ((1 - 2 * psi : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    rw [← hsqZ, Real.sqrt_sq (Real.rpow_nonneg (by linarith) (-(1 / 2 : ℝ)))]
  have hsqC : (((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2)) ^ 2 = ((m : ℝ)) ^ ((1 : ℝ) - 2 * psi) := by
    rw [pow_two, ← Real.rpow_add hmR (((1 : ℝ) - 2 * psi) / 2) (((1 : ℝ) - 2 * psi) / 2),
      show (((1 : ℝ) - 2 * psi) / 2 + ((1 : ℝ) - 2 * psi) / 2) = ((1 : ℝ) - 2 * psi)
        from by ring]
  have hsqrtC : Real.sqrt (((m : ℝ)) ^ ((1 : ℝ) - 2 * psi))
      = ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2) := by
    rw [← hsqC, Real.sqrt_sq (Real.rpow_nonneg hmR.le _)]
  rw [Matrix.frobenius_norm_def]
  refine le_trans (Real.rpow_le_rpow (by positivity) hsqsum (by norm_num)) ?_
  rw [← Real.sqrt_eq_rpow]
  have h1 : Real.sqrt ((m : ℝ) * (2 * u ^ 2 * Ssum2))
      ≤ Real.sqrt ((m : ℝ)) * (Real.sqrt 2 * (u * (cc ^ (-psi)
        + ((2 : ℝ) / (m : ℝ)) ^ (-psi) * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ))
          * ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2))))) := by
    have hcore : Real.sqrt Ssum2 ≤ cc ^ (-psi)
        + ((2 : ℝ) / (m : ℝ)) ^ (-psi) * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ))
          * ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2)) := by
      refine le_trans (Real.sqrt_le_sqrt hbound2) (le_trans
        (sqrt_add_le_sqrt_add (Real.rpow_nonneg hcc.le (-2 * psi))
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg h2m.le (-2 * psi))
            (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (1 - 2 * psi : ℝ)) (-1 : ℝ)))
            (Real.rpow_nonneg hmR.le ((1 : ℝ) - 2 * psi)))) ?_)
      rw [hsqrtA, Real.sqrt_mul (mul_nonneg (Real.rpow_nonneg h2m.le (-2 * psi))
          (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (1 - 2 * psi : ℝ)) (-1 : ℝ))) _,
        Real.sqrt_mul (Real.rpow_nonneg h2m.le (-2 * psi))
          ((1 - 2 * psi : ℝ) ^ (-1 : ℝ)), hsqrtB, hsqrtZ, hsqrtC]
      simp only [add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
      exact le_refl _
    have hmid : Real.sqrt 2 * u * Real.sqrt Ssum2
        ≤ Real.sqrt 2 * (u * (cc ^ (-psi)
          + ((2 : ℝ) / (m : ℝ)) ^ (-psi) * ((1 - 2 * psi) ^ (-(1 / 2 : ℝ))
            * ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2)))) := by
      refine le_trans (mul_le_mul_of_nonneg_left hcore
        (mul_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2) hu0)) ?_
      simp only [← mul_assoc, hudef, mul_assoc]
      exact le_refl _
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (m : ℝ)) _,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * u ^ 2) Ssum2,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (u ^ 2), Real.sqrt_sq hu0]
    exact mul_le_mul_of_nonneg_left hmid (Real.sqrt_nonneg (m : ℝ))
  refine le_trans h1 ?_
  -- final monomial comparison over common atoms
  have hscal : ((2 : ℝ) / (m : ℝ)) ^ (-psi) = ((m : ℝ)) ^ psi * ((2 : ℝ)) ^ (-psi) := by
    rw [Real.rpow_neg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hmR.le) psi,
      Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hmR.le psi, inv_div, div_eq_inv_mul,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) psi]
    ring
  have e3'' : Real.sqrt ((m : ℝ)) * ((m : ℝ)) ^ psi
      * ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2) = (m : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hmR ((1 : ℝ) / 2) psi,
      ← Real.rpow_add hmR (((1 : ℝ) / 2) + psi) (((1 : ℝ) - 2 * psi) / 2),
      show ((1 : ℝ) / 2 + psi + ((1 : ℝ) - 2 * psi) / 2) = 1 from by ring, Real.rpow_one]
  rw [hscal, hudef, hBCdef, show ((m : ℝ) / S)
      = Real.sqrt ((m : ℝ)) * ((m : ℝ)) ^ psi
        * ((m : ℝ)) ^ (((1 : ℝ) - 2 * psi) / 2) * (S : ℝ)⁻¹ from by
        rw [e3'']; ring]
  simp only [add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  first
    | exact le_refl _
    | exact le_rfl
    | ring

/-! ### Step 3: the uniform removal assembly -/

set_option maxHeartbeats 1000000 in
/-- **Uniform discrete Riesz cutoff removal.**  In the mesh regime `m n → ∞`,
`m n / S n → 2`, eventually positive `S n`, `m n`, `0 < psi < 1/2`, and
`|omega| ≤ B_omega` on `[-1, 1]`, the discrete cyclic cycle values converge
to the truncated ones uniformly in the row index after choosing a large
cutoff level `R`. -/
theorem hasUniformDiscreteRieszCutoffRemoval
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c B_omega : ℝ) (omega : ℝ → ℝ)
    (hmtop : Tendsto m atTop atTop)
    (hMS : Tendsto (fun n => ((m n : ℕ) : ℝ) / S n) atTop (𝓝 2))
    (hpos : ∀ᶠ n in atTop, 0 < S n ∧ 0 < m n)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    HasUniformDiscreteRieszCutoffRemoval m S psi c omega := by
  intro k hk eps heps
  -- constants: BC, Z, tau, W, eta
  have hB0 : 0 ≤ B_omega := by
    have hb := homegaB 0 (Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩)
    linarith [abs_nonneg (omega 0)]
  have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 (by omega)
  set BC : ℝ := B_omega * |c| with hBCdef
  have hBC0 : 0 ≤ BC := mul_nonneg hB0 (abs_nonneg c)
  set Z : ℝ := (1 - 2 * psi) ^ (-((1 : ℝ) / 2)) with hZdef
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos (by linarith) _
  set tau : ℝ := BC * (Real.sqrt 2 * (2 : ℝ) ^ (-psi) * Z * 3) with htaudef
  have htau0 : 0 ≤ tau := by
    refine mul_nonneg hBC0 ?_
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) (-psi)))
        hZ0.le) (by norm_num)
  set W : ℝ := 4 + 2 * tau with hWdef
  have hW0 : 0 < W := by have := htau0; linarith
  have hWk0 : 0 < W ^ (k - 1) := pow_pos hW0 (k - 1)
  set eta : ℝ := eps / (4 * (k : ℝ) * W ^ (k - 1)) with hetadef
  have heta0 : 0 < eta := by
    refine div_pos heps ?_
    exact mul_pos (mul_pos (by norm_num) hk0) hWk0
  have hA : 0 < (1 - 2 * psi) / 2 := by linarith
  -- (m n : ℝ) → ∞ and the mesh-correction limit rho → 1 (R-independent tails)
  have hmninf : Tendsto (fun n => ((m n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.2 hmtop
  have hpos' : ∀ᶠ n in atTop, 0 < S n ∧ 0 < ((m n : ℕ) : ℝ) :=
    hpos.mono fun n hn => ⟨hn.1, Nat.cast_pos.2 (by omega)⟩
  have hcorr : Tendsto (fun n => meshRho (m n) (S n) psi) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ (tendsto_mesh_correction_rpow hpsi1 hmninf hMS hpos')
    exact Filter.Eventually.of_forall fun n => rfl
  have hcorrK : Tendsto (fun n => meshRho (m n) (S n) psi ^ k) atTop (𝓝 1) := by
    simpa using hcorr.pow k
  -- q ↦ q^(-1/2) → 0 along (m n : ℝ)
  have hhalf0 : Tendsto (fun q : ℝ => q ^ (-((1 : ℝ) / 2))) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).inv_tendsto_atTop)
    refine Filter.eventually_atTop.2 ⟨1, fun x hx => ?_⟩
    exact (Real.rpow_neg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx) ((1 : ℝ) / 2)).symm
  have hhalfn : Tendsto (fun n : ℕ => ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2))) atTop (𝓝 0) :=
    hhalf0.comp hmninf
  -- (1) the band value tends to 0 in R; fix R0 with atomBf R < min eta 1
  have hAinv : Tendsto (fun R : ℕ => (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2))))
      atTop (𝓝 0) := by
    refine Tendsto.congr' ?_
      ((tendsto_rpow_atTop hA).inv_tendsto_atTop.comp
        (tendsto_natCast_atTop_iff.2 (tendsto_add_atTop_nat 1)))
    exact Filter.Eventually.of_forall fun R =>
      (Real.rpow_neg (Nat.cast_nonneg (R + 1)) ((1 - 2 * psi) / 2)).symm
  set atomBf : ℕ → ℝ := fun R => BC * (Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))
      * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))) with hatomBdef
  have hbandlim : Tendsto atomBf atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => BC * (Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))))
        atTop (𝓝 (BC * (Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))))) :=
      tendsto_const_nhds
    have h := hAinv.mul hc
    rw [zero_mul] at h
    refine Tendsto.congr' ?_ h
    refine Filter.Eventually.of_forall fun R => ?_
    rw [hatomBdef]
    ring
  have hminpos : (0 : ℝ) < min eta 1 := lt_min heta0 (by norm_num)
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℕ, ∀ R ≥ R0, atomBf R < min eta 1 :=
    Filter.eventually_atTop.1 (hbandlim.eventually (Iio_mem_nhds hminpos))
  refine Filter.eventually_atTop.2 ⟨R0, fun R hR0R => ?_⟩
  have hbandR : atomBf R < min eta 1 := hR0 R hR0R
  -- cutoff identity with cc = rieszCycleCutoff R = ((R + 1 : ℕ) : ℝ)⁻¹
  have hR1 : (0 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hccpsi : rieszCycleCutoff R ^ (-psi) = ((R + 1 : ℕ) : ℝ) ^ psi := by
    show (((R + 1 : ℕ) : ℝ)⁻¹) ^ (-psi) = ((R + 1 : ℕ) : ℝ) ^ psi
    rw [Real.inv_rpow hR1 (-psi), Real.rpow_neg hR1 psi, inv_inv]
  have hccA : rieszCycleCutoff R ^ ((1 - 2 * psi) / 2)
      = ((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)) := by
    show (((R + 1 : ℕ) : ℝ)⁻¹) ^ ((1 - 2 * psi) / 2)
      = ((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2))
    rw [Real.inv_rpow hR1 ((1 - 2 * psi) / 2), Real.rpow_neg hR1 ((1 - 2 * psi) / 2)]
  -- per-R atoms for the delta/omega tails
  set atomDf : ℕ → ℝ := fun n => BC * ((6 : ℝ) * (((R + 1 : ℕ) : ℝ) ^ psi)
      * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2))) with hatomDdef
  set atomOf : ℕ → ℝ := fun n => BC * (Real.sqrt 2 * ((3 : ℝ) * (((R + 1 : ℕ) : ℝ) ^ psi)
      * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)))) with hatomOdef
  -- (3) threshold for the rho-term
  set muRbase : ℝ := (3 : ℝ) * (|c| * B_omega) * (((R + 1 : ℕ) : ℝ) ^ psi) with hmuRdef
  have hmuR0 : 0 ≤ muRbase :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg c) hB0))
      (Real.rpow_nonneg (Nat.cast_nonneg (R + 1)) psi)
  have hmuRk0 : 0 ≤ muRbase ^ k := pow_nonneg hmuR0 k
  have hdenpos : (0 : ℝ) < 2 * (muRbase ^ k + 1) := by linarith
  have hden : (2 : ℝ) * (muRbase ^ k + 1) ≠ 0 := ne_of_gt hdenpos
  set t2 : ℝ := eps / (2 * (muRbase ^ k + 1)) with ht2def
  have ht2pos : 0 < t2 := div_pos heps hdenpos
  have h7 : t2 * (muRbase ^ k + 1) = eps / 2 := by
    rw [ht2def, div_mul_eq_mul_div, div_eq_div_iff hden (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  -- (2) per-fixed-R n-tails
  have hdelim : Tendsto atomDf atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => BC * ((6 : ℝ) * (((R + 1 : ℕ) : ℝ) ^ psi)))
        atTop (𝓝 (BC * ((6 : ℝ) * (((R + 1 : ℕ) : ℝ) ^ psi)))) := tendsto_const_nhds
    have h := hhalfn.mul hc
    rw [zero_mul] at h
    refine Tendsto.congr' ?_ h
    refine Filter.Eventually.of_forall fun n => ?_
    rw [hatomDdef]
    ring
  have homegim : Tendsto atomOf atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ =>
        BC * (Real.sqrt 2 * ((3 : ℝ) * (((R + 1 : ℕ) : ℝ) ^ psi))))
        atTop (𝓝 (BC * (Real.sqrt 2 * ((3 : ℝ) * (((R + 1 : ℕ) : ℝ) ^ psi))))) :=
      tendsto_const_nhds
    have h := hhalfn.mul hc
    rw [zero_mul] at h
    refine Tendsto.congr' ?_ h
    refine Filter.Eventually.of_forall fun n => ?_
    rw [hatomOdef]
    ring
  have edel : ∀ᶠ n : ℕ in atTop, atomDf n < min eta 1 :=
    hdelim.eventually (Iio_mem_nhds hminpos)
  have eome : ∀ᶠ n : ℕ in atTop, atomOf n < 1 :=
    homegim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have erho : ∀ᶠ n : ℕ in atTop, |meshRho (m n) (S n) psi ^ k - 1| < t2 := by
    obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hcorrK t2 ht2pos
    refine Filter.eventually_atTop.2 ⟨N2, fun n hn => ?_⟩
    have h3 := hN2 n hn
    rwa [Real.dist_eq] at h3
  have hsimple : ∀ᶠ n : ℕ in atTop, (0 < S n ∧ 0 < m n ∧ (1 : ℝ) < ((m n : ℕ) : ℝ) / S n ∧
      ((m n : ℕ) : ℝ) / S n < 3 ∧ (2 : ℕ) * (R + 1) ≤ m n) := by
    filter_upwards [hpos, hMS.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      hMS.eventually (Iio_mem_nhds (by norm_num : (2 : ℝ) < 3)),
      hmtop.eventually_ge_atTop (2 * (R + 1))] with n hn hqlo hqhi hbig
    exact ⟨hn.1, hn.2, hqlo, hqhi, hbig⟩
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 hsimple
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 ((erho.and edel).and eome)
  refine Filter.eventually_atTop.2 ⟨max N1 N2, fun n hn => ?_⟩
  obtain ⟨hSn, hmnN, hqlo, hqhi, hbig⟩ := hN1 n ((le_max_left _ _).trans hn)
  obtain ⟨⟨hrho', hdel'⟩, home'⟩ := hN2 n ((le_max_right _ _).trans hn)
  have hmnR : (0 : ℝ) < ((m n : ℕ) : ℝ) := Nat.cast_pos.2 hmnN
  have hq1 : (1 : ℝ) ≤ ((m n : ℕ) : ℝ) / S n := hqlo.le
  have hq3 : ((m n : ℕ) : ℝ) / S n ≤ 3 := hqhi.le
  have hqnn : 0 ≤ ((m n : ℕ) : ℝ) / S n := div_nonneg hmnR.le hSn.le
  have hmeshpos : 0 ≤ meshRho (m n) (S n) psi :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) hSn.le) hmnR.le) psi
  have hmesh2 : meshRho (m n) (S n) psi ≤ 2 := by
    have hSm : S n ≤ ((m n : ℕ) : ℝ) := by
      simpa using (le_div_iff₀ hSn).mp hq1
    have h1 : (2 : ℝ) * S n / ((m n : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hmnR]
      linarith
    refine le_trans (Real.rpow_le_rpow (div_nonneg (mul_nonneg (by norm_num) hSn.le)
      hmnR.le) h1 hpsi1.le) ?_
    have h22 : (2 : ℝ) ^ psi ≤ (2 : ℝ) ^ (1 : ℝ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 (by linarith)
    rwa [Real.rpow_one] at h22
  -- the cutoff smallness hypothesis for the mesh-difference Frobenius bound
  have hcut2 : (2 : ℝ) ≤ ((m n : ℕ) : ℝ) * rieszCycleCutoff R := by
    have hR1p : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos R
    have hcc : rieszCycleCutoff R = ((R + 1 : ℕ) : ℝ)⁻¹ := rfl
    rw [hcc, mul_comm, inv_mul_eq_div, le_div_iff₀ hR1p]
    exact_mod_cast hbig
  -- the √m/S ↔ q/√m split and 1/√m = m^(-1/2)
  have hsqrtinv : 0 < Real.sqrt ((m n : ℕ) : ℝ) := Real.sqrt_pos.2 hmnR
  have hsqrtid : Real.sqrt ((m n : ℕ) : ℝ) * Real.sqrt ((m n : ℕ) : ℝ) = ((m n : ℕ) : ℝ) :=
    Real.mul_self_sqrt hmnR.le
  have hminv : ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) = (Real.sqrt ((m n : ℕ) : ℝ))⁻¹ := by
    rw [Real.rpow_neg hmnR.le ((1 : ℝ) / 2), Real.sqrt_eq_rpow]
  have hsplit : Real.sqrt ((m n : ℕ) : ℝ) / S n
      = ((m n : ℕ) : ℝ) / S n * (Real.sqrt ((m n : ℕ) : ℝ))⁻¹ := by
    rw [div_eq_iff hSn.ne', div_mul_eq_mul_div]
    field_simp [hsqrtid, hSn.ne', hsqrtinv.ne']
    rw [Real.sq_sqrt hmnR.le]
  -- (4a) mesh-difference Frobenius bound, split into the delta-atom and the band atom
  have hDg := frobenius_rieszMeshDiff_le (m n) R (S n) psi c B_omega hSn hmnN hpsi1
    hpsi2 omega homegaB hcut2
  rw [← hBCdef, ← hZdef, hccpsi, hccA] at hDg
  have htp1 : Real.sqrt ((m n : ℕ) : ℝ) / S n
      ≤ (3 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) := by
    rw [hminv, hsplit]
    exact mul_le_mul_of_nonneg_right hq3 (inv_nonneg.2 (Real.sqrt_nonneg _))
  have ht1 : (Real.sqrt ((m n : ℕ) : ℝ) / S n) * meshRho (m n) (S n) psi
      * (((R + 1 : ℕ) : ℝ) ^ psi)
      ≤ (6 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) * (((R + 1 : ℕ) : ℝ) ^ psi) := by
    have hqm : ((m n : ℕ) : ℝ) / S n * meshRho (m n) (S n) psi ≤ (6 : ℝ) := by
      calc ((m n : ℕ) : ℝ) / S n * meshRho (m n) (S n) psi
          ≤ (3 : ℝ) * meshRho (m n) (S n) psi := mul_le_mul_of_nonneg_right hq3 hmeshpos
        _ ≤ (3 : ℝ) * (2 : ℝ) := mul_le_mul_of_nonneg_left hmesh2 (by norm_num)
        _ = 6 := by norm_num
    calc (Real.sqrt ((m n : ℕ) : ℝ) / S n) * meshRho (m n) (S n) psi
          * (((R + 1 : ℕ) : ℝ) ^ psi)
        = ((m n : ℕ) : ℝ) / S n * (Real.sqrt ((m n : ℕ) : ℝ))⁻¹
            * meshRho (m n) (S n) psi * (((R + 1 : ℕ) : ℝ) ^ psi) := by rw [hsplit]
      _ = ((m n : ℕ) : ℝ) / S n * meshRho (m n) (S n) psi
            * ((Real.sqrt ((m n : ℕ) : ℝ))⁻¹ * (((R + 1 : ℕ) : ℝ) ^ psi)) := by ring
      _ ≤ (6 : ℝ) * ((Real.sqrt ((m n : ℕ) : ℝ))⁻¹ * (((R + 1 : ℕ) : ℝ) ^ psi)) :=
            mul_le_mul_of_nonneg_right hqm (mul_nonneg
              (inv_nonneg.2 (Real.sqrt_nonneg _))
              (Real.rpow_nonneg (Nat.cast_nonneg (R + 1)) psi))
      _ = (6 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) * (((R + 1 : ℕ) : ℝ) ^ psi) := by
          rw [hminv]; ring
  have ht2b : Real.sqrt 2 * Z * (((m n : ℕ) : ℝ) / S n) ^ ((1 : ℝ) - psi)
        * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))
      ≤ Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))
        * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2))) := by
    have hq3rpow : (((m n : ℕ) : ℝ) / S n) ^ ((1 : ℝ) - psi)
        ≤ (3 : ℝ) ^ ((1 : ℝ) - psi) :=
      Real.rpow_le_rpow hqnn hq3 (by linarith)
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hq3rpow (mul_nonneg (by positivity) hZ0.le))
      (Real.rpow_nonneg (Nat.cast_nonneg (R + 1)) _)
  have hDg2 : ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖
      ≤ BC * ((6 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) * (((R + 1 : ℕ) : ℝ) ^ psi))
        + BC * (Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))
          * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))) := by
    calc ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖
        ≤ BC * ((Real.sqrt ((m n : ℕ) : ℝ) / S n) * meshRho (m n) (S n) psi
              * (((R + 1 : ℕ) : ℝ) ^ psi)
            + Real.sqrt 2 * Z * (((m n : ℕ) : ℝ) / S n) ^ ((1 : ℝ) - psi)
              * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))) := hDg
      _ = BC * ((Real.sqrt ((m n : ℕ) : ℝ) / S n) * meshRho (m n) (S n) psi
              * (((R + 1 : ℕ) : ℝ) ^ psi))
          + BC * (Real.sqrt 2 * Z * (((m n : ℕ) : ℝ) / S n) ^ ((1 : ℝ) - psi)
              * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))) := mul_add BC _ _
      _ ≤ BC * ((6 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) * (((R + 1 : ℕ) : ℝ) ^ psi))
          + BC * (Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))
            * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))) :=
            add_le_add (mul_le_mul_of_nonneg_left ht1 hBC0)
              (mul_le_mul_of_nonneg_left ht2b hBC0)
  -- (4b) truncated Frobenius bound, split into the omega-atom and tau
  have hT := frobenius_truncated_le (m n) R (S n) psi c B_omega hSn hmnN hpsi1 hpsi2
    omega homegaB
  rw [← hBCdef, ← hZdef, hccpsi] at hT
  have hsZ : 0 ≤ Real.sqrt 2 * (2 : ℝ) ^ (-psi) * Z :=
    mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (by norm_num) (-psi))) hZ0.le
  have hT2 : ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖
      ≤ BC * (Real.sqrt 2 * ((3 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)))
          * (((R + 1 : ℕ) : ℝ) ^ psi))
        + BC * (Real.sqrt 2 * (2 : ℝ) ^ (-psi) * Z * 3) := by
    calc ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖
        ≤ BC * (Real.sqrt 2 * (Real.sqrt ((m n : ℕ) : ℝ) / S n)
              * (((R + 1 : ℕ) : ℝ) ^ psi)
            + Real.sqrt 2 * (2 : ℝ) ^ (-psi) * Z * (((m n : ℕ) : ℝ) / S n)) := hT
      _ = BC * (Real.sqrt 2 * (Real.sqrt ((m n : ℕ) : ℝ) / S n)
              * (((R + 1 : ℕ) : ℝ) ^ psi))
          + BC * (Real.sqrt 2 * (2 : ℝ) ^ (-psi) * Z * (((m n : ℕ) : ℝ) / S n)) :=
          mul_add BC _ _
      _ ≤ BC * (Real.sqrt 2 * ((3 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)))
              * (((R + 1 : ℕ) : ℝ) ^ psi))
          + BC * (Real.sqrt 2 * (2 : ℝ) ^ (-psi) * Z * 3) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left htp1 (Real.sqrt_nonneg 2))
                (Real.rpow_nonneg (Nat.cast_nonneg (R + 1)) psi)) hBC0
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq3 hsZ) hBC0
  have hTbound : ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖
      ≤ 1 + tau := by
    have eO : BC * (Real.sqrt 2 * ((3 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)))
        * (((R + 1 : ℕ) : ℝ) ^ psi)) = atomOf n := by
      rw [hatomOdef]; ring
    rw [eO, ← htaudef] at hT2
    linarith [hT2, home']
  -- (4c) bracket bound and the two eps-halves
  have hminle1 : min eta 1 ≤ eta := min_le_left _ _
  have hminle2 : min eta 1 ≤ 1 := min_le_right _ _
  have hDg2eta : ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖ ≤ 2 * eta := by
    have eD : BC * ((6 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2))
        * (((R + 1 : ℕ) : ℝ) ^ psi)) = atomDf n := by rw [hatomDdef]; ring
    have eB : BC * (Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))
        * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))) = atomBf R := by
      rw [hatomBdef]
    rw [eD, eB] at hDg2
    linarith [hDg2, hdel', hbandR, hminle1]
  have hDg22 : ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖ ≤ 2 := by
    have eD : BC * ((6 : ℝ) * ((m n : ℕ) : ℝ) ^ (-((1 : ℝ) / 2))
        * (((R + 1 : ℕ) : ℝ) ^ psi)) = atomDf n := by rw [hatomDdef]; ring
    have eB : BC * (Real.sqrt 2 * Z * ((3 : ℝ) ^ ((1 : ℝ) - psi))
        * (((R + 1 : ℕ) : ℝ) ^ (-((1 - 2 * psi) / 2)))) = atomBf R := by
      rw [hatomBdef]
    rw [eD, eB] at hDg2
    linarith [hDg2, hdel', hbandR, hminle2]
  have hprod : meshRho (m n) (S n) psi
      * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖
      ≤ (2 : ℝ) * (1 + tau) := by
    calc meshRho (m n) (S n) psi
          * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖
        ≤ (2 : ℝ) * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖ :=
          mul_le_mul_of_nonneg_right hmesh2 (norm_nonneg _)
      _ ≤ (2 : ℝ) * (1 + tau) := mul_le_mul_of_nonneg_left hTbound (by norm_num)
  have hbrk0 : 0 ≤ ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖
      + meshRho (m n) (S n) psi
        * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg hmeshpos (norm_nonneg _))
  have hpow : (‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖ + meshRho (m n) (S n) psi
      * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖) ^ (k - 1)
      ≤ (4 + 2 * tau) ^ (k - 1) := by
    refine pow_le_pow_left₀ hbrk0 ?_ (k - 1)
    linarith [hDg22, hprod]
  have hterm1 : ((k : ℝ) * ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖
      * ((‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖ + meshRho (m n) (S n) psi
        * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖) ^ (k - 1)))
      ≤ eps / 2 := by
    have h1 : ((k : ℝ) * ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖)
        ≤ ((k : ℝ) * (2 * eta)) :=
      mul_le_mul_of_nonneg_left hDg2eta hk0.le
    have h2 : ((k : ℝ) * ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖
        * ((‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖ + meshRho (m n) (S n) psi
          * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖) ^ (k - 1)))
        ≤ ((k : ℝ) * (2 * eta)) * ((4 + 2 * tau) ^ (k - 1)) :=
      mul_le_mul h1 hpow (pow_nonneg hbrk0 (k - 1))
        (mul_nonneg hk0.le (by linarith))
    have h3 : ((k : ℝ) * (2 * eta)) * ((4 + 2 * tau) ^ (k - 1)) = eps / 2 := by
      have hWne : (4 + 2 * tau) ^ (k - 1) ≠ 0 := by
        rw [← hWdef]
        exact hWk0.ne'
      rw [hetadef, hWdef]
      field_simp [hk0.ne', hWne]
      norm_num
    linarith [h2, h3]
  have hmu0 : 0 ≤ ((m n : ℕ) : ℝ) / S n * (|c| * B_omega * (rieszCycleCutoff R ^ (-psi))) :=
    mul_nonneg hqnn (mul_nonneg (mul_nonneg (abs_nonneg c) hB0)
      (Real.rpow_nonneg (rieszCycleCutoff_pos R).le (-psi)))
  have hmule : ((m n : ℕ) : ℝ) / S n * (|c| * B_omega * (rieszCycleCutoff R ^ (-psi)))
      ≤ muRbase := by
    rw [hccpsi]
    calc ((m n : ℕ) : ℝ) / S n * (|c| * B_omega * (((R + 1 : ℕ) : ℝ) ^ psi))
        = ((m n : ℕ) : ℝ) / S n * ((|c| * B_omega) * (((R + 1 : ℕ) : ℝ) ^ psi)) := by ring
      _ ≤ (3 : ℝ) * ((|c| * B_omega) * (((R + 1 : ℕ) : ℝ) ^ psi)) :=
          mul_le_mul_of_nonneg_right hq3 (mul_nonneg (mul_nonneg (abs_nonneg c) hB0)
            (Real.rpow_nonneg (Nat.cast_nonneg (R + 1)) psi))
      _ = (3 : ℝ) * (|c| * B_omega) * (((R + 1 : ℕ) : ℝ) ^ psi) := by ring
  have hmuk : (((m n : ℕ) : ℝ) / S n * (|c| * B_omega * (rieszCycleCutoff R ^ (-psi)))) ^ k
      ≤ muRbase ^ k := pow_le_pow_left₀ hmu0 hmule k
  have hterm2 : |meshRho (m n) (S n) psi ^ k - 1|
      * (((m n : ℕ) : ℝ) / S n * (|c| * B_omega * (rieszCycleCutoff R ^ (-psi)))) ^ k
      < eps / 2 := by
    have h2 : t2 * muRbase ^ k < eps / 2 := by
      have h8 : t2 * muRbase ^ k < t2 * (muRbase ^ k + 1) :=
        mul_lt_mul_of_pos_left (by linarith) ht2pos
      rw [← h7]
      exact h8
    have h3 : |meshRho (m n) (S n) psi ^ k - 1|
        * (((m n : ℕ) : ℝ) / S n * (|c| * B_omega * (rieszCycleCutoff R ^ (-psi)))) ^ k
        ≤ t2 * muRbase ^ k := by
      calc |meshRho (m n) (S n) psi ^ k - 1|
            * (((m n : ℕ) : ℝ) / S n * (|c| * B_omega * (rieszCycleCutoff R ^ (-psi)))) ^ k
          ≤ t2 * (((m n : ℕ) : ℝ) / S n
              * (|c| * B_omega * (rieszCycleCutoff R ^ (-psi)))) ^ k :=
            mul_le_mul_of_nonneg_right (le_of_lt hrho') (pow_nonneg hmu0 k)
        _ ≤ t2 * muRbase ^ k := mul_le_mul_of_nonneg_left hmuk ht2pos.le
    linarith [h2, h3]
  -- (4d) close via the cyclic bound
  have hmain := abs_cycleValue_diff_le_cyclic (m n) k R (S n) psi c B_omega hSn hmnN
    hpsi1 hpsi2 hk omega homegaB
  calc |weightedRieszDiscreteCycleValue (m n) k (S n) psi c omega
        - weightedTruncatedRieszDiscreteCycleValue (m n) k R (S n) psi c omega|
      ≤ ((k : ℝ) * ‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖
          * ((‖rieszMeshDiffMatrix (m n) R (S n) psi c omega‖
              + meshRho (m n) (S n) psi
                * ‖weightedTruncatedRieszDiscreteMatrix (m n) R (S n) psi c omega‖) ^ (k - 1)))
        + |meshRho (m n) (S n) psi ^ k - 1|
          * (((m n : ℕ) : ℝ) / S n * (|c| * B_omega * rieszCycleCutoff R ^ (-psi))) ^ k :=
        hmain
    _ < eps := by linarith [hterm1, hterm2]
