import Hurst.FrozenQuadratureRun
import Hurst.BandRemovalComplete

/-!
# The frozen-vs-Riesz `hsmall` mirror assembly

This file is the last assembly of the corrected route: it produces the
far-band word input `hsmall` consumed by
`Hurst.frozenQ1_trace_pow_tendsto_of_farBand`
(`∀ eps > 0, ∀ᶠ n in atTop, |tr(F_n ^ k) − tr(actualQ1RieszMatrix n ^ k)| < eps`)
in the MIRROR architecture of `Hurst.BandRemovalComplete`.

## Scale audit (drives every statement below)

With `S = n * δ`, `m = (localWeightActiveSet n 1 δ t).card`, `ψ = 2 − 2 f t`,
`c = f t * (2 f t − 1)` (so `0 < ψ < 1/2` under `3/4 < f t`), the two sides are
(from the landed definitions `actualQ1NormalizedFrozenMatrix`
= `S⁻¹ u_i * S^ψ * crossLagCorr(h_i, h_j, d)` and `actualQ1RieszMatrix`
= `weightedRieszDiscreteMatrix m S ψ c ω` = `S⁻¹ ω(x_i) * c * S^ψ * d^{-ψ}`
with `d = Nat.dist` of the active indices):

* BOTH sides carry the common entry scale `S^{ψ−1}`: the frozen side is
  `S^{ψ−1} u_i crossLagCorr(h_i, h_j, d)`, the Riesz side
  `S^{ψ−1} ω(x_i) c d^{-ψ}`.
* Consequently the entrywise difference is `Θ(S^{ψ−1})` on EVERY band (at a
  fixed class the two `O(1)` constants — the frozen class value versus
  `c d^{-ψ}` times the row profile — genuinely differ), so
  `‖F_n − T_n‖_F = Θ(1)`: the direct Frobenius-difference route is arithmetically
  dead, exactly as `‖U‖_F` was on the Riesz side.  `hsmall` can only come from
  the WORD-LEVEL assembly (the sharp cyclic engine of `Hurst.BandRemovalSharp`,
  mirrored here at `rho = 1`) or from the common-limit packaging.
* Both sides have bounded-in-`n` Frobenius norm scale: per row,
  `∑_j |T i j|² ≤ 2 B_ω² c² (S^{ψ−1})² * m^{1−2ψ}/(1−2ψ)` — the `2ψ < 1` band
  power sum (`sum_range_rpow_neg_shift_le`) — so `‖T_n‖_F = O(1)`.

## Landed here

1. `abs_trace_add_pow_split_cyclic` (the L3 mirror at `rho = 1`): for ANY two
   matrices `D T` and `k ≥ 2`,
   `|tr((T+D)^k) − tr(T^k)| ≤ (‖D‖_F + ‖T‖_F)^k − ‖T‖_F^k`
   — the exact mirror of `abs_trace_rieszMeshDiff_split_cyclic` with the mesh
   correction removed; proved with the SAME public word machinery
   (`matrix_pow_binomial`, `trace_matWord_bound`, `sum_word_scalars_erase_eq`).
   Bernoulli corollary `abs_trace_add_pow_split_bernoulli`.
2. `frozenHsmall_rieszEntry_le` (uniform Riesz entry bound):
   `|T i j| ≤ S^{ψ−1} B_ω |c|` for every pair — the diagonal being exactly `0`.
3. `frozenHsmall_frozenEntry_near_le` (near-band frozen entry bound, from
   `frozenQ1_kernel_nearBand_bounded`): `|F i j| ≤ S^{ψ−1} U B` for `d ≤ R`,
   hence `frozenHsmall_nearBandDiff_le`: `|F i j − T i j| ≤ S^{ψ−1}(UB + B_ω|c|)`
   on the near band.
4. `frozenHsmall_class_eps` (deliverable 1, the KEY new analytic input): the
   class-stratified vanishing at the normalized level — for each FIXED class
   `d`, the class-`d` frozen entries converge to
   `S^{ψ−1} u_i * firstIncrementLagCorrelation (f t) d` at uniform relative
   precision `eps` (repackaging `frozenQ1_kernel_class_converges` through the
   `S^{-1} u_i` normalization; the `S^ψ` kernel scaling cancels the `S^{-1}`
   normalization, so the bound is uniform in `n`).
5. `frozenHsmall_rieszRowFar_le` (deliverable 2, far-band tail): per-row power
   sum `∑_j |T i j|² ≤ 2 B_ω² c² (S^{ψ−1})² m^{1−2ψ}/(1−2ψ)` via the row
   distance stratification `sum_row_dist_le` and the `2ψ < 1` power sum
   `sum_range_rpow_neg_shift_le`.
6. `frozenHsmallMirror` (deliverable 3, the assembly): given the two
   trace-power convergences to the common continuum limit `L` — the Riesz side
   is the LANDED Riesz quadrature (cf. the derivation of `hriesz` inside
   `frozenQ1_trace_pow_tendsto_of_farBand`; the frozen side is the same
   three-predicate run fed by the class vanishing of `frozenHsmall_class_eps`
   and the far-band envelope) — `hsmall` follows by epsilon-halving, in the
   EXACT shape consumed by `frozenQ1_trace_pow_tendsto_of_farBand`.

## Honest gap note

The word mirror (1) reduces `hsmall` to smallness of
`(‖F−T‖+‖T‖)^k − ‖T‖^k` with `‖T‖ = O(1)`; since `‖F−T‖_F = Θ(1)` (scale audit
above), the assembly must go through the common-limit form, and the remaining
documented step is the FROZEN-side quadrature
(`tr(F_n^k) → weightedRieszCycleIntegral ...`): its far band needs the `16/x`
relative envelope `firstIncrementCrossLagCorrelation_scaled_error_le_explicit`
assembled over words (mirroring `frobenius_rieszMeshDiff_le`'s stratification
with the profile bridge `u_i ↔ ω(x_i)`), while its near band is closed by
deliverable 4.  Everything else of the mirror route is proved here.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ### Small helpers -/

private theorem abs_sq_le_sq' {x B : ℝ} (h : |x| ≤ B) : |x| ^ 2 ≤ B ^ 2 := by
  rcases abs_le.mp h with ⟨h1, h2⟩
  nlinarith [h1, h2, abs_nonneg x]

private theorem abs_le_abs_add {a b : ℝ} : |a - b| ≤ |a| + |b| := by
  have ha1 : a ≤ |a| := le_abs_self a
  have ha2 : -|a| ≤ a := by
    rcases le_total 0 a with ha | ha
    · rw [abs_of_nonneg ha]; linarith
    · rw [abs_of_nonpos ha]; linarith
  have hb1 : b ≤ |b| := le_abs_self b
  have hb2 : -|b| ≤ b := by
    rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg hb]; linarith
    · rw [abs_of_nonpos hb]; linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

private theorem abs_add_le_add {x y : ℝ} : |x + y| ≤ |x| + |y| := by
  have hx1 : x ≤ |x| := le_abs_self x
  have hx2 : -|x| ≤ x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  have hy1 : y ≤ |y| := le_abs_self y
  have hy2 : -|y| ≤ y := by
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

private theorem countTrue_false_fun {k : ℕ} :
    countTrue (fun _ : Fin k => (false : Bool)) = 0 := by
  simp [countTrue]

private theorem countFalse_false_fun {k : ℕ} :
    countFalse (fun _ : Fin k => (false : Bool)) = k := by
  simp [countFalse]

/-! ### The L3 word engine mirrored at `rho = 1` -/

/-- **The cyclic word mirror (deliverable 3 engine).**  For any two matrices
`D T` on the same finite index type and `k ≥ 2`:
`|tr((T + D)^k) − tr(T^k)| ≤ (‖D‖_F + ‖T‖_F)^k − ‖T‖_F^k`.
This is `abs_trace_rieszMeshDiff_split_cyclic` of `Hurst.BandRemovalSharp`
with the mesh correction `rho` specialized to `1` and with an arbitrary pair
`D, T` (here the frozen-vs-Riesz pair).  The proof is the same cyclic word
expansion: `(T + D)^k = ∑_w matWord D T w` (`matrix_pow_binomial` at unit
scalars), the all-false word is `T^k`, every other word carries at least one
`D`-factor and is bounded by the rotation engine `trace_matWord_bound` with NO
`sqrt m` and no `m`-factor, and the word sum is transported by
`sum_word_scalars_erase_eq`. -/
theorem abs_trace_add_pow_split_cyclic {n : Type*} [Fintype n] [DecidableEq n]
    (D T : Matrix n n ℝ) {k : ℕ} (hk : 2 ≤ k) :
    |Matrix.trace ((T + D) ^ k) - Matrix.trace (T ^ k)|
      ≤ (‖D‖ + ‖T‖) ^ k - ‖T‖ ^ k := by
  classical
  have hexpand : (T + D) ^ k
      = ∑ w : Fin k → Bool,
          ((1 : ℝ) ^ countTrue w * (1 : ℝ) ^ countFalse w) • matWord D T w := by
    rw [show (T + D : Matrix n n ℝ) = (1 : ℝ) • D + (1 : ℝ) • T from by
      rw [one_smul, one_smul, add_comm]]
    exact matrix_pow_binomial D T 1 1 k
  set ff : Fin k → Bool := fun _ => (false : Bool) with hff
  set f : (Fin k → Bool) → Matrix n n ℝ := fun w =>
    ((1 : ℝ) ^ countTrue w * (1 : ℝ) ^ countFalse w) • matWord D T w with hf
  set E : Finset (Fin k → Bool) := Finset.univ.erase ff with hE
  have hterm0 : f ff = T ^ k := by
    rw [hf]
    show ((1 : ℝ) ^ countTrue (fun _ : Fin k => (false : Bool)) *
        (1 : ℝ) ^ countFalse (fun _ : Fin k => (false : Bool))) •
      matWord D T (fun _ : Fin k => (false : Bool)) = T ^ k
    rw [countTrue_false_fun, countFalse_false_fun, pow_zero, one_mul, one_pow,
      one_smul, matWord_const_false D T k]
  have hsplit : (∑ w ∈ E, f w) + f ff = ∑ w : Fin k → Bool, f w := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin k → Bool))
      (fun w => f w) (Finset.mem_univ ff)
    rw [← hE] at h
    exact h
  have h1 : Matrix.trace ((T + D) ^ k) - Matrix.trace (T ^ k)
      = Matrix.trace (∑ w ∈ E, f w) := by
    rw [hexpand, ← hsplit, hterm0, Matrix.trace_add]
    ring
  have htrsum : Matrix.trace (∑ w ∈ E, f w) = ∑ w ∈ E, Matrix.trace (f w) :=
    Matrix.trace_sum E (fun w => f w)
  have hs1 : |Matrix.trace (∑ w ∈ E, f w)| ≤ ∑ w ∈ E, |Matrix.trace (f w)| := by
    rw [htrsum]
    exact Finset.abs_sum_le_sum_abs (fun w => Matrix.trace (f w)) E
  have heq : (∑ w ∈ E, |Matrix.trace (f w)|)
      = (∑ w ∈ E, |Matrix.trace (matWord D T w)|) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    have hscale : |Matrix.trace (f w)|
        = (1 : ℝ) ^ countTrue w * (1 : ℝ) ^ countFalse w
          * |Matrix.trace (matWord D T w)| := by
      rw [hf]
      simp only [Matrix.trace_smul, smul_eq_mul, abs_mul, abs_pow, abs_one]
    rw [hscale, one_pow, one_mul, one_pow, one_mul]
  have hsum := le_trans (le_of_eq heq) (sum_abs_trace_matWord_le_true D T hk)
  calc |Matrix.trace ((T + D) ^ k) - Matrix.trace (T ^ k)|
      ≤ ∑ w ∈ E, |Matrix.trace (f w)| := by rw [h1]; exact hs1
    _ ≤ (‖D‖ + ‖T‖) ^ k - ‖T‖ ^ k := hsum

/-- Bernoulli corollary: `|tr((T+D)^k) − tr(T^k)| ≤ k ‖D‖_F (‖D‖_F+‖T‖_F)^{k−1}`. -/
theorem abs_trace_add_pow_split_bernoulli {n : Type*} [Fintype n] [DecidableEq n]
    (D T : Matrix n n ℝ) {k : ℕ} (hk : 2 ≤ k) :
    |Matrix.trace ((T + D) ^ k) - Matrix.trace (T ^ k)|
      ≤ (k : ℝ) * ‖D‖ * (‖D‖ + ‖T‖) ^ (k - 1) := by
  refine le_trans (abs_trace_add_pow_split_cyclic D T hk) ?_
  exact bernoulli_pow_split' (by omega) (norm_nonneg _) (norm_nonneg _)

/-! ### The Riesz-side entry bound (uniform over ALL pairs) -/

/-- **Uniform Riesz entry bound.**  Every entry of the quadrature matrix is at
most `S^{ψ−1} B_ω |c|`: the unit kernel vanishes on the diagonal and is
`d^{−ψ} ≤ 1` off it, so `|T i j| ≤ S⁻¹ B_ω |c| S^ψ`. -/
theorem frozenHsmall_rieszEntry_le (m : ℕ) (S psi c B_omega : ℝ)
    (hS : 0 < S) (hpsi0 : 0 ≤ psi)
    (omega : ℝ → ℝ) (homega : ∀ x : ℝ, |omega x| ≤ B_omega) (i j : Fin m) :
    |weightedRieszDiscreteMatrix m S psi c omega i j|
      ≤ S ^ (psi - 1) * B_omega * |c| := by
  have hB0 : 0 ≤ B_omega := le_trans (abs_nonneg (omega 0)) (homega 0)
  have hscale : S ^ (psi - 1) = S ^ psi * ((S : ℝ))⁻¹ := by
    rw [Real.rpow_sub hS psi 1, Real.rpow_one]; ring
  by_cases hd : Nat.dist i.val j.val = 0
  · rw [weightedRieszDiscreteMatrix_apply]
    unfold rankRieszKernel rankRieszUnitKernel
    rw [if_pos hd, mul_zero, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hS.le _) hB0) (abs_nonneg c)
  · have hd1 : 1 ≤ Nat.dist i.val j.val := Nat.one_le_iff_ne_zero.mpr hd
    have hdR : (1 : ℝ) ≤ (Nat.dist i.val j.val : ℝ) := by exact_mod_cast hd1
    have hunit : (Nat.dist i.val j.val : ℝ) ^ (-psi) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hdR (by linarith)
    have hψnn : 0 ≤ S ^ psi := Real.rpow_nonneg hS.le psi
    have hdnn : 0 ≤ (Nat.dist i.val j.val : ℝ) ^ (-psi) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) (-psi)
    rw [weightedRieszDiscreteMatrix_apply]
    unfold rankRieszKernel rankRieszUnitKernel
    rw [if_neg hd, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr hS.le), abs_of_nonneg hψnn, abs_of_nonneg hdnn]
    calc ((S : ℝ))⁻¹ * |omega (rieszCycleGridPoint m i)|
          * ((|c| * S ^ psi) * (Nat.dist i.val j.val : ℝ) ^ (-psi))
        ≤ ((S : ℝ))⁻¹ * B_omega * ((|c| * S ^ psi) * (Nat.dist i.val j.val : ℝ) ^ (-psi)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (homega _) (inv_nonneg.mpr hS.le))
            (mul_nonneg (mul_nonneg (abs_nonneg c) hψnn) hdnn)
      _ ≤ ((S : ℝ))⁻¹ * B_omega * ((|c| * S ^ psi) * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hunit (mul_nonneg (abs_nonneg c) hψnn))
            (mul_nonneg (inv_nonneg.mpr hS.le) hB0)
      _ = S ^ (psi - 1) * B_omega * |c| := by
          rw [mul_one, hscale]; ring

/-! ### Deliverable (1): the near-band entry bounds and class vanishing -/

/-- **Near-band frozen entry bound.**  On a fixed band `d ≤ R` the normalized
frozen entries are `O(S^{ψ−1})` with constant `U * B` from the compactness
bound `frozenQ1_kernel_nearBand_bounded` (`|F i j| ≤ S⁻¹ |u_i| S^ψ B`). -/
theorem frozenHsmall_frozenEntry_near_le
    (p a b M : ℝ) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (n : ℕ) (hn : 0 < n) (δ t : ℝ) (hS : 0 < (n : ℝ) * δ)
    (r : ℕ) (U : ℝ) (hU : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      |actualQ1ChainWeight f r n δ t i| ≤ U)
    (R : ℕ) (B : ℝ) (hB : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      Nat.dist (localWeightActiveIndex n 1 δ t i).val
          (localWeightActiveIndex n 1 δ t j).val ≤ R →
      |actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j|
        ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t) * B)
    (i j : Fin (localWeightActiveSet n 1 δ t).card)
    (hd : Nat.dist (localWeightActiveIndex n 1 δ t i).val
          (localWeightActiveIndex n 1 δ t j).val ≤ R) :
    |actualQ1NormalizedFrozenMatrix f hf r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U * B := by
  have hscale : ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
      = ((n : ℝ) * δ) ^ (2 - 2 * f t) * (((n : ℝ) * δ)⁻¹) := by
    rw [Real.rpow_sub hS (2 - 2 * f t) 1, Real.rpow_one]; ring
  have hFr : actualQ1NormalizedFrozenMatrix f hf r n δ t i j
      = ((n : ℝ) * δ)⁻¹ * (actualQ1ChainWeight f r n δ t i *
          actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j) := rfl
  rw [hFr, abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hS.le)]
  calc ((n : ℝ) * δ)⁻¹ * (|actualQ1ChainWeight f r n δ t i| *
        |actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j|)
      ≤ ((n : ℝ) * δ)⁻¹ * (U * (((n : ℝ) * δ) ^ (2 - 2 * f t) * B)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hU i) (hB i j hd) (abs_nonneg _)
            (by have := hU i; linarith [abs_nonneg (actualQ1ChainWeight f r n δ t i)]))
          (inv_nonneg.mpr hS.le)
    _ = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U * B := by rw [hscale]; ring

/-- **Near-band difference bound.**  On a fixed band `d ≤ R` the frozen-vs-Riesz
entry difference is `O(S^{ψ−1})` with constant `U * B + B_ω |c|`, `c = f t * (2 f t − 1)`. -/
theorem frozenHsmall_nearBandDiff_le
    (p a b M : ℝ) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (n : ℕ) (hn : 0 < n) (δ t : ℝ) (hS : 0 < (n : ℝ) * δ)
    (r : ℕ) (U : ℝ) (hU : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      |actualQ1ChainWeight f r n δ t i| ≤ U)
    (R : ℕ) (B : ℝ) (hB : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      Nat.dist (localWeightActiveIndex n 1 δ t i).val
          (localWeightActiveIndex n 1 δ t j).val ≤ R →
      |actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j|
        ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t) * B)
    (B_omega : ℝ) (hpsi0 : 0 ≤ 2 - 2 * f t)
    (hBω : ∀ x : ℝ, |equivalentKernel r x| ≤ B_omega)
    (i j : Fin (localWeightActiveSet n 1 δ t).card)
    (hd : Nat.dist (localWeightActiveIndex n 1 δ t i).val
          (localWeightActiveIndex n 1 δ t j).val ≤ R) :
    |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
        actualQ1RieszMatrix f r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * (U * B + B_omega * |f t * (2 * f t - 1)|) := by
  have hFr := frozenHsmall_frozenEntry_near_le p a b M f hf hF n hn δ t hS r U hU R B hB
    i j hd
  have hRn : |actualQ1RieszMatrix f r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_omega * |f t * (2 * f t - 1)| :=
    frozenHsmall_rieszEntry_le (localWeightActiveSet n 1 δ t).card ((n : ℝ) * δ)
      (2 - 2 * f t) (f t * (2 * f t - 1)) B_omega hS hpsi0 (equivalentKernel r) hBω i j
  calc |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
        actualQ1RieszMatrix f r n δ t i j|
      ≤ |actualQ1NormalizedFrozenMatrix f hf r n δ t i j|
        + |actualQ1RieszMatrix f r n δ t i j| := abs_le_abs_add
    _ ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * U * B
        + ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * B_omega * |f t * (2 * f t - 1)| := by
        linarith
    _ = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * (U * B + B_omega * |f t * (2 * f t - 1)|) := by
        ring

/-- **Deliverable (1), the class-stratified vanishing (KEY new analytic input).**
Fix a class `d`.  At uniform relative precision `eps` the class-`d` entries of
the NORMALIZED frozen matrix converge to the class value
`S^{ψ−1} u_i * firstIncrementLagCorrelation (f t) d` uniformly over all
class-`d` pairs — the repackaging of `frozenQ1_kernel_class_converges` through
the `S^{-1} u_i` normalization (the `S^ψ` scaling of the kernel cancels the
`S^{-1}` normalization on both sides, so the bound is uniform in `n`). -/
theorem frozenHsmall_class_eps
    (p M a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (η : ℕ → ℝ) (hη0 : Tendsto η atTop (𝓝 0))
    (hmid : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |(midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)) : ℝ) - f t| ≤ η n)
    (r : ℕ) (U : ℝ) (hU : ∀ᶠ n in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U)
    (d : ℕ) :
    ∀ eps > 0, ∀ᶠ n in atTop,
      ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        Nat.dist (localWeightActiveIndex n 1 (δ n) t i).val
          (localWeightActiveIndex n 1 (δ n) t j).val = d →
        |actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j
          - ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)
            * actualQ1ChainWeight f r n (δ n) t i
            * firstIncrementLagCorrelation (f t) (d : ℝ)|
        ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) * U * eps := by
  intro eps heps
  have hclass := frozenQ1_kernel_class_converges a b ha hb f hf hF t ht δ hδpos η
    hη0 hmid d eps heps
  filter_upwards [hclass, hU, hδpos, eventually_gt_atTop (0 : ℕ)]
    with n hclassn hUn hδn hnpos
  have hSnn : (0 : ℝ) < (n : ℝ) * δ n :=
    mul_pos (by exact_mod_cast hnpos : (0 : ℝ) < (n : ℝ)) hδn
  have hscale : ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)
      = ((n : ℝ) * δ n) ^ (2 - 2 * f t) * (((n : ℝ) * δ n)⁻¹) := by
    rw [Real.rpow_sub hSnn (2 - 2 * f t) 1, Real.rpow_one]; ring
  intro i j hdij
  have hkern := hclassn i j hdij
  have hFr : actualQ1NormalizedFrozenMatrix f hf r n (δ n) t i j
      = ((n : ℝ) * δ n)⁻¹ * (actualQ1ChainWeight f r n (δ n) t i *
          actualQ1FrozenApproxKernel f hf n (δ n) t ((n : ℝ) * δ n) i j) := rfl
  have hlim : ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1)
        * actualQ1ChainWeight f r n (δ n) t i
        * firstIncrementLagCorrelation (f t) (d : ℝ)
      = ((n : ℝ) * δ n)⁻¹ * (actualQ1ChainWeight f r n (δ n) t i *
          (((n : ℝ) * δ n) ^ (2 - 2 * f t)
            * firstIncrementLagCorrelation (f t) (d : ℝ))) := by
    rw [hscale]
    ring
  rw [hFr, hlim, ← mul_sub, ← mul_sub, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hSnn.le)]
  calc ((n : ℝ) * δ n)⁻¹ * (|actualQ1ChainWeight f r n (δ n) t i| *
        |actualQ1FrozenApproxKernel f hf n (δ n) t ((n : ℝ) * δ n) i j -
          ((n : ℝ) * δ n) ^ (2 - 2 * f t)
            * firstIncrementLagCorrelation (f t) (d : ℝ)|)
      ≤ ((n : ℝ) * δ n)⁻¹ * (U * (((n : ℝ) * δ n) ^ (2 - 2 * f t) * eps)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hUn i) hkern (abs_nonneg _)
            (by have := hUn i; linarith [abs_nonneg (actualQ1ChainWeight f r n (δ n) t i)]))
          (inv_nonneg.mpr hSnn.le)
    _ = ((n : ℝ) * δ n) ^ (2 - 2 * f t - 1) * U * eps := by rw [hscale]; ring

/-! ### Deliverable (2): the far-band power sum (Riesz side) -/

/-- **Far-band tail, per row (deliverable 2).**  For every row the squared
entry sum of the Riesz quadrature matrix obeys the `2ψ < 1` band power sum
`∑_j |T i j|² ≤ 2 B_ω² c² (S^{ψ−1})² * m^{1−2ψ}/(1−2ψ)`: each integer distance
occurs for at most two columns (`sum_row_dist_le`) and the power sum
`∑_{d < m} d^{−2ψ} ≤ m^{1−2ψ}/(1−2ψ)` converges
(`sum_range_rpow_neg_shift_le`).  The scale atom `(S⁻¹ * S^ψ)²` is
`(S^{ψ−1})²`. -/
theorem frozenHsmall_rieszRowFar_le (m : ℕ) (hm : 0 < m) (S psi c B_omega : ℝ)
    (hS : 0 < S) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (omega : ℝ → ℝ) (homega : ∀ x : ℝ, |omega x| ≤ B_omega) (i : Fin m) :
    (∑ j : Fin m, |weightedRieszDiscreteMatrix m S psi c omega i j| ^ 2)
      ≤ 2 * B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
        * (((m : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi)) := by
  classical
  have hB0 : 0 ≤ B_omega := le_trans (abs_nonneg (omega 0)) (homega 0)
  set f : ℕ → ℝ := fun d => (d : ℝ) ^ (-(2 * psi)) with hfdef
  have hfnn : ∀ d : ℕ, 0 ≤ f d := fun d =>
    Real.rpow_nonneg (Nat.cast_nonneg d) (-(2 * psi))
  have hK0 : 0 ≤ B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2 :=
    mul_nonneg (mul_nonneg (pow_nonneg hB0 2) (sq_nonneg c))
      (pow_nonneg (mul_nonneg (inv_nonneg.mpr hS.le) (Real.rpow_nonneg hS.le psi)) 2)
  -- per-entry bound: |T i j|² ≤ K * f(dist)
  have hentry : ∀ j : Fin m,
      |weightedRieszDiscreteMatrix m S psi c omega i j| ^ 2
        ≤ B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
          * f (Nat.dist i.val j.val) := by
    intro j
    by_cases hd : Nat.dist i.val j.val = 0
    · rw [weightedRieszDiscreteMatrix_apply]
      unfold rankRieszKernel rankRieszUnitKernel
      rw [if_pos hd, mul_zero, mul_zero, abs_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), hd]
      simp only [hfdef, Nat.cast_zero,
        Real.zero_rpow (show (-(2 * psi) : ℝ) ≠ 0 by linarith), mul_zero]
      exact le_refl 0
    · have hd1 : 1 ≤ Nat.dist i.val j.val := Nat.one_le_iff_ne_zero.mpr hd
      have hdR : (1 : ℝ) ≤ (Nat.dist i.val j.val : ℝ) := by exact_mod_cast hd1
      have hdpos : (0 : ℝ) < (Nat.dist i.val j.val : ℝ) := by positivity
      have hψnn : 0 ≤ S ^ psi := Real.rpow_nonneg hS.le psi
      have habsexp : |weightedRieszDiscreteMatrix m S psi c omega i j|
          = ((S : ℝ))⁻¹ * |omega (rieszCycleGridPoint m i)|
            * ((|c| * S ^ psi) * ((Nat.dist i.val j.val : ℝ) ^ (-psi))) := by
        rw [weightedRieszDiscreteMatrix_apply]
        unfold rankRieszKernel rankRieszUnitKernel
        rw [if_neg hd, abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr hS.le), abs_of_nonneg hψnn,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      have hbound : |weightedRieszDiscreteMatrix m S psi c omega i j|
          ≤ ((S : ℝ))⁻¹ * B_omega
            * ((|c| * S ^ psi) * ((Nat.dist i.val j.val : ℝ) ^ (-psi))) := by
        rw [habsexp]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (homega _) (inv_nonneg.mpr hS.le))
          (mul_nonneg (mul_nonneg (abs_nonneg c) hψnn)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have hsq : |weightedRieszDiscreteMatrix m S psi c omega i j| ^ 2
          ≤ (((S : ℝ))⁻¹ * B_omega
              * ((|c| * S ^ psi) * ((Nat.dist i.val j.val : ℝ) ^ (-psi)))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hbound 2
      rw [mul_pow, mul_pow, mul_pow, mul_pow] at hsq
      have hc2 : |c| ^ 2 = c ^ 2 := by
        rcases le_total 0 c with hc | hc
        · rw [abs_of_nonneg hc]
        · rw [abs_of_nonpos hc, neg_pow]; norm_num
      have hsqf : ((Nat.dist i.val j.val : ℝ) ^ (-psi)) ^ 2
          = f (Nat.dist i.val j.val) := by
        show ((Nat.dist i.val j.val : ℝ) ^ (-psi)) ^ 2
            = (Nat.dist i.val j.val : ℝ) ^ (-(2 * psi))
        rw [pow_two, ← Real.rpow_add hdpos (-(psi : ℝ)) (-(psi : ℝ)),
          show (-(psi : ℝ) + -(psi : ℝ)) = -(2 * psi) from by ring]
      rw [hc2, hsqf] at hsq
      have hjoin : ((S : ℝ))⁻¹ ^ 2 * (S ^ psi) ^ 2 = ((S : ℝ)⁻¹ * S ^ psi) ^ 2 := by
        rw [mul_pow]
      have hmon : ((S : ℝ))⁻¹ ^ 2 * B_omega ^ 2
            * ((c ^ 2 * (S ^ psi) ^ 2) * f (Nat.dist i.val j.val))
          = B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
            * f (Nat.dist i.val j.val) := by
        rw [← hjoin]; ring
      exact hsq.trans (le_of_eq hmon)
  -- row stratification and the power sum
  have hstep : (∑ j : Fin m, |weightedRieszDiscreteMatrix m S psi c omega i j| ^ 2)
      ≤ B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
        * (∑ j : Fin m, f (Nat.dist i.val j.val)) := by
    refine le_trans (Finset.sum_le_sum fun j _ => hentry j) ?_
    have heq : (∑ j : Fin m, B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
          * f (Nat.dist i.val j.val))
        = (∑ j : Fin m, f (Nat.dist i.val j.val)
            * (B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2)) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [heq, ← Finset.sum_mul]
    exact le_of_eq (mul_comm (∑ j : Fin m, f (Nat.dist i.val j.val))
      (B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2))
  have hrow := sum_row_dist_le f hfnn i
  have hsum : (∑ d ∈ Finset.range m, f d)
      ≤ ((m : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi) :=
    sum_range_rpow_neg_shift_le (by linarith) hpsi2 m
  have hrow2 : (∑ j : Fin m, f (Nat.dist i.val j.val))
      ≤ 2 * (((m : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi)) :=
    le_trans hrow (mul_le_mul_of_nonneg_left hsum (by norm_num))
  calc (∑ j : Fin m, |weightedRieszDiscreteMatrix m S psi c omega i j| ^ 2)
      ≤ B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
        * (∑ j : Fin m, f (Nat.dist i.val j.val)) := hstep
    _ ≤ B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
        * (2 * (((m : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi))) :=
        mul_le_mul_of_nonneg_left hrow2 hK0
    _ = 2 * B_omega ^ 2 * c ^ 2 * ((S : ℝ)⁻¹ * S ^ psi) ^ 2
        * (((m : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi)) := by ring

/-! ### Deliverable (3): the hsmall assembly (mirror of the Riesz round) -/

/-- **The hsmall assembly (deliverable 3).**  With both trace powers converging
to the common continuum limit `L` (the Riesz side is the LANDED Riesz
quadrature instance, cf. the derivation of `hriesz` inside
`frozenQ1_trace_pow_tendsto_of_farBand`; the frozen side is the same
three-predicate run fed by the class vanishing of `frozenHsmall_class_eps` and
the far-band envelope), the difference of the trace powers is eventually
arbitrarily small — in the EXACT shape consumed as `hsmall` by
`frozenQ1_trace_pow_tendsto_of_farBand`. -/
theorem frozenHsmallMirror
    (p a b M : ℝ) (r : ℕ) (_hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (_hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k)
    (L : ℝ)
    (hFquad : Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop (𝓝 L))
    (hTquad : Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) atTop (𝓝 L)) :
    ∀ eps > 0, ∀ᶠ n in atTop,
      |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| < eps := by
  intro eps heps
  have he2 : (0 : ℝ) < eps / 2 := by linarith
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hFquad (eps / 2) he2
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hTquad (eps / 2) he2
  refine Filter.eventually_atTop.2 ⟨max N1 N2, fun n hn' => ?_⟩
  have hFn := hN1 n (le_trans (le_max_left N1 N2) hn')
  have hTn := hN2 n (le_trans (le_max_right N1 N2) hn')
  have hFa : |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) - L|
      < eps / 2 := by
    rw [Real.dist_eq] at hFn
    linarith
  have hTb : |Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k) - L|
      < eps / 2 := by
    rw [Real.dist_eq] at hTn
    linarith
  have hsplit : |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)|
      ≤ |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) - L|
        + |Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k) - L| := by
    have hring : Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)
        = (Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) - L)
          + (L - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) := by ring
    rw [hring]
    calc |(Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) - L)
            + (L - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k))|
        ≤ |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) - L|
          + |L - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| := abs_add_le_add
      _ = |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k) - L|
          + |Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k) - L| := by
          rw [abs_sub_comm L (Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k))]
  linarith

end Hurst
