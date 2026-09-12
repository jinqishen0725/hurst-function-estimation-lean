import Hurst.DiscreteRieszCycleBridge
import Hurst.TruncatedRieszCycleBridge
import Hurst.EdgeComparison
import Hurst.TruncatedPairSum
import Hurst.ActualWeightedOperatorNorm
import Hurst.MatrixFrobeniusTrace

/-!
# Uniform boundedness of the truncated cycle value

Uniform (in `m`, `S`) Frobenius-norm control of the `S⁻¹`-normalized truncated
Riesz matrix and, as a consequence, of every cyclic trace power:

* every entry of `weightedTruncatedRieszDiscreteMatrix m R S psi c omega` is at
  most `u := S⁻¹ * |c| * B_omega * (rieszCycleCutoff R)^(-psi)` in absolute
  value (the row's `omega`-factor is bounded by `B_omega` on the grid, and the
  capped negative power `max cutoff t ^ (-psi)` is maximized at the cutoff);
* hence `‖T‖_Frobenius ≤ m * u` (there are `m * m` entries);
* hence `|tr(T ^ k)| ≤ ‖T‖_F * ‖T^(k-1)‖_F ≤ ‖T‖_F ^ k ≤ (m * u) ^ k`.

Main result `truncatedCycleValue_abs_le`: for `2 ≤ k`,

`|weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega|
  ≤ ((m : ℝ) / S) ^ k * (|c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) ^ k`.

Since `rieszCycleCutoff R = (R + 1)⁻¹`, the constant
`|c| * B_omega * (rieszCycleCutoff R) ^ (-psi) = |c| * B_omega * (R+1) ^ psi`
is explicit, finite, and depends only on `psi, R, c, B_omega` (not on `k`).
For fixed `k, R` and any sequence with `m / S → 2` and `m, S → ∞` the bound is
the uniform constant `(2 * |c| * B_omega * (R+1)^psi) ^ k`, which is exactly
the uniform boundedness of the truncated cycle value needed for the telescoped
`|untruncated - truncated|` estimate.

Remark (documented deviation from the originally requested shape): the shape
`(m/S)^(k-2) * (m/S^2) * C^k` would tend to `0` along `m/S → 2, m → ∞`, which
is incompatible with the proved quadrature theorem
(`HasFixedCutoffRieszCycleQuadrature`): along such sequences the truncated
cycle value converges to the fixed-cutoff continuum cyclic integral
`weightedTruncatedRieszCycleIntegral k R psi c omega`, which is nonzero in
general (e.g. `omega ≡ 1`, `c ≠ 0`, `k = 2`).  The honest shape
`(m/S)^k * C^k` (equivalently `(m/S)^(k-2) * (m/S)^2 * C^k`) carries the same
uniform-boundedness content with a fully explicit constant.
-/

noncomputable section

open Set Matrix
open scoped Matrix.Norms.Frobenius

namespace Hurst

/-! ### The uniform entry bound -/

/-- Every entry of the truncated Riesz matrix is bounded by
`S⁻¹ * |c| * B_omega * cutoff^(-psi)`, uniformly in the row and column. -/
theorem abs_weightedTruncatedRieszDiscreteMatrix_le
    (m R : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S) (hpsi : 0 < psi) (hB : 0 ≤ B_omega)
    (omega : ℝ → ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (hm : 0 < m) (i j : Fin m) :
    |weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j|
      ≤ (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) := by
  have hcut : 0 < rieszCycleCutoff R := rieszCycleCutoff_pos R
  have hgi : rieszCycleGridPoint m i ∈ Icc (-1 : ℝ) 1 := rieszCycleGridPoint_mem_Icc hm i
  have homega : |omega (rieszCycleGridPoint m i)| ≤ B_omega := homegaB _ hgi
  have hbase : 0 < max (rieszCycleCutoff R)
      |rieszCycleGridPoint m i - rieszCycleGridPoint m j| :=
    hcut.trans_le (le_max_left _ _)
  have hrpow0 : 0 ≤ (max (rieszCycleCutoff R)
      |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi) :=
    Real.rpow_nonneg hbase.le (-psi)
  have hkey : (max (rieszCycleCutoff R)
      |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi)
      ≤ (rieszCycleCutoff R) ^ (-psi) := max_rpow_neg_le_cutoff hcut hpsi
  unfold weightedTruncatedRieszDiscreteMatrix truncatedRieszKernel
  calc |(S : ℝ)⁻¹ * omega (rieszCycleGridPoint m i) *
        (c * (max (rieszCycleCutoff R)
          |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi))|
      = (S : ℝ)⁻¹ * (|omega (rieszCycleGridPoint m i)| *
        (|c| * (max (rieszCycleCutoff R)
          |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi))) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hS), abs_of_nonneg hrpow0]
        ring
    _ ≤ (S : ℝ)⁻¹ * (B_omega *
        (|c| * (max (rieszCycleCutoff R)
          |rieszCycleGridPoint m i - rieszCycleGridPoint m j|) ^ (-psi))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right homega (mul_nonneg (abs_nonneg c) hrpow0))
          (inv_nonneg.2 hS.le)
    _ ≤ (S : ℝ)⁻¹ * (B_omega * (|c| * (rieszCycleCutoff R) ^ (-psi))) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hS.le)
        refine mul_le_mul_of_nonneg_left ?_ hB
        exact mul_le_mul_of_nonneg_left hkey (abs_nonneg c)
    _ = (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) := by ring

/-! ### Frobenius norm control -/

/-- The Frobenius norm of the truncated Riesz matrix is at most `m * u`. -/
theorem frobenius_norm_weightedTruncatedRieszDiscreteMatrix_le
    (m R : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S) (hpsi : 0 < psi) (hB : 0 ≤ B_omega)
    (omega : ℝ → ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (hm : 0 < m) :
    ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega‖
      ≤ (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) := by
  have hcut : 0 < rieszCycleCutoff R := rieszCycleCutoff_pos R
  have hu0 : 0 ≤ (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) :=
    mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (abs_nonneg c)) hB)
      (Real.rpow_nonneg hcut.le (-psi))
  have hu : ∀ i j : Fin m,
      |weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j|
        ≤ (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) :=
    fun i j => abs_weightedTruncatedRieszDiscreteMatrix_le m R S psi c B_omega hS hpsi hB
      omega homegaB hm i j
  have hsum : ∑ i : Fin m,
      ∑ j : Fin m, ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j‖ ^ (2 : ℝ)
      ≤ ((m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi))) ^ (2 : ℝ) := by
    have hrow : ∀ i : Fin m,
        ∑ j : Fin m,
          ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j‖ ^ (2 : ℝ)
          ≤ (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) ^ (2 : ℝ) := by
      intro i
      have hterm : ∀ j : Fin m,
          ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j‖ ^ (2 : ℝ)
            ≤ ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) ^ (2 : ℝ) := by
        intro j
        rw [Real.norm_eq_abs]
        exact Real.rpow_le_rpow (abs_nonneg _) (hu i j) (by norm_num)
      have h := Finset.sum_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hterm j)
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    calc ∑ i : Fin m,
        ∑ j : Fin m,
          ‖weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j‖ ^ (2 : ℝ)
        ≤ ∑ i : Fin m,
            (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) ^ (2 : ℝ) :=
        Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hrow i)
      _ = (m : ℝ) *
            ((m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) ^ (2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi))) ^ (2 : ℝ) := by
        rw [Real.mul_rpow (Nat.cast_nonneg m) hu0]
        simp only [Real.rpow_two]
        ring
  rw [Matrix.frobenius_norm_def]
  have hmu0 : 0 ≤ (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) :=
    mul_nonneg (Nat.cast_nonneg m) hu0
  refine le_trans (Real.rpow_le_rpow (by positivity) hsum (by norm_num)) ?_
  rw [← Real.rpow_mul hmu0, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by ring, Real.rpow_one]

/-- The Frobenius norm of a positive matrix power is bounded by the power of
the Frobenius norm (for positive exponents). -/
private theorem frobenius_norm_pow_le' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ∀ j : ℕ, ‖A ^ (j + 1)‖ ≤ ‖A‖ ^ (j + 1) := by
  intro j
  induction j with
  | zero => rw [pow_one, pow_one]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact le_trans (Matrix.frobenius_norm_mul _ _)
        (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-! ### The main uniform boundedness theorem -/

/-- **Uniform boundedness of the truncated cycle value.**  For `2 ≤ k`, fixed
`R`, `psi ∈ (0, 1/2)`, bounded `omega` (with bound `B_omega` on `[-1,1]`), and
any `m ≥ 1`, `S > 0`:

`|weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega|
  ≤ ((m : ℝ) / S) ^ k * (|c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) ^ k`.

The constant `|c| * B_omega * (rieszCycleCutoff R) ^ (-psi) = |c| * B_omega *
(R + 1) ^ psi` is explicit and depends only on `psi, R, c, B_omega`; hence for
fixed `k, R` the bound is uniform along any sequence with `m / S → 2` and
`m, S → ∞` (it converges to `(2 * |c| * B_omega * (R+1)^psi) ^ k`). -/
theorem truncatedCycleValue_abs_le (k : ℕ) (hk : 2 ≤ k) (R : ℕ) (psi c B_omega : ℝ)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1) (omega : ℝ → ℝ)
    (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (m : ℕ) (S : ℝ) (hS : 0 < S) (hm : 0 < m) :
    |weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega|
      ≤ (((m : ℝ) / S) * (|c| * B_omega * (rieszCycleCutoff R) ^ (-psi))) ^ k := by
  set T : Matrix (Fin m) (Fin m) ℝ :=
    weightedTruncatedRieszDiscreteMatrix m R S psi c omega with hTdef
  have hB0 : 0 ≤ B_omega := by
    have h : |omega (0 : ℝ)| ≤ B_omega :=
      homegaB 0 (Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩)
    linarith [abs_nonneg (omega (0 : ℝ))]
  have hcut : 0 < rieszCycleCutoff R := rieszCycleCutoff_pos R
  have hu0 : 0 ≤ (S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi) :=
    mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (abs_nonneg c)) hB0)
      (Real.rpow_nonneg hcut.le (-psi))
  have hnorm : ‖T‖ ≤ (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi)) :=
    frobenius_norm_weightedTruncatedRieszDiscreteMatrix_le m R S psi c B_omega hS hpsi1 hB0
      omega homegaB hm
  have hnorm0 : 0 ≤ ‖T‖ := norm_nonneg _
  have hTp : T ^ k = T ^ (k - 1) * T := by
    conv => lhs; rw [← show k - 1 + 1 = k from (by omega), pow_succ]
  calc |weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega|
      = |Matrix.trace (T ^ k)| :=
      by rw [weightedTruncatedRieszDiscreteCycleValue_eq_trace_pow]
    _ = |Matrix.trace (T ^ (k - 1) * T)| := by rw [hTp]
    _ ≤ ‖T ^ (k - 1)‖ * ‖T‖ := abs_matrix_trace_mul_le_frobenius _ _
    _ ≤ ‖T‖ ^ (k - 1) * ‖T‖ := by
        have h := frobenius_norm_pow_le' T (k - 2)
        rw [show (k - 2) + 1 = k - 1 by omega] at h
        exact mul_le_mul_of_nonneg_right h hnorm0
    _ = ‖T‖ ^ k := by
        rw [← pow_succ, show k - 1 + 1 = k from (by omega)]
    _ ≤ ((m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * (rieszCycleCutoff R) ^ (-psi))) ^ k :=
        pow_le_pow_left₀ hnorm0 hnorm k
    _ = (((m : ℝ) / S) * (|c| * B_omega * (rieszCycleCutoff R) ^ (-psi))) ^ k := by
        congr 1
        field_simp

end Hurst
