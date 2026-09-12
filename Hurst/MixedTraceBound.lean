import Hurst.DiscreteRieszCycleBridge
import Hurst.TruncatedRieszCycleBridge
import Hurst.TruncatedCycleBound
import Hurst.MatrixFrobeniusTrace
import Hurst.EdgeComparison

/-!
# Untruncated uniform entry/Frobenius bounds and mixed trace powers

Two groups of results:

1. Uniform (in `m`, `S`) bounds for the *untruncated* weighted Riesz matrix
   `weightedRieszDiscreteMatrix m S psi c omega` (the `S⁻¹`-normalized matrix
   whose kernel is `c * S ^ psi` times the `Nat.dist`-based unit kernel with
   zero diagonal):
   * every entry is at most `u := S⁻¹ * |c| * B_omega * S ^ psi` in absolute
     value, because the row weight `omega` is bounded by `B_omega` on the grid
     (`[-1,1]`) and the unit kernel is bounded by `1`;
   * hence `‖U‖_Frobenius ≤ m * u` (the `m * u` pattern of the truncated twin
     in `Hurst.TruncatedCycleBound`).

2. Mixed trace bounds: for real matrices `A B` and exponents `a b : ℕ` with
   `a ≥ 1`, `b ≥ 1`,
   `|Matrix.trace (A ^ a * B ^ b)| ≤ ‖A‖_F ^ a * ‖B‖_F ^ b`, and the alternating
   four-factor analogue
   `|tr ((A^a * B^b) * (A^c * B^d))| ≤ ‖A‖_F ^ (a + c) * ‖B‖_F ^ (b + d)`.

   Caveat (documented): exponent `0` genuinely fails for this shape — for
   `a = 0` one would need `|tr X| ≤ ‖X‖_F`, which is false in general (e.g.
   `X = I`, where `|tr I| = n > 1 = ‖I‖_F`; the honest general bound carries a
   `√n` factor).  That is why the hypotheses `1 ≤ a`, `1 ≤ b` are required.
   In the application the mixed regime has `a + b = k ≥ 2` with both factors
   nontrivial; the pure-power case (`a = 0` or `b = 0`) reduces to a trace of a
   single power and is handled by the `√n`-free cyclic-splitting route
   `tr(T ^ k) = tr(T ^ (k - 1) * T)` used in `Hurst.TruncatedCycleBound`.
-/

noncomputable section

open Set Matrix
open scoped Matrix.Norms.Frobenius

namespace Hurst

/-! ### Uniform bounds for the untruncated weighted Riesz matrix -/

/-- Every entry of the untruncated Riesz matrix is bounded by
`S⁻¹ * |c| * B_omega * S ^ psi`, uniformly in the row and column. -/
theorem abs_weightedRieszDiscreteMatrix_le
    (m : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S) (hpsi : 0 < psi) (hB : 0 ≤ B_omega)
    (omega : ℝ → ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (hm : 0 < m) (i j : Fin m) :
    |weightedRieszDiscreteMatrix m S psi c omega i j|
      ≤ (S : ℝ)⁻¹ * |c| * B_omega * S ^ psi := by
  have hgi : rieszCycleGridPoint m i ∈ Icc (-1 : ℝ) 1 := rieszCycleGridPoint_mem_Icc hm i
  have homega : |omega (rieszCycleGridPoint m i)| ≤ B_omega := homegaB _ hgi
  have hunit : |rankRieszUnitKernel psi i j| ≤ 1 :=
    rankRieszUnitKernel_abs_le_one psi hpsi.le i j
  have hSrpow0 : 0 ≤ S ^ psi := Real.rpow_nonneg hS.le psi
  have hkernel : |rankRieszKernel S psi c i j| ≤ |c| * S ^ psi := by
    unfold rankRieszKernel
    rw [abs_mul, abs_mul, abs_of_nonneg hSrpow0]
    calc |c| * S ^ psi * |rankRieszUnitKernel psi i j|
        ≤ |c| * S ^ psi * 1 :=
        mul_le_mul_of_nonneg_left hunit (mul_nonneg (abs_nonneg c) hSrpow0)
      _ = |c| * S ^ psi := by ring
  unfold weightedRieszDiscreteMatrix
  calc |(S : ℝ)⁻¹ * omega (rieszCycleGridPoint m i) * rankRieszKernel S psi c i j|
      = (S : ℝ)⁻¹ * (|omega (rieszCycleGridPoint m i)|
          * |rankRieszKernel S psi c i j|) := by
        rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hS)]
        ring
    _ ≤ (S : ℝ)⁻¹ * (B_omega * (|c| * S ^ psi)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hS.le)
        refine le_trans (mul_le_mul_of_nonneg_left hkernel (abs_nonneg _)) ?_
        exact mul_le_mul_of_nonneg_right homega (mul_nonneg (abs_nonneg c) hSrpow0)
    _ = (S : ℝ)⁻¹ * |c| * B_omega * S ^ psi := by ring

/-- The Frobenius norm of the untruncated Riesz matrix is at most `m * u`
with `u = S⁻¹ * |c| * B_omega * S ^ psi`. -/
theorem frobenius_norm_weightedRieszDiscreteMatrix_le
    (m : ℕ) (S psi c B_omega : ℝ) (hS : 0 < S) (hpsi : 0 < psi) (hB : 0 ≤ B_omega)
    (omega : ℝ → ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (hm : 0 < m) :
    ‖weightedRieszDiscreteMatrix m S psi c omega‖
      ≤ (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi) := by
  have hu0 : 0 ≤ (S : ℝ)⁻¹ * |c| * B_omega * S ^ psi :=
    mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (abs_nonneg c)) hB)
      (Real.rpow_nonneg hS.le psi)
  have hu : ∀ i j : Fin m,
      |weightedRieszDiscreteMatrix m S psi c omega i j|
        ≤ (S : ℝ)⁻¹ * |c| * B_omega * S ^ psi :=
    fun i j => abs_weightedRieszDiscreteMatrix_le m S psi c B_omega hS hpsi hB
      omega homegaB hm i j
  have hsum : ∑ i : Fin m,
      ∑ j : Fin m, ‖weightedRieszDiscreteMatrix m S psi c omega i j‖ ^ (2 : ℝ)
      ≤ ((m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi)) ^ (2 : ℝ) := by
    have hrow : ∀ i : Fin m,
        ∑ j : Fin m,
          ‖weightedRieszDiscreteMatrix m S psi c omega i j‖ ^ (2 : ℝ)
          ≤ (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi) ^ (2 : ℝ) := by
      intro i
      have hterm : ∀ j : Fin m,
          ‖weightedRieszDiscreteMatrix m S psi c omega i j‖ ^ (2 : ℝ)
            ≤ ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi) ^ (2 : ℝ) := by
        intro j
        rw [Real.norm_eq_abs]
        exact Real.rpow_le_rpow (abs_nonneg _) (hu i j) (by norm_num)
      have h := Finset.sum_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hterm j)
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    calc ∑ i : Fin m,
        ∑ j : Fin m,
          ‖weightedRieszDiscreteMatrix m S psi c omega i j‖ ^ (2 : ℝ)
        ≤ ∑ i : Fin m,
            (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi) ^ (2 : ℝ) :=
        Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hrow i)
      _ = (m : ℝ) *
            ((m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi) ^ (2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi)) ^ (2 : ℝ) := by
        rw [Real.mul_rpow (Nat.cast_nonneg m) hu0]
        simp only [Real.rpow_two]
        ring
  rw [Matrix.frobenius_norm_def]
  have hmu0 : 0 ≤ (m : ℝ) * ((S : ℝ)⁻¹ * |c| * B_omega * S ^ psi) :=
    mul_nonneg (Nat.cast_nonneg m) hu0
  refine le_trans (Real.rpow_le_rpow (by positivity) hsum (by norm_num)) ?_
  rw [← Real.rpow_mul hmu0, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by ring, Real.rpow_one]

/-! ### Mixed trace powers -/

/-- For positive exponents the Frobenius norm of a matrix power is bounded by
the power of the Frobenius norm. -/
private theorem frobenius_norm_pow_le' {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ∀ j : ℕ, ‖A ^ (j + 1)‖ ≤ ‖A‖ ^ (j + 1) := by
  intro j
  induction j with
  | zero => rw [pow_one, pow_one]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact le_trans (Matrix.frobenius_norm_mul _ _)
        (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- Nonnegative-exponent form of the power bound (requires `1 ≤ k`; for
`k = 0` the statement `‖A ^ 0‖ ≤ ‖A‖ ^ 0` is the false-by-scale `1 ≤ 1` only
when `‖A‖ ≥ 1`, hence the hypothesis). -/
private theorem frobenius_norm_pow_le_of_one_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (k : ℕ) (hk : 1 ≤ k) : ‖A ^ k‖ ≤ ‖A‖ ^ k := by
  have h := frobenius_norm_pow_le' A (k - 1)
  rwa [show k - 1 + 1 = k by omega] at h

/-- Product of two inequalities on reals (`mul_le_mul'` is unusable here: in
this Mathlib version `MulLeftMono ℝ` does not synthesize). -/
private theorem mul_le_mul_le {x y z w : ℝ} (h1 : x ≤ y) (h2 : z ≤ w)
    (hy : 0 ≤ y) (hz : 0 ≤ z) : x * z ≤ y * w :=
  le_trans (mul_le_mul_of_nonneg_right h1 hz) (mul_le_mul_of_nonneg_left h2 hy)

/-- **Mixed trace bound.**  For real matrices `A B` and exponents `a b : ℕ`
with `a ≥ 1` and `b ≥ 1`:

`|Matrix.trace (A ^ a * B ^ b)| ≤ ‖A‖_F ^ a * ‖B‖_F ^ b`.

The hypothesis `a, b ≥ 1` is essential: the route is
`|tr X Y| ≤ ‖X‖_F ‖Y‖_F` followed by `‖A ^ a‖_F ≤ ‖A‖_F ^ a`, and for an
exponent `0` the factor `A ^ 0 = 1` would contribute a trace `n` against the
bound `1` (the honest zero-exponent bound carries a `√n` factor).  In the
application `a + b = k ≥ 2` with both summands positive; the degenerate
`a = 0` or `b = 0` case is a pure-power trace handled elsewhere (cyclic
splitting `tr(T ^ k) = tr(T ^ (k - 1) * T)`, cf. `Hurst.TruncatedCycleBound`). -/
theorem trace_mixed_frobenius_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Matrix.trace (A ^ a * B ^ b)| ≤ ‖A‖ ^ a * ‖B‖ ^ b := by
  calc |Matrix.trace (A ^ a * B ^ b)| ≤ ‖A ^ a‖ * ‖B ^ b‖ :=
      abs_matrix_trace_mul_le_frobenius _ _
    _ ≤ ‖A‖ ^ a * ‖B‖ ^ b :=
      mul_le_mul_le (frobenius_norm_pow_le_of_one_le A a ha)
        (frobenius_norm_pow_le_of_one_le B b hb)
        (pow_nonneg (norm_nonneg A) a) (norm_nonneg (B ^ b))

/-- **Alternating four-factor trace bound.**  For exponents `a b c d : ℕ` all
at least `1`:

`|tr ((A ^ a * B ^ b) * (A ^ c * B ^ d))| ≤ ‖A‖_F ^ (a + c) * ‖B‖_F ^ (b + d)`.

Up to associativity of matrix multiplication this is the trace of the
alternating product `A ^ a * B ^ b * A ^ c * B ^ d`. -/
theorem trace_alternating_frobenius_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) :
    |Matrix.trace ((A ^ a * B ^ b) * (A ^ c * B ^ d))|
      ≤ ‖A‖ ^ (a + c) * ‖B‖ ^ (b + d) := by
  have hP : ‖A ^ a * B ^ b‖ ≤ ‖A‖ ^ a * ‖B‖ ^ b :=
    le_trans (Matrix.frobenius_norm_mul _ _)
      (mul_le_mul_le (frobenius_norm_pow_le_of_one_le A a ha)
        (frobenius_norm_pow_le_of_one_le B b hb)
        (pow_nonneg (norm_nonneg A) a) (norm_nonneg (B ^ b)))
  have hQ : ‖A ^ c * B ^ d‖ ≤ ‖A‖ ^ c * ‖B‖ ^ d :=
    le_trans (Matrix.frobenius_norm_mul _ _)
      (mul_le_mul_le (frobenius_norm_pow_le_of_one_le A c hc)
        (frobenius_norm_pow_le_of_one_le B d hd)
        (pow_nonneg (norm_nonneg A) c) (norm_nonneg (B ^ d)))
  have hAA : ‖A‖ ^ a * ‖A‖ ^ c ≤ ‖A‖ ^ (a + c) := by rw [pow_add]
  have hBB : ‖B‖ ^ b * ‖B‖ ^ d ≤ ‖B‖ ^ (b + d) := by rw [pow_add]
  calc |Matrix.trace ((A ^ a * B ^ b) * (A ^ c * B ^ d))|
      ≤ ‖A ^ a * B ^ b‖ * ‖A ^ c * B ^ d‖ := abs_matrix_trace_mul_le_frobenius _ _
    _ ≤ (‖A‖ ^ a * ‖B‖ ^ b) * (‖A‖ ^ c * ‖B‖ ^ d) :=
      mul_le_mul_le hP hQ
        (mul_nonneg (pow_nonneg (norm_nonneg A) a) (pow_nonneg (norm_nonneg B) b))
        (norm_nonneg _)
    _ = (‖A‖ ^ a * ‖A‖ ^ c) * (‖B‖ ^ b * ‖B‖ ^ d) := by ring
    _ ≤ ‖A‖ ^ (a + c) * ‖B‖ ^ (b + d) :=
      mul_le_mul_le hAA hBB (pow_nonneg (norm_nonneg A) (a + c))
        (mul_nonneg (pow_nonneg (norm_nonneg B) b) (pow_nonneg (norm_nonneg B) d))

end Hurst
