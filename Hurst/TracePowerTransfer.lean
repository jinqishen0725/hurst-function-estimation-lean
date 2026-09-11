import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Hurst.MatrixFrobeniusTrace

/-!
# Trace power transfer estimates

Perturbation bounds for traces of matrix powers under the Frobenius norm.
-/

set_option maxHeartbeats 2000000

noncomputable section
open Filter Matrix
open scoped Topology Matrix.Norms.Frobenius
namespace Hurst

variable {n : ℕ}

section NormedRing

variable {R : Type*} [NormedRing R]

/-- A power of `A` multiplied by a fixed matrix: `‖A ^ s * X‖ ≤ ‖A‖ ^ s * ‖X‖`
for every `s`, including `s = 0` (the identity factor is absorbed on the `X` side). -/
theorem norm_pow_left_mul_le (A X : R) :
    ∀ s : ℕ, ‖A ^ s * X‖ ≤ ‖A‖ ^ s * ‖X‖
  | 0 => by simp
  | s + 1 => by
      have h : A ^ (s + 1) * X = A ^ s * (A * X) := by
        rw [pow_succ, mul_assoc]
      calc ‖A ^ (s + 1) * X‖ = ‖A ^ s * (A * X)‖ := by rw [h]
        _ ≤ ‖A‖ ^ s * ‖A * X‖ := norm_pow_left_mul_le A (A * X) s
        _ ≤ ‖A‖ ^ s * (‖A‖ * ‖X‖) :=
            mul_le_mul_of_nonneg_left (norm_mul_le A X) (pow_nonneg (norm_nonneg A) s)
        _ = ‖A‖ ^ (s + 1) * ‖X‖ := by rw [pow_succ]; ring

/-- Multiplication of a fixed matrix by a power: `‖X * A ^ t‖ ≤ ‖X‖ * ‖A‖ ^ t`
for every `t`, including `t = 0`. -/
theorem norm_mul_pow_right_le (X A : R) :
    ∀ t : ℕ, ‖X * A ^ t‖ ≤ ‖X‖ * ‖A‖ ^ t
  | 0 => by simp
  | t + 1 => by
      have h : X * A ^ (t + 1) = X * A ^ t * A := by
        rw [pow_succ, ← mul_assoc]
      calc ‖X * A ^ (t + 1)‖ = ‖X * A ^ t * A‖ := by rw [h]
        _ ≤ ‖X * A ^ t‖ * ‖A‖ := norm_mul_le _ _
        _ ≤ (‖X‖ * ‖A‖ ^ t) * ‖A‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_pow_right_le X A t) (norm_nonneg A)
        _ = ‖X‖ * ‖A‖ ^ (t + 1) := by rw [pow_succ]; ring

end NormedRing

/-- Telescope identity: `A ^ k - B ^ k = ∑_{t < k} A ^ (k - 1 - t) * (A - B) * B ^ t`. -/
theorem matrix_pow_sub_pow_telescope {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (k : ℕ) :
    A ^ k - B ^ k = ∑ t ∈ Finset.range k, A ^ (k - 1 - t) * (A - B) * B ^ t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel]
    have hrec : ∑ t ∈ Finset.range k, A ^ (k - t) * (A - B) * B ^ t
        = A * ∑ t ∈ Finset.range k, A ^ (k - 1 - t) * (A - B) * B ^ t := by
      rw [Matrix.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht' : t < k := Finset.mem_range.mp ht
      have h2 : k - 1 - t + 1 = k - t := by omega
      have h1 : A ^ (k - t) = A * A ^ (k - 1 - t) := by
        rw [← pow_succ', h2]
      rw [h1, mul_assoc, mul_assoc, mul_assoc]
    have hlast : A ^ (k - k) * (A - B) * B ^ k = (A - B) * B ^ k := by
      rw [Nat.sub_self, pow_zero, one_mul]
    have key : A * (A ^ k - B ^ k) + (A - B) * B ^ k = A ^ (k + 1) - B ^ (k + 1) := by
      rw [mul_sub, sub_mul, ← pow_succ' A k, ← pow_succ' B k, sub_add_sub_cancel]
    rw [hrec, hlast]
    rw [← ih]
    exact key.symm

/-- The absolute trace is bounded by `√n` times the Frobenius norm. -/
theorem abs_trace_le_sqrt_card_mul_frobenius (Z : Matrix (Fin n) (Fin n) ℝ) :
    |Matrix.trace Z| ≤ Real.sqrt n * ‖Z‖ := by
  have hnorm : ‖Z‖ = Real.sqrt (∑ i : Fin n, ∑ j : Fin n, |Z i j| ^ 2) := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by simp [Real.norm_eq_abs]
  have h3 : Real.sqrt (∑ i : Fin n, |Z i i| ^ 2)
      ≤ Real.sqrt (∑ i : Fin n, ∑ j : Fin n, |Z i j| ^ 2) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => |Z i j| ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  calc |Matrix.trace Z| = |∑ i : Fin n, Z i i| := by simp [Matrix.trace, Matrix.diag]
    _ ≤ ∑ i : Fin n, |Z i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, (1 * |Z i i|) := by simp
    _ ≤ Real.sqrt (∑ _i : Fin n, (1 : ℝ) ^ 2) * Real.sqrt (∑ i : Fin n, |Z i i| ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => 1) (fun i => |Z i i|)
    _ ≤ Real.sqrt n * Real.sqrt (∑ i : Fin n, ∑ j : Fin n, |Z i j| ^ 2) :=
        mul_le_mul (by simp) h3 (by simp) (Real.sqrt_nonneg _)
    _ = Real.sqrt n * ‖Z‖ := by rw [hnorm]

/-- Scalar estimate: `a ^ (k - 1 - t) * b ^ t ≤ (max a b) ^ (k - 1)` for nonnegative
`a b` and `t < k`. -/
theorem pow_mul_pow_le_max_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k t : ℕ) (ht : t < k) :
    a ^ (k - 1 - t) * b ^ t ≤ (max a b) ^ (k - 1) := by
  have htk : k - 1 - t + t = k - 1 := by omega
  have p1 : a ^ (k - 1 - t) ≤ (max a b) ^ (k - 1 - t) :=
    pow_le_pow_left₀ ha (le_max_left a b) _
  have p2 : b ^ t ≤ (max a b) ^ t := pow_le_pow_left₀ hb (le_max_right a b) t
  calc a ^ (k - 1 - t) * b ^ t
      ≤ (max a b) ^ (k - 1 - t) * (max a b) ^ t :=
        mul_le_mul p1 p2 (pow_nonneg hb t)
          (pow_nonneg (le_trans ha (le_max_left a b)) (k - 1 - t))
    _ = (max a b) ^ (k - 1 - t + t) := (pow_add (max a b) (k - 1 - t) t).symm
    _ = (max a b) ^ (k - 1) := by rw [htk]

/-- Main estimate: perturbing `A` to `B` changes the `k`-th power trace by at most
`√n · k · C ^ (k - 1) · ‖A - B‖_F` where `C` is the larger Frobenius norm.
(The dimension factor `√n` is sharp: it already appears at `k = 1` for `A - B = I`.)
The corresponding statement with `C` an operator norm holds after replacing the
right-hand side by `√n · k · (√n · C) ^ (k - 1) * ‖A - B‖_F`. -/
theorem abs_trace_pow_sub_le (A B : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    |Matrix.trace (A ^ k) - Matrix.trace (B ^ k)|
      ≤ Real.sqrt n * (k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) := by
  have hL : ∀ (s : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ),
      ‖A ^ s * Y‖ ≤ ‖A‖ ^ s * ‖Y‖ := by
    intro s
    induction s with
    | zero => intro Y; simp
    | succ s ih =>
      intro Y
      calc ‖A ^ (s + 1) * Y‖ = ‖A ^ s * (A * Y)‖ := by rw [pow_succ, mul_assoc]
        _ ≤ ‖A‖ ^ s * ‖A * Y‖ := ih (A * Y)
        _ ≤ ‖A‖ ^ s * (‖A‖ * ‖Y‖) :=
            mul_le_mul_of_nonneg_left (Matrix.frobenius_norm_mul A Y)
              (pow_nonneg (norm_nonneg A) s)
        _ = ‖A‖ ^ (s + 1) * ‖Y‖ := by rw [pow_succ]; ring
  have hR : ∀ (Y : Matrix (Fin n) (Fin n) ℝ) (s : ℕ),
      ‖Y * B ^ s‖ ≤ ‖Y‖ * ‖B‖ ^ s := by
    intro Y s
    induction s with
    | zero => simp
    | succ s ih =>
      calc ‖Y * B ^ (s + 1)‖ = ‖Y * B ^ s * B‖ := by rw [pow_succ, ← mul_assoc]
        _ ≤ ‖Y * B ^ s‖ * ‖B‖ := Matrix.frobenius_norm_mul _ _
        _ ≤ (‖Y‖ * ‖B‖ ^ s) * ‖B‖ :=
            mul_le_mul_of_nonneg_right ih (norm_nonneg B)
        _ = ‖Y‖ * ‖B‖ ^ (s + 1) := by rw [pow_succ]; ring
  have hterm : ∀ t ∈ Finset.range k,
      ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖ ≤ (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
    intro t ht
    have hnp : 0 ≤ ‖A‖ ^ (k - 1 - t) := pow_nonneg (norm_nonneg A) (k - 1 - t)
    have e1 : ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖
        ≤ ‖A‖ ^ (k - 1 - t) * (‖A - B‖ * ‖B‖ ^ t) := by
      rw [mul_assoc]
      exact le_trans (hL (k - 1 - t) ((A - B) * B ^ t))
        (mul_le_mul_of_nonneg_left (hR (A - B) t) hnp)
    have e2 : ‖A‖ ^ (k - 1 - t) * (‖A - B‖ * ‖B‖ ^ t)
        ≤ (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
      have h3 : ‖A‖ ^ (k - 1 - t) * (‖A - B‖ * ‖B‖ ^ t)
          = (‖A‖ ^ (k - 1 - t) * ‖B‖ ^ t) * ‖A - B‖ := by
        rw [mul_comm ‖A - B‖ (‖B‖ ^ t), mul_assoc]
      rw [h3]
      exact mul_le_mul_of_nonneg_right
        (pow_mul_pow_le_max_pow ‖A‖ ‖B‖ (norm_nonneg A) (norm_nonneg B) k t
          (Finset.mem_range.mp ht)) (norm_nonneg (A - B))
    exact e1.trans e2
  calc |Matrix.trace (A ^ k) - Matrix.trace (B ^ k)|
      = |Matrix.trace (A ^ k - B ^ k)| := by rw [Matrix.trace_sub]
    _ = |∑ t ∈ Finset.range k,
          Matrix.trace (A ^ (k - 1 - t) * (A - B) * B ^ t)| := by
        rw [matrix_pow_sub_pow_telescope, Matrix.trace_sum]
    _ ≤ ∑ t ∈ Finset.range k,
          |Matrix.trace (A ^ (k - 1 - t) * (A - B) * B ^ t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range k,
          (Real.sqrt n * ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖) :=
        Finset.sum_le_sum fun t _ => abs_trace_le_sqrt_card_mul_frobenius _
    _ = Real.sqrt n * ∑ t ∈ Finset.range k,
          ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.sqrt n * (k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        calc ∑ t ∈ Finset.range k, ‖A ^ (k - 1 - t) * (A - B) * B ^ t‖
            ≤ ∑ t ∈ Finset.range k, ((max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖) :=
              Finset.sum_le_sum hterm
          _ = k * (max ‖A‖ ‖B‖) ^ (k - 1) * ‖A - B‖ := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_assoc]

/-- Convergence corollary: if `A i` and `B i` agree in Frobenius norm asymptotically
and their Frobenius norms are eventually uniformly bounded by `C`, then every fixed
power trace difference tends to zero. -/
theorem tendsto_abs_trace_pow_sub (A B : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (h : Tendsto (fun i ↦ ‖A i - B i‖) atTop (nhds 0))
    (C : ℝ) (hC : ∀ᶠ i in atTop, max ‖A i‖ ‖B i‖ ≤ C) (k : ℕ) :
    Tendsto (fun i ↦ |Matrix.trace ((A i) ^ k) - Matrix.trace ((B i) ^ k)|)
      atTop (nhds 0) := by
  have hg : Tendsto (fun i ↦ Real.sqrt n * (k * C ^ (k - 1)) * ‖A i - B i‖)
      atTop (nhds 0) := by
    simpa using h.const_mul (Real.sqrt n * (k * C ^ (k - 1)))
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hg
  filter_upwards [hC] with i hi
  have hbound : ‖A i‖ ≤ C := le_trans (le_max_left ‖A i‖ ‖B i‖) hi
  calc |Matrix.trace ((A i) ^ k) - Matrix.trace ((B i) ^ k)|
      ≤ Real.sqrt n * (k * (max ‖A i‖ ‖B i‖) ^ (k - 1) * ‖A i - B i‖) :=
        abs_trace_pow_sub_le _ _ _
    _ ≤ Real.sqrt n * (k * C ^ (k - 1) * ‖A i - B i‖) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ?_ (norm_nonneg (A i - B i))) (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_trans (norm_nonneg (A i)) (le_max_left ‖A i‖ ‖B i‖)) hi _)
          (Nat.cast_nonneg k)
    _ = (Real.sqrt n * (k * C ^ (k - 1))) * ‖A i - B i‖ := (mul_assoc _ _ _).symm

end Hurst
