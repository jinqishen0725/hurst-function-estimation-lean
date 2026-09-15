import Hurst.P7UnknownScale
import Hurst.GridErrorRate
import Hurst.ScaleBandwidth

/-!
# P7 E7: the explicit row-bound split and the composed unknown-scale rate

This module closes the gap left in `Hurst.P7UnknownScale` (its docstring, E7
layer): the explicit split of the conservative row bound `firstStrideLongRowBound`
(file 24 E7) into one polynomially decaying part and the squared grid
covariance error, and the composition of the conditional rate theorem with the
ordinary long-L1 machinery.

## Contents

1. The row-bound split `p7_firstStrideLongRowBound_div_n_le`: for every `b < 1`
   and `1 ≤ d` there is a constant `Cv ≥ 0` (explicit in `A, b, d`) with, for
   EVERY `n ≥ 1`,

   `firstStrideLongRowBound b C A d n / n ≤
      Cv * (n^{-1/2} + n^{-1} + n^{2b-2}) + 32 * gridCovarianceError b C n ^ 2`.

   Term structure: `n^{-1/2}` and `n^{-1}` come from the `⌈√n⌉` (Hölder/pilot)
   part, `n^{2b-2}` from the kernel-tail term `((√n/d)^{2b-2})^2 = (d^{2b-2})^{-2} · n^{2b-2}`,
   and `32 * gridCovarianceError^2` from the covariance-error term
   `2 n (4 E)^2 / n = 32 E^2`.
2. Mesh domination: the polynomial sum and its square root are dominated by
   constant multiples of `n^{-(1-b)}` throughout the long-memory band
   `3/4 ≤ b < 1` (`p7_rpow_sum_le_mesh`, `p7_sqrt_rpow_sum_le_mesh`), and
   `gridCovarianceError b C n ≤ 2 C (1 + log 2n) n^{-(1-b)}`
   (`p7_gridCovarianceError_le_mesh`).
3. The eventual conservative mesh-polynomial bound
   `p7_q1_scale_L1_mesh_eventual_bound`: the RHS of the σ-scale long-L1 bound
   (the square-root variance part with the two row bounds, plus the bias part)
   is eventually `≤ C' (1 + log 2n)^2 n^{-(1-b)}` with an explicit `C'`.
   The square root preserves the rate `(1-b)` because `√(n^{2b-2}) = n^{b-1}`
   and `√(n^{-1/4}) ≤ n^{-(1-b)}` for `b ≥ 3/4`.
4. The composed rate corollary `p7_unknownScale_scale_L1_rate`: under the
   ordinary hypotheses of the σ-scale L1 bound plus the bandwidth window
   `(1-γ)ψ < 1-b`, at the optimal local bandwidth pair `(m, δ) =
   (scaleAverageResolution p, optimalLocalBandwidth p)`,

   `n^{(1-γ)ψ} * E_σ|ŝ_n - log σ²| → 0`,

   by chaining `p7_unknownScale_scale_L1_rate_of_mesh_bound`.

No `sorry`/`axiom`: the split is proved from the definition of
`firstStrideLongRowBound`, and step 4 only composes landed theorems.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

set_option maxHeartbeats 1000000

/-! ### Elementary helpers -/

/-- √-subadditivity: `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private theorem p7_sqrt_add_le (x y : ℝ) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hx := Real.sqrt_nonneg x
  have hy := Real.sqrt_nonneg y
  have h1 : (Real.sqrt x + Real.sqrt y) ^ 2
      = x + y + 2 * Real.sqrt x * Real.sqrt y := by
    rw [pow_two, mul_add, add_mul, add_mul,
      Real.mul_self_sqrt hx0, Real.mul_self_sqrt hy0]
    ring
  have hle : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    rw [h1]
    linarith [mul_nonneg hx hy]
  have h2 := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x + Real.sqrt y)] at h2

/-- The three-term polynomial sum is dominated by `3 * n^{-(1-b)}` throughout
the half-band `1/2 ≤ b < 1` (each exponent `-1/2, -1, 2b-2` is at most
`-(1-b)`). -/
theorem p7_rpow_sum_le_mesh (b : ℝ) (hb2 : 1 / 2 ≤ b) (hb : b < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)
      ≤ 3 * (n : ℝ) ^ (-(1 - b)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have e1 : (n : ℝ) ^ (-1 / 2 : ℝ) ≤ (n : ℝ) ^ (-(1 - b)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e2 : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-(1 - b)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e3 : (n : ℝ) ^ (2 * b - 2) ≤ (n : ℝ) ^ (-(1 - b)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  linarith

/-- The grid covariance error is dominated by the mesh-polynomial form
`2 C (1 + log 2n) n^{-(1-b)}` for `1/2 ≤ b < 1`, `0 ≤ C`. -/
theorem p7_gridCovarianceError_le_mesh (b C : ℝ) (hb2 : 1 / 2 ≤ b) (hb : b < 1)
    (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n) :
    gridCovarianceError b C n
      ≤ 2 * C * (1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (-(1 - b)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have e2 : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-(1 - b)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e3 : (n : ℝ) ^ (2 * b - 2) ≤ (n : ℝ) ^ (-(1 - b)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
    have h1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2n : (1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
    have := Real.log_nonneg h2n
    linarith
  unfold gridCovarianceError
  calc C * (1 + Real.log (2 * (n : ℝ))) *
        ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
      ≤ C * (1 + Real.log (2 * (n : ℝ))) * (2 * (n : ℝ) ^ (-(1 - b))) :=
        mul_le_mul_of_nonneg_left (by linarith [e2, e3]) (mul_nonneg hC hL0)
    _ = 2 * C * (1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (-(1 - b)) := by ring

/-- `√(n^e) = n^{e/2}`. -/
private theorem p7_sqrt_rpow (n : ℕ) (hnR : 0 < (n : ℝ)) (e : ℝ) :
    Real.sqrt ((n : ℝ) ^ e) = (n : ℝ) ^ (e / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnR.le]
  congr 1
  ring

/-- The square root preserves the rate `(1-b)` in the long-memory band:
`√(n^{-1/2}) + √(n^{-1}) + √(n^{2b-2}) ≤ 3 · n^{-(1-b)}` for `3/4 ≤ b < 1`
(the `n^{-1/4}` term is dominated since `1/4 ≥ 1 - b`). -/
theorem p7_sqrt_rpow_sum_le_mesh (b : ℝ) (hb34 : 3 / 4 ≤ b) (hb : b < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)) + Real.sqrt ((n : ℝ) ^ (-1 : ℝ))
        + Real.sqrt ((n : ℝ) ^ (2 * b - 2))
      ≤ 3 * (n : ℝ) ^ (-(1 - b)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have s1 : Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)) = (n : ℝ) ^ (-1 / 4 : ℝ) := by
    rw [p7_sqrt_rpow n hnR]
    congr 1
    ring
  have s2 : Real.sqrt ((n : ℝ) ^ (-1 : ℝ)) = (n : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [p7_sqrt_rpow n hnR]
  have s3 : Real.sqrt ((n : ℝ) ^ (2 * b - 2)) = (n : ℝ) ^ (b - 1) := by
    rw [p7_sqrt_rpow n hnR (2 * b - 2)]
    congr 1
    ring
  have e1 : (n : ℝ) ^ (-1 / 4 : ℝ) ≤ (n : ℝ) ^ (-(1 - b)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e2 : (n : ℝ) ^ (-1 / 2 : ℝ) ≤ (n : ℝ) ^ (-(1 - b)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e3 : (n : ℝ) ^ (b - 1) ≤ (n : ℝ) ^ (-(1 - b)) := by
    have h : (n : ℝ) ^ (b - 1) = (n : ℝ) ^ (-(1 - b)) := by congr 1; ring
    rw [h]
  linarith

/-! ### The row-bound split (file 24 E7) -/

/-- **E7, the explicit row-bound split.**  For `b < 1` and `1 ≤ d` there is a
constant `Cv ≥ 0` (explicit in `A, b, d`) such that for EVERY `n ≥ 1`,

`firstStrideLongRowBound b C A d n / n
  ≤ Cv * (n^{-1/2} + n^{-1} + n^{2b-2}) + 32 * (gridCovarianceError b C n)^2`.

Decay attribution: `n^{-1/2}` from the `⌈√n⌉` (Hölder/pilot) part, `n^{-1}`
from the same term's constant part, `n^{2b-2}` from the kernel tail
`((√n/d)^{2b-2})^2 = (d^{2b-2})^{-2} · n^{2b-2}`, and `32 · gridCov²` from the
covariance-error term `2 n (4 E)^2 / n = 32 E^2`. -/
theorem p7_firstStrideLongRowBound_div_n_le
    (b C A : ℝ) (d : ℕ) (hb : b < 1) (hd : 1 ≤ d) :
    ∃ Cv ≥ 0, ∀ n : ℕ, 1 ≤ n →
      firstStrideLongRowBound b C A d n / (n : ℝ)
        ≤ Cv * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
              + (n : ℝ) ^ (2 * b - 2))
          + 32 * (gridCovarianceError b C n) ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show (0 : ℕ) < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : 0 < (d : ℝ) ^ (2 * b - 2) := Real.rpow_pos_of_pos hdR _
  have hKd0 : 0 < ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 := pow_pos (inv_pos.mpr hdp) 2
  have hA0 : 0 ≤ (4 * A) ^ 2 := sq_nonneg _
  refine ⟨2 * (4 * A) ^ 2 * (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2),
    mul_nonneg (mul_nonneg (by norm_num) hA0) (by linarith [hKd0.le, hd1]),
    fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℕ) < n by omega)
  have hnnz : (n : ℝ) ≠ 0 := hnR.ne'
  -- key power rewrites
  have hsqdiv : (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)
        = (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((-1 / 2 : ℝ) + 1) := by rw [Real.rpow_add hnR]
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num
  have hrinv : (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) = 1 := by
    calc (n : ℝ) ^ (-1 : ℝ) * (n : ℝ)
        = (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((-1 : ℝ) + 1) := by rw [Real.rpow_add hnR]
      _ = 1 := by norm_num
  have hceil : ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ)
      ≤ (n : ℝ) ^ (1 / 2 : ℝ) + 1 + 2 * (d : ℝ) := by
    have hc := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg hnR.le (1 / 2 : ℝ))).le
    have hcast : (((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ))
        = ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) : ℕ) : ℝ) + 2 * (d : ℝ) := by
      push_cast
      ring
    rw [hcast]
    linarith
  have hKdid : ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 = (((d : ℝ) ^ (2 * b - 2)) ^ 2)⁻¹ := by
    rw [inv_pow]
  have hsplitn : 2 * (n : ℝ) ^ (1 / 2 : ℝ) + 4 * (d : ℝ) + 3
      = 2 * ((n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ))
        + ((4 * (d : ℝ) + 3) * ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ))) := by
    rw [hsqdiv, hrinv]
    ring
  have hpow2 : ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2
      = ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 * (n : ℝ) ^ (2 * b - 2) := by
    have hX0 : ((d : ℝ) ^ (2 * b - 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hdp.ne'
    have hdiv := Real.div_rpow (Real.rpow_nonneg hnR.le (1 / 2 : ℝ)) hdR.le
      (2 * b - 2)
    have hinner : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * b - 2) = (n : ℝ) ^ (b - 1) := by
      have h := Real.rpow_mul hnR.le (1 / 2 : ℝ) (2 * b - 2)
      rw [← h]
      congr 1
      ring
    have hsq : ((n : ℝ) ^ (b - 1)) ^ 2 = (n : ℝ) ^ (2 * b - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
      congr 1
      ring
    calc ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2
        = (((n : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * b - 2)
            / ((d : ℝ) ^ (2 * b - 2))) ^ 2 := by rw [hdiv]
      _ = (((n : ℝ) ^ (b - 1)) / ((d : ℝ) ^ (2 * b - 2))) ^ 2 := by rw [hinner]
      _ = (n : ℝ) ^ (2 * b - 2) / ((d : ℝ) ^ (2 * b - 2)) ^ 2 := by
          rw [div_pow, hsq]
      _ = ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 * (n : ℝ) ^ (2 * b - 2) := by
          rw [hKdid, div_eq_inv_mul, mul_comm]
  -- the split
  calc firstStrideLongRowBound b C A d n / (n : ℝ)
      = 2 * (4 * A) ^ 2 *
          (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1) / (n : ℝ) +
        2 * (4 * A) ^ 2 * ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2 +
        2 * (n : ℝ) * (4 * gridCovarianceError b C n) ^ 2 / (n : ℝ) := by
        unfold firstStrideLongRowBound
        field_simp
    _ ≤ 2 * (4 * A) ^ 2 *
          (2 * (n : ℝ) ^ (-1 / 2 : ℝ) + (4 * (d : ℝ) + 3) * (n : ℝ) ^ (-1 : ℝ)) +
        2 * (4 * A) ^ 2 * (((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 * (n : ℝ) ^ (2 * b - 2)) +
        32 * (gridCovarianceError b C n) ^ 2 := by
        have hdiv1 : (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ)
              + 1) / (n : ℝ)
            ≤ 2 * (n : ℝ) ^ (-1 / 2 : ℝ) + (4 * (d : ℝ) + 3) * (n : ℝ) ^ (-1 : ℝ) := by
          apply (div_le_iff₀ hnR).mpr
          have hnum : 2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1
              ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) + 4 * (d : ℝ) + 3 := by linarith
          calc 2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1
              ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) + 4 * (d : ℝ) + 3 := hnum
            _ = 2 * ((n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ))
                  + ((4 * (d : ℝ) + 3) * ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ))) := hsplitn
            _ = (2 * (n : ℝ) ^ (-1 / 2 : ℝ)
                  + (4 * (d : ℝ) + 3) * (n : ℝ) ^ (-1 : ℝ)) * (n : ℝ) := by
                ring
        have hterm1 : 2 * (4 * A) ^ 2 *
            (2 * ((Nat.ceil ((n : ℝ) ^ (1 / 2 : ℝ)) + 2 * d : ℕ) : ℝ) + 1) / (n : ℝ)
            ≤ 2 * (4 * A) ^ 2 *
              (2 * (n : ℝ) ^ (-1 / 2 : ℝ) + (4 * (d : ℝ) + 3) * (n : ℝ) ^ (-1 : ℝ)) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hdiv1 (mul_nonneg (by norm_num) hA0)
        have hterm2 : 2 * (4 * A) ^ 2 *
            ((((n : ℝ) ^ (1 / 2 : ℝ)) / d) ^ (2 * b - 2)) ^ 2
            ≤ 2 * (4 * A) ^ 2 *
              (((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 * (n : ℝ) ^ (2 * b - 2)) := by
          rw [hpow2]
        have hterm3 : 2 * (n : ℝ) * (4 * gridCovarianceError b C n) ^ 2 / (n : ℝ)
            = 32 * (gridCovarianceError b C n) ^ 2 := by
          calc 2 * (n : ℝ) * (4 * gridCovarianceError b C n) ^ 2 / (n : ℝ)
              = (2 * (4 * gridCovarianceError b C n) ^ 2) * (n : ℝ) / (n : ℝ) := by ring
            _ = 2 * (4 * gridCovarianceError b C n) ^ 2 := mul_div_cancel_right₀ _ hnnz
            _ = 32 * (gridCovarianceError b C n) ^ 2 := by ring
        linarith [hterm1, hterm2, hterm3]
    _ ≤ 2 * (4 * A) ^ 2 *
          (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2) *
          ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) +
        32 * (gridCovarianceError b C n) ^ 2 := by
        have hx0 : 0 ≤ (n : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hnR.le _
        have hy0 : 0 ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg hnR.le _
        have hz0 : 0 ≤ (n : ℝ) ^ (2 * b - 2) := Real.rpow_nonneg hnR.le _
        have hc1 : 2 * (4 * A) ^ 2 * 2
            ≤ 2 * (4 * A) ^ 2 * (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hKd0.le, hd1])
            (mul_nonneg (by norm_num) hA0)
        have hc2 : 2 * (4 * A) ^ 2 * (4 * (d : ℝ) + 3)
            ≤ 2 * (4 * A) ^ 2 * (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hKd0.le, hd1])
            (mul_nonneg (by norm_num) hA0)
        have hc3 : 2 * (4 * A) ^ 2 * ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2
            ≤ 2 * (4 * A) ^ 2 * (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hKd0.le])
            (mul_nonneg (by norm_num) hA0)
        have m1 : 2 * (4 * A) ^ 2 * 2 * (n : ℝ) ^ (-1 / 2 : ℝ)
            ≤ 2 * (4 * A) ^ 2 * (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2) *
              (n : ℝ) ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hc1 hx0
        have m2 : 2 * (4 * A) ^ 2 * (4 * (d : ℝ) + 3) * (n : ℝ) ^ (-1 : ℝ)
            ≤ 2 * (4 * A) ^ 2 * (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2) *
              (n : ℝ) ^ (-1 : ℝ) := mul_le_mul_of_nonneg_right hc2 hy0
        have m3 : 2 * (4 * A) ^ 2 * ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2 * (n : ℝ) ^ (2 * b - 2)
            ≤ 2 * (4 * A) ^ 2 * (2 + (4 * (d : ℝ) + 3) + ((d : ℝ) ^ (2 * b - 2))⁻¹ ^ 2) *
              (n : ℝ) ^ (2 * b - 2) := mul_le_mul_of_nonneg_right hc3 hz0
        nlinarith [m1, m2, m3, hx0, hy0, hz0]

/-! ### The eventual mesh-polynomial bound derived from the split -/

/-- **E7, the mesh-polynomial eventual bound.**  The RHS of the σ-scale long-L1
bound (square-root variance part with the two conservative row bounds, plus the
logarithmic bias part) is eventually bounded by
`C' (1 + log 2n)^2 n^{-(1-b)}` with an explicit constant `C'`, throughout the
long-memory band `3/4 ≤ b < 1`.  The square root preserves the rate `(1-b)`
because `√(n^{2b-2}) = n^{b-1}` and `√(n^{-1/2}) = n^{-1/4} ≤ n^{-(1-b)}`.
This derives the boxed bound of file 24 E8 from the explicit row-bound split
`p7_firstStrideLongRowBound_div_n_le` and the `gridCovarianceError` decay
forms. -/
theorem p7_q1_scale_L1_mesh_eventual_bound
    (b C₁ C₂ A₁ A₂ D₁ D₂ E : ℝ)
    (hb : b < 1) (hb34 : 3 / 4 ≤ b)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hE : 0 ≤ E) :
    ∃ C' ≥ 0, ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((4 + 4 / (Real.log 2) ^ 2) * (Real.log n) ^ 2 *
          (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
           D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)) +
        Real.log n * gridCovarianceError b E n
        ≤ C' * (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (-(1 - b)) := by
  obtain ⟨Cv₁, hCv₁₀, hs1⟩ :=
    p7_firstStrideLongRowBound_div_n_le b C₁ A₁ 1 hb (by norm_num)
  obtain ⟨Cv₂, hCv₂₀, hs2⟩ :=
    p7_firstStrideLongRowBound_div_n_le b C₂ A₂ 2 hb (by norm_num)
  set K : ℝ := 4 + 4 / (Real.log 2) ^ 2 with hK_def
  set C' : ℝ := Real.sqrt K *
      ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * 3
        + (Real.sqrt (32 * D₁) * (2 * C₁) + Real.sqrt (32 * D₂) * (2 * C₂)))
    + 2 * E with hC'_def
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hC'0 : 0 ≤ C' := by
    dsimp [C']
    rw [mul_add]
    have tA : 0 ≤ Real.sqrt K * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * 3) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (by norm_num))
    have tB : 0 ≤ Real.sqrt K * (Real.sqrt (32 * D₁) * (2 * C₁)
        + Real.sqrt (32 * D₂) * (2 * C₂)) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith [hC₁]))
          (mul_nonneg (Real.sqrt_nonneg _) (by linarith [hC₂])))
    linarith [tA, tB, hE]
  refine ⟨C', hC'0, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℕ) < n by omega)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set L : ℝ := 1 + Real.log (2 * (n : ℝ)) with hL_def
  set M : ℝ := (n : ℝ) ^ (-(1 - b)) with hM_def
  have hL1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    have h2n : (1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
    have := Real.log_nonneg h2n
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hM0 : 0 ≤ M := Real.rpow_nonneg hnR.le _
  have hE1 : gridCovarianceError b C₁ n ≤ 2 * C₁ * L * M :=
    p7_gridCovarianceError_le_mesh b C₁ (by linarith [hb34]) hb hC₁ n hn
  have hE2 : gridCovarianceError b C₂ n ≤ 2 * C₂ * L * M :=
    p7_gridCovarianceError_le_mesh b C₂ (by linarith [hb34]) hb hC₂ n hn
  -- the two row bounds through the split
  have f1 : D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n
      ≤ D₁ * Cv₁ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
            + (n : ℝ) ^ (2 * b - 2))
        + 32 * (D₁ * (gridCovarianceError b C₁ n) ^ 2) := by
    have hrew : D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n
        = D₁ * (firstStrideLongRowBound b C₁ A₁ 1 n / (n : ℝ)) := by ring
    rw [hrew]
    have hs := hs1 n hn
    linarith [mul_le_mul_of_nonneg_left hs hD₁]
  have f2 : D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n
      ≤ D₂ * Cv₂ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
            + (n : ℝ) ^ (2 * b - 2))
        + 32 * (D₂ * (gridCovarianceError b C₂ n) ^ 2) := by
    have hrew : D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n
        = D₂ * (firstStrideLongRowBound b C₂ A₂ 2 n / (n : ℝ)) := by ring
    rw [hrew]
    have hs := hs2 n hn
    linarith [mul_le_mul_of_nonneg_left hs hD₂]
  -- the square-root chapter: the rate (1-b) survives the square root
  have hS0 : 0 ≤ (n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2) :=
    add_nonneg (add_nonneg (Real.rpow_nonneg hnR.le _) (Real.rpow_nonneg hnR.le _))
      (Real.rpow_nonneg hnR.le _)
  have hDCv₁ : 0 ≤ D₁ * Cv₁ := mul_nonneg hD₁ hCv₁₀
  have hDCv₂ : 0 ≤ D₂ * Cv₂ := mul_nonneg hD₂ hCv₂₀
  have hcov0₁ : 0 ≤ gridCovarianceError b C₁ n :=
    p7_gridCovarianceError_nonneg b C₁ hC₁ n
  have hcov0₂ : 0 ≤ gridCovarianceError b C₂ n :=
    p7_gridCovarianceError_nonneg b C₂ hC₂ n
  have hrow₁ : 0 ≤ firstStrideLongRowBound b C₁ A₁ 1 n := by
    unfold firstStrideLongRowBound gridCovarianceError
    positivity
  have hrow₂ : 0 ≤ firstStrideLongRowBound b C₂ A₂ 2 n := by
    unfold firstStrideLongRowBound gridCovarianceError
    positivity
  have p1₀ : 0 ≤ D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n :=
    mul_nonneg (div_nonneg hD₁ hnR.le) hrow₁
  have p2₀ : 0 ≤ D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n :=
    mul_nonneg (div_nonneg hD₂ hnR.le) hrow₂
  have c1 : Real.sqrt (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n)
      ≤ Real.sqrt (D₁ * Cv₁) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
            + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
        + Real.sqrt (32 * D₁) * gridCovarianceError b C₁ n := by
    have h1 := Real.sqrt_le_sqrt f1
    have h2 := p7_sqrt_add_le (D₁ * Cv₁ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
        + (n : ℝ) ^ (2 * b - 2)))
      (32 * (D₁ * (gridCovarianceError b C₁ n) ^ 2))
      (mul_nonneg hDCv₁ hS0) (mul_nonneg (by norm_num) (mul_nonneg hD₁ (sq_nonneg _)))
    calc Real.sqrt (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n)
        ≤ Real.sqrt (D₁ * Cv₁ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
              + (n : ℝ) ^ (2 * b - 2))
            + 32 * (D₁ * (gridCovarianceError b C₁ n) ^ 2)) := h1
      _ ≤ Real.sqrt (D₁ * Cv₁ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
              + (n : ℝ) ^ (2 * b - 2)))
          + Real.sqrt (32 * (D₁ * (gridCovarianceError b C₁ n) ^ 2)) := h2
      _ = Real.sqrt (D₁ * Cv₁) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
              + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
          + Real.sqrt (32 * D₁) * gridCovarianceError b C₁ n := by
          rw [Real.sqrt_mul hDCv₁,
            show (32 : ℝ) * (D₁ * (gridCovarianceError b C₁ n) ^ 2)
              = (32 * D₁) * (gridCovarianceError b C₁ n) ^ 2 from by ring,
            Real.sqrt_mul (mul_nonneg (by norm_num) hD₁),
            Real.sqrt_sq_eq_abs, abs_of_nonneg hcov0₁]
  have c2 : Real.sqrt (D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)
      ≤ Real.sqrt (D₂ * Cv₂) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
            + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
        + Real.sqrt (32 * D₂) * gridCovarianceError b C₂ n := by
    have h1 := Real.sqrt_le_sqrt f2
    have h2 := p7_sqrt_add_le (D₂ * Cv₂ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
        + (n : ℝ) ^ (2 * b - 2)))
      (32 * (D₂ * (gridCovarianceError b C₂ n) ^ 2))
      (mul_nonneg hDCv₂ hS0) (mul_nonneg (by norm_num) (mul_nonneg hD₂ (sq_nonneg _)))
    calc Real.sqrt (D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)
        ≤ Real.sqrt (D₂ * Cv₂ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
              + (n : ℝ) ^ (2 * b - 2))
            + 32 * (D₂ * (gridCovarianceError b C₂ n) ^ 2)) := h1
      _ ≤ Real.sqrt (D₂ * Cv₂ * ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
              + (n : ℝ) ^ (2 * b - 2)))
          + Real.sqrt (32 * (D₂ * (gridCovarianceError b C₂ n) ^ 2)) := h2
      _ = Real.sqrt (D₂ * Cv₂) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
              + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
          + Real.sqrt (32 * D₂) * gridCovarianceError b C₂ n := by
          rw [Real.sqrt_mul hDCv₂,
            show (32 : ℝ) * (D₂ * (gridCovarianceError b C₂ n) ^ 2)
              = (32 * D₂) * (gridCovarianceError b C₂ n) ^ 2 from by ring,
            Real.sqrt_mul (mul_nonneg (by norm_num) hD₂),
            Real.sqrt_sq_eq_abs, abs_of_nonneg hcov0₂]
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogL : Real.log (n : ℝ) ≤ L := by
    dsimp [L]
    have h2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) hnR.ne']
    have := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    rw [h2n]
    linarith
  have hLle : L ≤ L ^ 2 := by nlinarith [hL1]
  have hLM : L * M ≤ L ^ 2 * M := mul_le_mul_of_nonneg_right hLle hM0
  have hsqrtbound : Real.sqrt (K * (Real.log (n : ℝ)) ^ 2 *
      (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
        D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n))
      ≤ (Real.sqrt K * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * 3
          + (Real.sqrt (32 * D₁) * (2 * C₁)
            + Real.sqrt (32 * D₂) * (2 * C₂)))) * L ^ 2 * M := by
    have hfac : Real.sqrt (K * (Real.log (n : ℝ)) ^ 2 *
        (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
          D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n))
        = Real.sqrt K * Real.log (n : ℝ) * Real.sqrt (D₁ / (n : ℝ) *
            firstStrideLongRowBound b C₁ A₁ 1 n +
            D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n) := by
      rw [Real.sqrt_mul (mul_nonneg hK0 (sq_nonneg (Real.log (n : ℝ)))),
        Real.sqrt_mul hK0, Real.sqrt_sq_eq_abs, abs_of_nonneg hlog0]
    have hSR2 : Real.sqrt (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
        D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)
        ≤ (Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * (3 * M)
          + (Real.sqrt (32 * D₁) * (2 * C₁)
            + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * M) := by
      have hsum := p7_sqrt_add_le
        (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n)
        (D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n) p1₀ p2₀
      have hSS := p7_sqrt_rpow_sum_le_mesh b hb34 hb n hn
      have hsqrtS : Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
            + (n : ℝ) ^ (2 * b - 2)) ≤ 3 * M := by
        have hx : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hnR.le _
        have hy : (0 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg hnR.le _
        have hz : (0 : ℝ) ≤ (n : ℝ) ^ (2 * b - 2) := Real.rpow_nonneg hnR.le _
        have hq1 := p7_sqrt_add_le ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ))
          ((n : ℝ) ^ (2 * b - 2)) (add_nonneg hx hy) hz
        have hq2 := p7_sqrt_add_le ((n : ℝ) ^ (-1 / 2 : ℝ)) ((n : ℝ) ^ (-1 : ℝ)) hx hy
        have h3 := p7_sqrt_rpow_sum_le_mesh b hb34 hb n hn
        rw [hM_def]
        calc Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ)
                + (n : ℝ) ^ (2 * b - 2))
            ≤ Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ) + (n : ℝ) ^ (-1 : ℝ))
              + Real.sqrt ((n : ℝ) ^ (2 * b - 2)) := hq1
          _ ≤ (Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)) + Real.sqrt ((n : ℝ) ^ (-1 : ℝ)))
                + Real.sqrt ((n : ℝ) ^ (2 * b - 2)) := add_le_add hq2 le_rfl
          _ ≤ 3 * (n : ℝ) ^ (-(1 - b)) := h3
      have tSA : Real.sqrt (D₁ * Cv₁) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
            + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
          + Real.sqrt (D₂ * Cv₂) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
            + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
          ≤ (Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * (3 * M) := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_left hsqrtS
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have tCB : Real.sqrt (32 * D₁) * gridCovarianceError b C₁ n
          + Real.sqrt (32 * D₂) * gridCovarianceError b C₂ n
          ≤ (Real.sqrt (32 * D₁) * (2 * C₁)
            + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * M) := by
        calc Real.sqrt (32 * D₁) * gridCovarianceError b C₁ n
            + Real.sqrt (32 * D₂) * gridCovarianceError b C₂ n
            ≤ Real.sqrt (32 * D₁) * (2 * C₁ * L * M)
              + Real.sqrt (32 * D₂) * (2 * C₂ * L * M) :=
                add_le_add (mul_le_mul_of_nonneg_left hE1 (Real.sqrt_nonneg _))
                  (mul_le_mul_of_nonneg_left hE2 (Real.sqrt_nonneg _))
          _ = (Real.sqrt (32 * D₁) * (2 * C₁)
                + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * M) := by ring
      calc Real.sqrt (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
            D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)
          ≤ Real.sqrt (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n)
            + Real.sqrt (D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n) := hsum
        _ ≤ (Real.sqrt (D₁ * Cv₁) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
                + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
              + Real.sqrt (32 * D₁) * gridCovarianceError b C₁ n)
            + (Real.sqrt (D₂ * Cv₂) * Real.sqrt ((n : ℝ) ^ (-1 / 2 : ℝ)
                + (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))
              + Real.sqrt (32 * D₂) * gridCovarianceError b C₂ n) := add_le_add c1 c2
        _ ≤ (Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * (3 * M)
            + (Real.sqrt (32 * D₁) * (2 * C₁)
              + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * M) := by
            linarith [tSA, tCB]
    have hstep1 : Real.sqrt K * Real.log (n : ℝ) * Real.sqrt (D₁ / (n : ℝ) *
          firstStrideLongRowBound b C₁ A₁ 1 n +
          D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)
        ≤ (Real.sqrt K * L) * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * (3 * M)
          + (Real.sqrt (32 * D₁) * (2 * C₁)
            + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * M)) := by
      have tA : 0 ≤ (Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * (3 * M) := by
        refine mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
        positivity
      have tB : 0 ≤ (Real.sqrt (32 * D₁) * (2 * C₁)
          + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * M) := by
        refine mul_nonneg
          (add_nonneg (mul_nonneg (Real.sqrt_nonneg (32 * D₁)) (by linarith [hC₁]))
            (mul_nonneg (Real.sqrt_nonneg (32 * D₂)) (by linarith [hC₂]))) ?_
        nlinarith [hL0, hM0]
      exact le_trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogL (Real.sqrt_nonneg K)) (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left hSR2
          (mul_nonneg (Real.sqrt_nonneg K) hL0))
    have hstep2 : (Real.sqrt K * L) * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂))
          * (3 * M) + (Real.sqrt (32 * D₁) * (2 * C₁)
          + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * M))
        ≤ (Real.sqrt K * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * 3
          + (Real.sqrt (32 * D₁) * (2 * C₁)
            + Real.sqrt (32 * D₂) * (2 * C₂)))) * (L ^ 2 * M) := by
      have hKA : 0 ≤ Real.sqrt K * ((Real.sqrt (D₁ * Cv₁)
          + Real.sqrt (D₂ * Cv₂)) * 3) :=
        mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (by norm_num))
      have hKB : 0 ≤ Real.sqrt K * (Real.sqrt (32 * D₁) * (2 * C₁)
          + Real.sqrt (32 * D₂) * (2 * C₂)) :=
        mul_nonneg (Real.sqrt_nonneg _)
          (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith [hC₁]))
            (mul_nonneg (Real.sqrt_nonneg _) (by linarith [hC₂])))
      have p1 : Real.sqrt K * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * 3)
          * (L * M)
          ≤ Real.sqrt K * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * 3)
            * (L ^ 2 * M) := mul_le_mul_of_nonneg_left hLM hKA
      have p2 : Real.sqrt K * (Real.sqrt (32 * D₁) * (2 * C₁)
          + Real.sqrt (32 * D₂) * (2 * C₂)) * (L * (L * M))
          ≤ Real.sqrt K * (Real.sqrt (32 * D₁) * (2 * C₁)
            + Real.sqrt (32 * D₂) * (2 * C₂)) * (L ^ 2 * M) := by
        rw [show (L : ℝ) * (L * M) = L ^ 2 * M from by ring]
      nlinarith [p1, p2, hM0, hL0]
    rw [hfac]
    exact le_trans hstep1 (le_trans hstep2 (le_of_eq (by ring)))
  -- the bias part
  have hb1 : gridCovarianceError b E n ≤ 2 * E * L * M :=
    p7_gridCovarianceError_le_mesh b E (by linarith [hb34]) hb hE n hn
  have hcovE0 : 0 ≤ gridCovarianceError b E n :=
    p7_gridCovarianceError_nonneg b E hE n
  have hbias : Real.log (n : ℝ) * gridCovarianceError b E n
      ≤ 2 * E * L ^ 2 * M := by
    have h1 : Real.log (n : ℝ) * gridCovarianceError b E n
        ≤ L * (2 * E * L * M) :=
      mul_le_mul hlogL hb1 hcovE0 (by linarith)
    rw [show (2 : ℝ) * E * L ^ 2 * M = L * (2 * E * L * M) from by ring]
    exact h1
  calc Real.sqrt (K * (Real.log (n : ℝ)) ^ 2 *
        (D₁ / (n : ℝ) * firstStrideLongRowBound b C₁ A₁ 1 n +
         D₂ / (n : ℝ) * firstStrideLongRowBound b C₂ A₂ 2 n)) +
      Real.log (n : ℝ) * gridCovarianceError b E n
      ≤ (Real.sqrt K * ((Real.sqrt (D₁ * Cv₁) + Real.sqrt (D₂ * Cv₂)) * 3
            + (Real.sqrt (32 * D₁) * (2 * C₁)
              + Real.sqrt (32 * D₂) * (2 * C₂)))) * L ^ 2 * M
          + 2 * E * L ^ 2 * M := by linarith [hsqrtbound, hbias]
    _ = C' * (1 + Real.log (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ (-(1 - b)) := by
        dsimp [C', L, M]
        ring

/-! ### The composed rate corollary -/

/-- **E7 composed (the target corollary).**  Under the ordinary hypotheses of
the σ-scale long-L1 bound (`p7_q1LogScale_L1_sigma_bound` — weight
reproduction, stride nondegeneracy, Hölder range), the long-memory band
condition `3/4 ≤ b < 1`, and the bandwidth window `(1-γ)ψ < 1-b`, at the
optimal local bandwidth pair `(m, δ) = (scaleAverageResolution p,
optimalLocalBandwidth p)` the normalized scale error satisfies

`n^{(1-γ)ψ} * E_σ|ŝ_n - log σ²| → 0`.

This chains the explicit row-bound split (via
`p7_q1_scale_L1_mesh_eventual_bound`) into the conditional rate theorem
`p7_unknownScale_scale_L1_rate_of_mesh_bound`, discharging its boxed-bound
hypothesis. -/
theorem p7_unknownScale_scale_L1_rate
    (p a b M : ℝ) (r : ℕ) (γ ψ : ℝ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hb34 : 3 / 4 ≤ b) (hab : a ≤ b)
    (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (σ : ℝ) (hσ : σ ≠ 0)
    (hwin : (1 - γ) * ψ < 1 - b)
    (hw : ∀ n m : ℕ, ∀ δ : ℝ, ∑ i, averagedLocalWeights r n 2 m δ i = 1)
    (h₁ : ∀ n : ℕ, ∀ i, ∑ j, commonFirstStrideCoefficients n 1 2 (by norm_num) i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0)
    (h₂ : ∀ n : ℕ, ∀ i, ∑ j, commonFirstStrideCoefficients n 2 2 (by norm_num) i j •
      gridObservationFeatures n (midpointSampleHurst f hf.1 n) j ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 - γ) * ψ) *
      (∫ x, |q1LogScaleEstimator r n (scaleAverageResolution p n)
          (optimalLocalBandwidth p n) x - Real.log (σ ^ 2)|
        ∂featureGaussian
          (fun i => σ • gridObservationFeatures n
            (midpointSampleHurst f hf.1 n) i))) atTop (𝓝 0) := by
  obtain ⟨N₀, hN₀, A₁, hA₁, C₁, hC₁, D₁, hD₁, A₂, hA₂, C₂, hC₂, D₂, hD₂,
      Ew, hEw, N, hN, hsig⟩ :=
    p7_q1LogScale_L1_sigma_bound p a b M r hp ha hb hab hM f hf hF σ hσ hw h₁ h₂
  obtain ⟨C', hC'0, hC'⟩ :=
    p7_q1_scale_L1_mesh_eventual_bound b C₁ C₂ A₁ A₂ D₁ D₂ Ew hb hb34 hC₁ hC₂ hD₁ hD₂ hEw
  refine p7_unknownScale_scale_L1_rate_of_mesh_bound b γ ψ C' hb hC'0 hwin
    (fun n => ∫ x, |q1LogScaleEstimator r n (scaleAverageResolution p n)
        (optimalLocalBandwidth p n) x - Real.log (σ ^ 2)|
      ∂featureGaussian
        (fun i => σ • gridObservationFeatures n
          (midpointSampleHurst f hf.1 n) i))
    (Eventually.of_forall fun n => integral_nonneg fun _ => abs_nonneg _) ?_
  filter_upwards [hC', optimalLocalBandwidth_eventual_design p (N₀ : ℝ) hp,
    eventually_ge_atTop N] with n hmesh hdesign hnN
  obtain ⟨hn1, hδpos, hδhalf, hN₀le, _, hlogn⟩ := hdesign
  obtain ⟨hm, hmd⟩ := scaleAverageResolution_design p n hδpos
  have hsigb := hsig n hnN hlogn (scaleAverageResolution p n) hm
    (optimalLocalBandwidth p n) hδpos hδhalf hN₀le hmd
  exact le_trans hsigb hmesh

end Hurst
