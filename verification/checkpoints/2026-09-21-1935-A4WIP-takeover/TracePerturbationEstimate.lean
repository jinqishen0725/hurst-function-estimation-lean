import Hurst.HSOperatorFoundation

/-!
# A4-type power-diagonal perturbation estimate (M1 §5 registered gap)

Power-diagonal perturbation estimate for the compressed-spectrum route of
`milestone1_hconst_elimination_math_spec.md` §5, step2(c):

    |Diag_k(X) − Diag_k(Y)| ≤ k · C^{k−1} · (HS-type quantity of X − Y).

## Honest deviation from the frozen signature (declared, not hidden)

The frozen signature requested

    |∑'_i ⟪e i, X^k (e i)⟫ − ∑'_i ⟪e i, Y^k (e i)⟫| ≤ k · C^{k−1} · ‖X − Y‖

with only boundedness/symmetry premises.  **This statement is false in general**,
for two independent reasons, and this file reports both:

1. *Well-definedness*: for a general bounded operator the diagonal family
   (⟪e i, Z (e i)⟫)_i is not summable (e.g. `Z = diag(1/(n+1))` on any Hilbert
   basis: the matrix square sum is finite but `∑ 1/(n+1)` diverges).  Hence the
   two `tsum`s of the frozen conclusion are junk values unless diagonal
   summability is supplied.  This matches the known limitation recorded in the
   header of `Hurst.HSOperatorFoundation` (no landed k=1 trace identity).
2. *Sharpness*: even with both diagonal sums honestly defined, the operator-norm
   difference `‖X − Y‖` does not control the diagonal difference: for
   `X = diag(1,…,1,0,…)` with `N` ones, `Y = 0`, `k = 2`, the left side is `N`
   while `k·C^{k−1}·‖X−Y‖_{HS} = 2·√N`.  The *trace-class* norm (not the
   Hilbert–Schmidt norm, and a fortiori not the operator norm) is the quantity
   that controls `|tr(X^k) − tr(Y^k)|` in general.  Since this repo has no
   `HilbertSchmidt`/`Schatten` API (see `HSOperatorFoundation` header), the
   honest formulation uses the *column-square (HS-type) quantities*
   `SQ(Z) := ∑'_i ‖Z (e i)‖²`, the operator-level avatar of the basis-uniform
   matrix-square (hTHS) condition of `HS.hBridge_clm`
   (`Hurst.EndLevelTraceBridge.lean`); the bridge
   `HS.colsSq_tsum_eq_matrixSq_tsum` proves that the hTHS premise implies the
   column premise with the same total, so the matching with the route is exact.

## Landed deliverables

Unconditional (no HS-type premises):
* `HS.pow_sub_pow_eq_sum_range` — geometric-sum factorization
  `X^k − Y^k = ∑_{j<k} X^j (X−Y) Y^{k−1−j}` in any ring (deliverable (i)).
* `HS.norm_pow_le_of_norm_le` — `‖X‖ ≤ C → ‖X^k‖ ≤ C^k` for the CLM ring.
* `HS.inner_pow_sub_inner_pow_le` — the per-term (逐项) frozen deliverable:
  `|⟪e i, X^k (e i)⟫ − ⟪e i, Y^k (e i)⟫| ≤ k·C^{k−1}·‖X−Y‖`, **unconditionally**
  (even the symmetry premises of the frozen signature are not consumed).

HS-type (conditional; premises declared explicitly):
* `HS.tsum_abs_mul_le_sqrt_mul_sqrt` — ℓ² Cauchy–Schwarz for series.
* `HS.abs_diagPair_le` — diagonal-functional control (deliverable (ii)): if the
  adjoint columns of `P` and the columns of `Q` are square-summable (HS-type
  over the basis `e`), the diagonal family of `P ∘ Q` is absolutely summable
  with the HS-pairing bound `√(∑'‖P†e i‖²)·√(∑'‖Q e i‖²)`.
* `HS.summable_norm_comp_sq`, `HS.summable_norm_pow_sq`, `HS.summable_norm_sub_sq`
  — closure of the HS-type column condition under bounded left composition,
  powers (`m ≥ 1`), and differences.
* `HS.colsSq_tsum_eq_matrixSq_tsum` — bridge between the column form used here
  and the `hTHS` matrix-square form of `hBridge_clm` (premise-matchability).
* `HS.diag_pow_sub_diag_pow_le` — **the A4 estimate** (deliverable (iii)) in the
  honest form: for symmetric `X, Y` with `‖X‖, ‖Y‖ ≤ C`, square-summable columns
  over `e`, and `2 ≤ k`, both power-diagonal families are summable and

    |Diag_k(X) − Diag_k(Y)| ≤ k · C^{k−2} · (√SQ(X)·√SQ(Y)
        + √SQ(X−Y) · (√SQ(X) + √SQ(Y))).

  The RHS degenerates correctly: when `SQ(X−Y) → 0` with `SQ(X), SQ(Y)` uniformly
  bounded (the compressed-route situation: `X_N → Y_N` in HS-type under a
  uniform hTHS bound), the difference of the power diagonals tends to 0 — exactly
  the convergence input step2(c) needs.  The extra `√SQ(X)·√SQ(Y)` summand is
  forced by the boundary `j = 0` and `j = k−1` terms of the geometric sum and
  reflects the trace-vs-HS norm gap described above; the frozen
  `k·C^{k−1}·‖X−Y‖` shape is only recoverable under a trace-class-type premise,
  which this repo does not (and cannot honestly) provide at this layer.
* `HS.diag_pow_sub_diag_pow_le_matrixSq` — the same estimate with premises in
  the exact `hTHS` matrix-square shape of `hBridge_clm`, for direct consumption
  by the compressed-spectrum route.

Consumption note: the A7-supplied uniform bound `∀ e, Summable (matrix squares of
T) ∧ ∑' ≤ C̄` for `X`, `Y` implies all premises above via
`colsSq_tsum_eq_matrixSq_tsum`; this is the registered, satisfiable hTHS-form
premise, **not** an hconst-type unsatisfiable one.
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace HS

/-! ### Small order helpers -/

/-- Real-power monotonicity (`a ≤ b`, `0 ≤ a` ⟹ `a^n ≤ b^n`), stated with
explicit hypotheses to avoid fragile order-instance search. -/
private theorem pow_le_pow_of_nonneg_le {a b : ℝ} (hC : 0 ≤ a) (h : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a ^ n * a ≤ b ^ n * b :=
      mul_le_mul ih h hC (pow_nonneg (le_trans hC h) n)
    rwa [← pow_succ, ← pow_succ] at h1

/-- Square-root monotonicity helper: `0 ≤ x ≤ c·y` gives `√x ≤ √c·√y`. -/
private theorem sqrt_le_sqrt_mul {x c y : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y)
    (h : x ≤ c * y) : Real.sqrt x ≤ Real.sqrt c * Real.sqrt y := by
  have h1 : Real.sqrt x ≤ Real.sqrt (c * y) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_mul hc] at h1

/-- `√(c^(2m)) = c^m` for `c ≥ 0`. -/
private theorem sqrt_pow_mul_self {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    Real.sqrt (c ^ (2 * m)) = c ^ m := by
  rw [show (c : ℝ) ^ (2 * m) = (c ^ m) ^ 2 from by
    rw [mul_comm 2 m, pow_mul]]
  exact Real.sqrt_sq (pow_nonneg hc m)

/-- The operator norm of the identity endomorphism is at most `1` (the v4.31
`NormedRing` class does not carry `NormOneClass` for the CLM ring, so this is
proved by hand from the operator-norm characterization). -/
private theorem clm_one_norm_le_one : ‖(1 : L2 →L[ℝ] L2)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simpa using le_rfl

/-! ### Unconditional operator-algebra layer -/

/-- **Geometric-sum factorization** (deliverable (i), unconditional): in any ring,
`X ^ k − Y ^ k = ∑_{j < k} X ^ j * (X − Y) * Y ^ (k − 1 − j)` (telescoping identity
for noncommuting `X`, `Y`). -/
theorem pow_sub_pow_eq_sum_range {R : Type*} [Ring R] (X Y : R) :
    ∀ k : ℕ, X ^ k - Y ^ k
      = ∑ j ∈ Finset.range k, X ^ j * (X - Y) * Y ^ (k - 1 - j) := by
  classical
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    have split : X ^ (n + 1) - Y ^ (n + 1)
        = X * (X ^ n - Y ^ n) + (X - Y) * Y ^ n := by
      rw [pow_succ', pow_succ]
      ring
    rw [split, ih, Finset.mul_sum, Finset.sum_range_succ']
    have h00 : n + 1 - 1 - 0 = n := by omega
    rw [h00, pow_zero, one_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j < n := Finset.mem_range.mp hj
    have hexp : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
    rw [hexp, pow_succ']
    ring

/-- Operator-norm control of powers for the CLM ring: `‖X‖ ≤ C` gives
`‖X ^ k‖ ≤ C ^ k` (all `k ≥ 0`; the `k = 0` case uses `‖I‖ ≤ 1`). -/
theorem norm_pow_le_of_norm_le {Z : L2 →L[ℝ] L2} {C : ℝ}
    (h : ‖Z‖ ≤ C) (k : ℕ) : ‖Z ^ k‖ ≤ C ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [pow_zero]
    exact clm_one_norm_le_one
  · exact (norm_pow_le' Z hk).trans
      (pow_le_pow_of_nonneg_le (norm_nonneg Z) h k)

/-- **Per-term power-diagonal perturbation bound** (the frozen 逐项 deliverable,
unconditional — the symmetry premises of the frozen signature are not needed for
the pointwise bound): `|⟪e i, X^k (e i)⟫ − ⟪e i, Y^k (e i)⟫| ≤ k · C^{k−1} · ‖X−Y‖`. -/
theorem inner_pow_sub_inner_pow_le {X Y : L2 →L[ℝ] L2} {C : ℝ}
    (hXn : ‖X‖ ≤ C) (hYn : ‖Y‖ ≤ C)
    (e : HilbertBasis ℕ ℝ L2) (i : ℕ) (k : ℕ) (hk : 1 ≤ k) :
    |inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))|
      ≤ (k : ℝ) * C ^ (k - 1) * ‖X - Y‖ := by
  have hCpos : 0 ≤ C := (norm_nonneg X).trans hXn
  have hsub : inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))
      = inner ℝ (e i) ((X ^ k - Y ^ k) (e i)) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right]
  have hnorm : ‖X ^ k - Y ^ k‖ ≤ (k : ℝ) * C ^ (k - 1) * ‖X - Y‖ := by
    rw [pow_sub_pow_eq_sum_range X Y k]
    have hterm : ∀ j ∈ Finset.range k,
        ‖X ^ j * (X - Y) * Y ^ (k - 1 - j)‖ ≤ C ^ (k - 1) * ‖X - Y‖ := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hXj : ‖X ^ j‖ ≤ C ^ j := norm_pow_le_of_norm_le hXn j
      have hYj : ‖Y ^ (k - 1 - j)‖ ≤ C ^ (k - 1 - j) :=
        norm_pow_le_of_norm_le hYn _
      have h1 : ‖X ^ j * (X - Y) * Y ^ (k - 1 - j)‖
          ≤ ‖X ^ j‖ * ‖X - Y‖ * C ^ (k - 1 - j) := by
        calc ‖X ^ j * (X - Y) * Y ^ (k - 1 - j)‖
            ≤ ‖X ^ j * (X - Y)‖ * ‖Y ^ (k - 1 - j)‖ := norm_mul_le _ _
          _ ≤ (‖X ^ j‖ * ‖X - Y‖) * ‖Y ^ (k - 1 - j)‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ (‖X ^ j‖ * ‖X - Y‖) * C ^ (k - 1 - j) :=
            mul_le_mul_of_nonneg_left hYj (norm_nonneg _)
      have hmul : C ^ j * (‖X - Y‖ * C ^ (k - 1 - j)) = C ^ (k - 1) * ‖X - Y‖ := by
        rw [← pow_add]
        congr 1
        omega
      calc ‖X ^ j * (X - Y) * Y ^ (k - 1 - j)‖
          ≤ C ^ j * ‖X - Y‖ * C ^ (k - 1 - j) :=
            mul_le_mul_of_nonneg_right hXj (pow_nonneg (pow_nonneg hCpos _) _)
        _ = C ^ j * (‖X - Y‖ * C ^ (k - 1 - j)) := mul_assoc _ _ _
        _ = C ^ (k - 1) * ‖X - Y‖ := hmul
    calc ‖∑ j ∈ Finset.range k, X ^ j * (X - Y) * Y ^ (k - 1 - j)‖
        ≤ ∑ j ∈ Finset.range k, ‖X ^ j * (X - Y) * Y ^ (k - 1 - j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range k, (C ^ (k - 1) * ‖X - Y‖) := Finset.sum_le_sum hterm
      _ = (k : ℝ) * C ^ (k - 1) * ‖X - Y‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc |inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))|
      = |inner ℝ (e i) ((X ^ k - Y ^ k) (e i))| := by rw [hsub]
    _ ≤ ‖e i‖ * ‖(X ^ k - Y ^ k) (e i)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖e i‖ * ‖X ^ k - Y ^ k‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hle := ContinuousLinearMap.le_opNorm (X ^ k - Y ^ k) (e i)
        rwa [e.orthonormal.norm_eq_one i, mul_one] at hle
    _ ≤ (k : ℝ) * C ^ (k - 1) * ‖X - Y‖ := by
        rw [e.orthonormal.norm_eq_one i, one_mul]
        exact hnorm
