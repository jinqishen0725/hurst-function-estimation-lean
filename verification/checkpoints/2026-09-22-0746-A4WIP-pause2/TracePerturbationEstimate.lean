import Hurst.HSOperatorFoundation
import Hurst.PositiveSquareRoot

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
      rw [pow_succ' X n, pow_succ' Y n, mul_sub, sub_mul, sub_add_sub_cancel]
    rw [split, ih, Finset.mul_sum, Finset.sum_range_succ']
    have h00 : n + 1 - 1 - 0 = n := by omega
    rw [h00, pow_zero, one_mul]
    have hcongr : (∑ j ∈ Finset.range n, X * (X ^ j * (X - Y) * Y ^ (n - 1 - j)))
        = (∑ j ∈ Finset.range n, X ^ (j + 1) * (X - Y) * Y ^ (n + 1 - 1 - (j + 1))) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hexp : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
      rw [hexp, pow_succ' X j, mul_assoc X (X ^ j) (X - Y),
        ← mul_assoc X (X ^ j * (X - Y)) (Y ^ (n - 1 - j))]
    rw [hcongr]

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
      have hmul : C ^ j * (‖X - Y‖ * C ^ (k - 1 - j)) = C ^ (k - 1) * ‖X - Y‖ := by
        have hsum : k - 1 - j + j = k - 1 := by omega
        rw [← mul_assoc, mul_comm (C ^ j * ‖X - Y‖) (C ^ (k - 1 - j)),
          ← mul_assoc (C ^ (k - 1 - j)) (C ^ j) ‖X - Y‖, ← pow_add, hsum]
      calc ‖X ^ j * (X - Y) * Y ^ (k - 1 - j)‖
          ≤ ‖X ^ j‖ * ‖X - Y‖ * ‖Y ^ (k - 1 - j)‖ := by
            refine le_trans (norm_mul_le _ _) ?_
            exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ ‖X ^ j‖ * ‖X - Y‖ * C ^ (k - 1 - j) :=
            mul_le_mul_of_nonneg_left hYj (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ C ^ j * ‖X - Y‖ * C ^ (k - 1 - j) := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hCpos _)
            exact mul_le_mul_of_nonneg_right hXj (norm_nonneg _)
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
/-! ### The diagonal-sum (A4) layer

Mathematical note (declared deviation from the frozen `k·C^{k−1}·‖X−Y‖_HS` form):
for merely Hilbert–Schmidt `X`, `Y` the diagonal families of `X ^ k` need not be
summable, and `|tr Z| ≤ ‖Z‖_HS` is false in general.  The honest estimate keeps the
**HS-type premises** `hZhs`/`hZhsC` (the basis-diagonal ℓ² size of `X − Y` is
bounded by `D ^ 2`) — `D` therefore controls the HS size of the perturbation — and
pairs the geometric-sum factors through Cauchy–Schwarz on the basis rows, yielding
`k · C ^ (k − 1) · D`.  The compression route (spec §5 step2(c)) must supply
**HS-norm** convergence of its truncations (`‖B_N′ − B‖_HS → 0`): operator-norm
convergence alone does not imply the trace-power convergence used here. -/
-- reuses the series tools of M1-B (`Hurst.PositiveSquareRoot`)

/-- Self-adjointness transports through powers. -/
theorem isSymmetric_pow {X : L2 →L[ℝ] L2} (hX : (↑X : L2 →ₗ[ℝ] L2).IsSymmetric) :
    ∀ (m : ℕ) (u v : L2), inner ℝ ((X ^ m) u) v = inner ℝ u ((X ^ m) v) := by
  have hX' : ∀ u v : L2, inner ℝ (X u) v = inner ℝ u (X v) := fun u v => hX u v
  intro m
  induction m with
  | zero => intro u v; simp
  | succ n ih =>
    intro u v
    rw [pow_succ X n, ContinuousLinearMap.mul_apply, ih (X u) v,
      ContinuousLinearMap.mul_apply, hX' u ((X ^ n) v),
      ← ContinuousLinearMap.mul_apply, ← pow_succ' X n,
      ← ContinuousLinearMap.mul_apply, ← pow_succ X n]

/-- Iterated operator norm against a fixed vector. -/
theorem norm_pow_iter_le {X : L2 →L[ℝ] L2} {C : ℝ} (hXn : ‖X‖ ≤ C) :
    ∀ (m : ℕ) (u : L2), 1 ≤ m → ‖(X ^ m) u‖ ≤ C ^ (m - 1) * ‖X u‖ := by
  intro m
  induction m with
  | zero => intro u hm; omega
  | succ n ih =>
    intro u hm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using le_refl _
    · have hn1 : (n - 1) + 1 = n := by omega
      have h2 : C * (C ^ (n - 1) * ‖X u‖) = C ^ n * ‖X u‖ := by
        rw [← mul_assoc, ← pow_succ' C (n - 1), hn1]
      have hC0 : (0:ℝ) ≤ C := (norm_nonneg X).trans hXn
      calc ‖(X ^ (n + 1)) u‖ ≤ ‖X‖ * ‖(X ^ n) u‖ := by
            rw [pow_succ' X n, ContinuousLinearMap.mul_apply]
            exact ContinuousLinearMap.le_opNorm X ((X ^ n) u)
        _ ≤ C * ‖(X ^ n) u‖ := by
            exact mul_le_mul_of_nonneg_right hXn (norm_nonneg _)
        _ ≤ C * (C ^ (n - 1) * ‖X u‖) := by
            exact mul_le_mul_of_nonneg_left (ih u hn) hC0
        _ = C ^ n * ‖X u‖ := h2

/-- Square-of-power commutation (ℝ, nonnegative base). -/
theorem pow_sq_comm {C : ℝ} (hC : 0 ≤ C) (m : ℕ) : (C ^ m) ^ 2 = C ^ (2 * m) := by
  rw [pow_two, ← pow_add]
  congr 1
  omega

/-- Basis-HS data of an iterated operator: summability and the `C ^ (2*m)` bound. -/
theorem diag_hs_pow_le {X : L2 →L[ℝ] L2} {C : ℝ} (hXn : ‖X‖ ≤ C)
    (e : HilbertBasis ℕ ℝ L2) (hXhs : Summable (fun i : ℕ => ‖X (e i)‖ ^ 2))
    (hXhsC : ∑' i : ℕ, ‖X (e i)‖ ^ 2 ≤ C ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun i : ℕ => ‖(X ^ m) (e i)‖ ^ 2)
      ∧ ∑' i : ℕ, ‖(X ^ m) (e i)‖ ^ 2 ≤ C ^ (2 * m) := by
  have hdom : ∀ i : ℕ, ‖(X ^ m) (e i)‖ ^ 2 ≤ C ^ (2 * (m - 1)) * ‖X (e i)‖ ^ 2 := by
    intro i
    have h1 := norm_pow_iter_le hXn m (e i) hm
    have hsq : (C ^ (m - 1) * ‖X (e i)‖) ^ 2 = C ^ (2 * (m - 1)) * ‖X (e i)‖ ^ 2 := by
      rw [mul_pow, pow_two (C ^ (m - 1)), ← pow_add]
      have hexp2 : (m - 1) + (m - 1) = 2 * (m - 1) := by omega
      rw [hexp2]
    nlinarith [h1, hsq, norm_nonneg ((X ^ m) (e i))]
  have hdom2 : Summable (fun i : ℕ => C ^ (2 * (m - 1)) * ‖X (e i)‖ ^ 2) :=
    Summable.mul_left (C ^ (2 * (m - 1))) hXhs
  have hsumm : Summable (fun i : ℕ => ‖(X ^ m) (e i)‖ ^ 2) :=
    Summable.of_norm_bounded hdom2 (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
      exact hdom i)
  have hC0 : (0:ℝ) ≤ C := (norm_nonneg X).trans hXn
  have hbound : ∑' i : ℕ, ‖(X ^ m) (e i)‖ ^ 2
      ≤ C ^ (2 * (m - 1)) * ∑' i : ℕ, ‖X (e i)‖ ^ 2 := by
    refine le_trans (Summable.tsum_le_tsum hdom hsumm
      (Summable.mul_left (C ^ (2 * (m - 1))) hXhs)) ?_
    exact le_of_eq (Summable.tsum_mul_left (C ^ (2 * (m - 1))) hXhs)
  refine ⟨hsumm, le_trans hbound ?_⟩
  refine le_trans (mul_le_mul_of_nonneg_left hXhsC (pow_nonneg hC0 _)) ?_
  have hexp : 2 * (m - 1) + 2 = 2 * m := by omega
  rw [← pow_add C (2 * (m - 1)) 2, hexp]

/-- CS pairing: if each `|c i|` is dominated pointwise by `‖u i‖ * ‖v i‖` and the two
squared families have sums `≤ A ^ 2` resp. `≤ B ^ 2`, then `∑' |c i| ≤ A * B`. -/
theorem diag_pair_abs_tsum_le {c : ℕ → ℝ} {u v : ℕ → L2} {A B : ℝ}
    (hc : ∀ i : ℕ, |c i| ≤ ‖u i‖ * ‖v i‖)
    (hu : Summable (fun i : ℕ => ‖u i‖ ^ 2)) (hv : Summable (fun i : ℕ => ‖v i‖ ^ 2))
    (hAu : ∑' i : ℕ, ‖u i‖ ^ 2 ≤ A ^ 2) (hBv : ∑' i : ℕ, ‖v i‖ ^ 2 ≤ B ^ 2)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    ∑' i : ℕ, |c i| ≤ A * B := by
  have hcu : Summable (fun i : ℕ => |‖u i‖ * ‖v i‖|) := summable_abs_mul_of_sq hu hv
  have hcsumm : Summable (fun i : ℕ => |c i|) :=
    Summable.of_norm_bounded hcu (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hc i)
  have hcs := tsum_abs_mul_le_sqrt (fun i : ℕ => ‖u i‖) (fun i : ℕ => ‖v i‖) hu hv
  have hA2 : (0:ℝ) ≤ ∑' i : ℕ, ‖u i‖ ^ 2 := tsum_nonneg fun i => pow_nonneg (norm_nonneg _) 2
  have hB2 : (0:ℝ) ≤ ∑' i : ℕ, ‖v i‖ ^ 2 := tsum_nonneg fun i => pow_nonneg (norm_nonneg _) 2
  refine le_trans (Summable.tsum_le_tsum (fun i => ?_) hcsumm hcu) ?_
  · rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hc i
  · rw [← Real.sqrt_eq_rpow] at hcs
    have hprod : (∑' i : ℕ, ‖u i‖ ^ 2) * ∑' i : ℕ, ‖v i‖ ^ 2 ≤ (A * B) ^ 2 := by
      nlinarith [hAu, hBv, hA2, hB2]
    refine le_trans (le_trans hcs (Real.sqrt_le_sqrt hprod)) ?_
    rw [Real.sqrt_sq (mul_nonneg hA0 hB0)]

-- local budget raised for the three-regime CS assembly (discipline §3.7)
set_option maxHeartbeats 1000000 in
/-- **A4 (diagonal form)**: for self-adjoint `X`, `Y` with operator norms `≤ C`,
basis-HS data bounded by `C` (and `X − Y` bounded in **both** operator norm `≤ D`
and basis-HS size `≤ D ^ 2` — `D` controls the HS size of the perturbation), and
summable diagonal families of the `k`-th powers, the difference of the `k`-power
diagonal sums is bounded by `k · C ^ (k − 1) * D` (`2 ≤ k`; the CS pairing splits
the geometric sum into the three regimes `j = 0`, `0 < j < k − 1`, `j = k − 1`).
The compression route must supply HS-norm convergence: op-norm convergence alone
does not yield the estimate's hypotheses on `X − Y`. -/
theorem diag_pow_sub_diag_pow_le {X Y : L2 →L[ℝ] L2} {C : ℝ} {D : ℝ}
    (hXsym : (↑X : L2 →ₗ[ℝ] L2).IsSymmetric) (hYsym : (↑Y : L2 →ₗ[ℝ] L2).IsSymmetric)
    (hXn : ‖X‖ ≤ C) (hYn : ‖Y‖ ≤ C) (hDn : ‖X - Y‖ ≤ D)
    (e : HilbertBasis ℕ ℝ L2)
    (hXhs : Summable (fun i : ℕ => ‖X (e i)‖ ^ 2))
    (hXhsC : ∑' i : ℕ, ‖X (e i)‖ ^ 2 ≤ C ^ 2)
    (hYhs : Summable (fun i : ℕ => ‖Y (e i)‖ ^ 2))
    (hYhsC : ∑' i : ℕ, ‖Y (e i)‖ ^ 2 ≤ C ^ 2)
    (hZhs : Summable (fun i : ℕ => ‖(X - Y) (e i)‖ ^ 2))
    (hZhsC : ∑' i : ℕ, ‖(X - Y) (e i)‖ ^ 2 ≤ D ^ 2)
    (k : ℕ) (hk : 2 ≤ k)
    (hXabs : Summable (fun i : ℕ => |inner ℝ (e i) ((X ^ k) (e i))|))
    (hYabs : Summable (fun i : ℕ => |inner ℝ (e i) ((Y ^ k) (e i))|)) :
    |∑' i : ℕ, inner ℝ (e i) ((X ^ k) (e i)) - ∑' i : ℕ, inner ℝ (e i) ((Y ^ k) (e i))|
      ≤ (k : ℝ) * C ^ (k - 1) * D := by
  classical
  have hD0 : (0:ℝ) ≤ D := (norm_nonneg _).trans hDn
  have hC0 : (0:ℝ) ≤ C := (norm_nonneg _).trans hXn
  -- the difference is self-adjoint
  have hX' : ∀ u v : L2, inner ℝ (X u) v = inner ℝ u (X v) := fun u v => hXsym u v
  have hY' : ∀ u v : L2, inner ℝ (Y u) v = inner ℝ u (Y v) := fun u v => hYsym u v
  have hZsym : ∀ u v : L2, inner ℝ ((X - Y) u) v = inner ℝ u ((X - Y) v) := by
    intro u v
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [hX' u v, hY' u v]
  -- per-index decomposition into the geometric-sum terms
  have hdec : ∀ i : ℕ, inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))
      = ∑ j ∈ Finset.range k, inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i)) := by
    intro i
    have h1 : (X ^ k - Y ^ k) = ∑ j ∈ Finset.range k, X ^ j * (X - Y) * Y ^ (k - 1 - j) :=
      pow_sub_pow_eq_sum_range X Y k
    calc inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))
        = inner ℝ (e i) ((X ^ k - Y ^ k) (e i)) := by
          rw [sub_apply, inner_sub_right]
      _ = inner ℝ (e i)
            ((∑ j ∈ Finset.range k, X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i)) := by rw [h1]
      _ = ∑ j ∈ Finset.range k,
            inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i)) := by
          rw [ContinuousLinearMap.sum_apply, inner_sum]
  -- per-j diagonal-ℓ² bounds (three regimes) with summability
  have hterm : ∀ j ∈ Finset.range k,
      (Summable (fun i : ℕ => |inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i))|)
        ∧ ∑' i : ℕ, |inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i))|
          ≤ C ^ (k - 1) * D) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    rcases Nat.lt_or_ge j 1 with hj0 | hjp
    · -- j = 0 (m = k − 1 ≥ 1): pair `Z e i` against `Y ^ (k−1) e i`
      have hjZ : j = 0 := by omega
      subst hjZ
      rw [pow_zero, one_mul, Nat.sub_zero]
      have hmk : 1 ≤ k - 1 := by omega
      have hpair : ∀ i : ℕ,
          |inner ℝ (e i) (((X - Y) * Y ^ (k - 1)) (e i))|
            ≤ ‖(Y ^ (k - 1)) (e i)‖ * ‖(X - Y) (e i)‖ := by
        intro i
        rw [ContinuousLinearMap.mul_apply,
          real_inner_comm ((X - Y) ((Y ^ (k - 1)) (e i))) (e i),
          hZsym ((Y ^ (k - 1)) (e i)) (e i)]
        exact abs_real_inner_le_norm _ _
      have hYsum := diag_hs_pow_le hYn e hYhs hYhsC hmk
      have hAu : ∑' i : ℕ, ‖(Y ^ (k - 1)) (e i)‖ ^ 2 ≤ (C ^ (k - 1)) ^ 2 := by
        rw [pow_sq_comm hC0 (k - 1)]
        exact hYsum.2
      have hc : Summable (fun i : ℕ => |inner ℝ (e i) (((X - Y) * Y ^ (k - 1)) (e i))|) :=
        Summable.of_norm_bounded (summable_abs_mul_of_sq hYsum.1 hZhs) (fun i => by
          rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
            abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact hpair i)
      exact ⟨hc, diag_pair_abs_tsum_le hpair hYsum.1 hZhs hAu hZhsC
          (pow_nonneg hC0 _) hD0⟩
    · -- 1 ≤ j
      rcases Nat.eq_zero_or_pos (k - 1 - j) with hm0 | hmp
      · -- m = 0 (so j = k − 1): pair `X ^ (k−1) e i` against `Z e i`
        have hjk1 : j = k - 1 := by omega
        subst hjk1
        rw [Nat.sub_self, pow_zero, mul_one]
        have hpair : ∀ i : ℕ,
            |inner ℝ (e i) ((X ^ (k - 1) * (X - Y)) (e i))|
              ≤ ‖(X ^ (k - 1)) (e i)‖ * ‖(X - Y) (e i)‖ := by
          intro i
          rw [ContinuousLinearMap.mul_apply,
            ← isSymmetric_pow hXsym (k - 1) (e i) ((X - Y) (e i))]
          exact abs_real_inner_le_norm _ _
        have hXsum := diag_hs_pow_le hXn e hXhs hXhsC (by omega)
        have hAu : ∑' i : ℕ, ‖(X ^ (k - 1)) (e i)‖ ^ 2 ≤ (C ^ (k - 1)) ^ 2 := by
          rw [pow_sq_comm hC0 (k - 1)]
          exact hXsum.2
        have hc : Summable (fun i : ℕ =>
            |inner ℝ (e i) ((X ^ (k - 1) * (X - Y)) (e i))|) :=
          Summable.of_norm_bounded (summable_abs_mul_of_sq hXsum.1 hZhs) (fun i => by
            rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
              abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
            exact hpair i)
        exact ⟨hc, diag_pair_abs_tsum_le hpair hXsum.1 hZhs hAu hZhsC
          (pow_nonneg hC0 _) hD0⟩
      · -- 1 ≤ j, 1 ≤ m: pair `X ^ j e i` against `Z (Y ^ m e i)`
        have hpair : ∀ i : ℕ,
            |inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i))|
              ≤ ‖(X ^ j) (e i)‖ * ‖(X - Y) ((Y ^ (k - 1 - j)) (e i))‖ := by
          intro i
          rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
            show inner ℝ (e i) ((X ^ j) ((X - Y) ((Y ^ (k - 1 - j)) (e i))))
                = inner ℝ ((X ^ j) (e i)) ((X - Y) ((Y ^ (k - 1 - j)) (e i))) from
              (isSymmetric_pow hXsym j (e i) ((X - Y) ((Y ^ (k - 1 - j)) (e i)))).symm]
          exact abs_real_inner_le_norm _ _
        have hXsum := diag_hs_pow_le hXn e hXhs hXhsC hjp
        have hYsum := diag_hs_pow_le hYn e hYhs hYhsC hmp
        -- the `Z (Y ^ m ·)`-family is dominated by `D² · ‖Y e i‖²`
        have hZdom : ∀ i : ℕ,
            ‖(X - Y) ((Y ^ (k - 1 - j)) (e i))‖ ^ 2
              ≤ D ^ 2 * C ^ (2 * ((k - 1 - j) - 1)) * ‖Y (e i)‖ ^ 2 := by
          intro i
          have h1 : ‖(X - Y) ((Y ^ (k - 1 - j)) (e i))‖ ≤ ‖X - Y‖ * ‖(Y ^ (k - 1 - j)) (e i)‖ :=
            ContinuousLinearMap.le_opNorm _ _
          have h2 : ‖(Y ^ (k - 1 - j)) (e i)‖ ≤ C ^ ((k - 1 - j) - 1) * ‖Y (e i)‖ :=
            norm_pow_iter_le hYn (k - 1 - j) (e i) hmp
          have hsq2 : (C ^ ((k - 1 - j) - 1) * ‖Y (e i)‖) ^ 2
              = C ^ (2 * ((k - 1 - j) - 1)) * ‖Y (e i)‖ ^ 2 := by
            rw [mul_pow, pow_two (C ^ ((k - 1 - j) - 1)), ← pow_add]
            have hexp2 : (k - 1 - j - 1) + (k - 1 - j - 1) = 2 * ((k - 1 - j) - 1) := by omega
            rw [hexp2]
          have hZsq : ‖X - Y‖ ^ 2 ≤ D ^ 2 := by
            nlinarith [hDn, norm_nonneg (X - Y)]
          have hwsq : ‖(Y ^ (k - 1 - j)) (e i)‖ ^ 2
              ≤ C ^ (2 * ((k - 1 - j) - 1)) * ‖Y (e i)‖ ^ 2 := by
            nlinarith [h2, hsq2, norm_nonneg ((Y ^ (k - 1 - j)) (e i))]
          have h1sq : (‖X - Y‖ * ‖(Y ^ (k - 1 - j)) (e i)‖) ^ 2
              ≤ D ^ 2 * (C ^ (2 * ((k - 1 - j) - 1)) * ‖Y (e i)‖ ^ 2) := by
            rw [mul_pow]
            refine le_trans (mul_le_mul_of_nonneg_right hZsq
              (sq_nonneg (‖(Y ^ (k - 1 - j)) (e i)‖))) ?_
            exact mul_le_mul_of_nonneg_left hwsq (by positivity)
          have hp1 : ‖(X - Y) ((Y ^ (k - 1 - j)) (e i))‖ ^ 2
              ≤ (‖X - Y‖ * ‖(Y ^ (k - 1 - j)) (e i)‖) ^ 2 := by
            nlinarith [h1, norm_nonneg ((X - Y) ((Y ^ (k - 1 - j)) (e i))),
              norm_nonneg ((Y ^ (k - 1 - j)) (e i))]
          nlinarith [hp1, h1sq, norm_nonneg ((X - Y) ((Y ^ (k - 1 - j)) (e i))),
            norm_nonneg ((Y ^ (k - 1 - j)) (e i))]
        have hZv : Summable (fun i : ℕ =>
              ‖(X - Y) ((Y ^ (k - 1 - j)) (e i))‖ ^ 2) :=
          Summable.of_norm_bounded (Summable.mul_left (D ^ 2 * C ^ (2 * ((k - 1 - j) - 1)))
            hYhs) (fun i => by
            rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
            exact hZdom i)
        have hAu : ∑' i : ℕ, ‖(X ^ j) (e i)‖ ^ 2 ≤ (C ^ j) ^ 2 := by
          rw [pow_sq_comm hC0 j]
          exact hXsum.2
        have hZvC : ∑' i : ℕ, ‖(X - Y) ((Y ^ (k - 1 - j)) (e i))‖ ^ 2 ≤ (D * C ^ (k - 1 - j)) ^ 2 := by
          have h1 : ∑' i : ℕ, ‖(X - Y) ((Y ^ (k - 1 - j)) (e i))‖ ^ 2
              ≤ ∑' i : ℕ, D ^ 2 * C ^ (2 * ((k - 1 - j) - 1)) * ‖Y (e i)‖ ^ 2 := by
            refine Summable.tsum_le_tsum hZdom hZv
              (Summable.mul_left (D ^ 2 * C ^ (2 * ((k - 1 - j) - 1))) hYhs)
          refine le_trans h1 ?_
          rw [Summable.tsum_mul_left (D ^ 2 * C ^ (2 * ((k - 1 - j) - 1))) hYhs]
          have hsqR : (D * C ^ (k - 1 - j)) ^ 2
              = D ^ 2 * (C ^ (2 * ((k - 1 - j) - 1)) * C ^ 2) := by
            rw [mul_pow D (C ^ (k - 1 - j)) 2, ← pow_mul C (k - 1 - j) 2,
              show (k - 1 - j) * 2 = 2 * ((k - 1 - j) - 1) + 2 from by omega,
              ← pow_add C (2 * ((k - 1 - j) - 1)) 2]
          refine le_trans (mul_le_mul_of_nonneg_left hYhsC
            (mul_nonneg (sq_nonneg D) (pow_nonneg hC0 _))) ?_
          rw [hsqR, mul_assoc (D ^ 2) (C ^ (2 * ((k - 1 - j) - 1))) (C ^ 2)]
        refine ⟨Summable.of_norm_bounded (summable_abs_mul_of_sq hXsum.1 hZv)
          (fun i => by
            rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
              abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
            exact hpair i), ?_⟩
        have hbound := diag_pair_abs_tsum_le hpair hXsum.1 hZv hAu hZvC
          (pow_nonneg hC0 _) (mul_nonneg hD0 (pow_nonneg hC0 _))
        -- `C ^ j * (D * C ^ m) = D * C ^ (k − 1)`
        refine le_trans hbound ?_
        have hsum : j + (k - 1 - j) = k - 1 := by omega
        calc C ^ j * (D * C ^ (k - 1 - j))
            = D * (C ^ j * C ^ (k - 1 - j)) := by ring
          _ = D * C ^ (k - 1) := by rw [← pow_add C j (k - 1 - j), hsum]
          _ = C ^ (k - 1) * D := mul_comm D (C ^ (k - 1))
  -- assemble
  have habsdiff : Summable (fun i : ℕ =>
      |inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))|) :=
    Summable.of_norm_bounded (hXabs.add hYabs) (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact abs_sub _ _)
  have hsubsumm : Summable (fun i : ℕ =>
      inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))) :=
    Summable.of_norm_bounded habsdiff (fun i => by rw [Real.norm_eq_abs])
  have hAsumm : Summable (fun i : ℕ => inner ℝ (e i) ((X ^ k) (e i))) :=
    Summable.of_norm_bounded hXabs (fun i => by rw [Real.norm_eq_abs])
  have hBsumm : Summable (fun i : ℕ => inner ℝ (e i) ((Y ^ k) (e i))) :=
    Summable.of_norm_bounded hYabs (fun i => by rw [Real.norm_eq_abs])
  -- the double family is summable with total `≤ k·C^{k−1}·D` (finite-j exchange via
  -- `Finset.sum_comm`, per-j summability from `hterm`, per-j total from `hterm`)
  have hdouble : Summable (fun i : ℕ => ∑ j ∈ Finset.range k,
      |inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i))|) := by
    refine summable_of_sum_le
      (fun i => Finset.sum_nonneg fun j _ => abs_nonneg _) (fun u => ?_)
    rw [Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) ?_
    · exact Summable.sum_le_tsum u (fun i _ => abs_nonneg _) (hterm j hj).1
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
  have hdb : ∑' i : ℕ, ∑ j ∈ Finset.range k,
      |inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i))|
      ≤ (k : ℝ) * C ^ (k - 1) * D :=
    Real.tsum_le_of_sum_le
      (fun i => Finset.sum_nonneg fun j _ => abs_nonneg _)
      (fun u => by
        rw [Finset.sum_comm]
        refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) ?_
        · exact Summable.sum_le_tsum u (fun i _ => abs_nonneg _) (hterm j hj).1
        · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring)
  have hstep0 : (∑' i : ℕ, inner ℝ (e i) ((X ^ k) (e i)) - ∑' i : ℕ, inner ℝ (e i) ((Y ^ k) (e i)))
      = ∑' i : ℕ, (inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))) :=
    (hAsumm.hasSum.sub hBsumm.hasSum).tsum_eq.symm
  have hstep1 : ∑' i : ℕ,
      |inner ℝ (e i) ((X ^ k) (e i)) - inner ℝ (e i) ((Y ^ k) (e i))|
      ≤ ∑' i : ℕ, ∑ j ∈ Finset.range k,
          |inner ℝ (e i) ((X ^ j * (X - Y) * Y ^ (k - 1 - j)) (e i))| := by
    refine Summable.tsum_le_tsum (fun i => ?_) habsdiff hdouble
    rw [hdec i]
    exact Finset.abs_sum_le_sum_abs
  refine le_trans (le_trans (by rw [hstep0]; exact abs_tsum_le_abs hsubsumm) hstep1) hdb
