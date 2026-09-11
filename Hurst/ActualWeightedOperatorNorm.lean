import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Normed

/-!
# Operator norm bounds by absolute row sums

Stage 1 (generic): the `L∞` operator norm of a real matrix is exactly the
maximum absolute row sum, together with the induced `mulVec` bound and
entrywise corollaries.

Stage 2 (actual model): a uniform-in-time bound on the row-sum operator norm
of the actual long-memory weighted matrices, derived from weight-energy
bounds and correlation bounds.
-/

open scoped NNReal

namespace Hurst

/-! ## Stage 1: the row-sum operator norm -/

section RowSumNorm

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Row-sum operator norm.** The `L∞` operator norm of a real matrix, i.e.
the norm attached to `Matrix.linftyOpSeminormedAddCommGroup`, re-exposed as an
explicit definition. -/
noncomputable def rowSumOpNorm (A : Matrix m n ℝ) : ℝ :=
  @Norm.norm (Matrix m n ℝ)
    (Matrix.linftyOpSeminormedAddCommGroup (m := m) (n := n) (α := ℝ)).toNorm A

/-- The normed-group (`NormedAddCommGroup`) presentation of the same `L∞`
operator norm computes to the same row-sum norm. -/
theorem norm_linftyOp_eq_rowSumOpNorm (A : Matrix m n ℝ) :
    @Norm.norm (Matrix m n ℝ)
      (Matrix.linftyOpNormedAddCommGroup (m := m) (n := n) (α := ℝ)).toNorm A = rowSumOpNorm A :=
  rfl

omit [Fintype m] in
private theorem row_coe (A : Matrix m n ℝ) (i : m) :
    ((∑ j, ‖A i j‖₊ : ℝ≥0) : ℝ) = ∑ j, |A i j| := by
  rw [NNReal.coe_sum]
  exact Finset.sum_congr rfl fun j _ => by simp

omit [Fintype m] in
private theorem row_nnreal (A : Matrix m n ℝ) (i : m) :
    (∑ j, ‖A i j‖₊ : ℝ≥0) = Real.toNNReal (∑ j, |A i j|) := by
  refine NNReal.eq ?_
  rw [row_coe A i, Real.coe_toNNReal _ (Finset.sum_nonneg fun j _ => abs_nonneg _)]

/-- The `L∞` operator norm of a real matrix is the maximum absolute row sum. -/
theorem rowSumOpNorm_eq_sup (A : Matrix m n ℝ) :
    rowSumOpNorm A =
      ((Finset.univ : Finset m).sup fun i => Real.toNNReal (∑ j, |A i j|) : ℝ≥0) := by
  simp only [rowSumOpNorm, Matrix.linfty_opNorm_def]
  exact congrArg (fun s : ℝ≥0 => (s : ℝ)) (Finset.sup_congr rfl fun i _ => row_nnreal A i)

/-- Every absolute row sum is bounded by the row-sum operator norm. -/
theorem rowSumOpNorm_row_le (A : Matrix m n ℝ) (i : m) :
    ∑ j, |A i j| ≤ rowSumOpNorm A := by
  rw [rowSumOpNorm_eq_sup]
  conv => rhs; rw [Finset.sup_congr rfl fun k _ => (row_nnreal A k).symm]
  conv => lhs; rw [← row_coe A i]
  exact NNReal.coe_le_coe.2
    (Finset.le_sup (f := fun k => ∑ j, ‖A k j‖₊) (Finset.mem_univ i))

/-- The row-sum operator norm is nonnegative. -/
theorem rowSumOpNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ rowSumOpNorm A := by
  rw [rowSumOpNorm_eq_sup]
  exact NNReal.coe_nonneg _

/-- The row-sum operator norm is at most `C` iff every absolute row sum is. -/
theorem rowSumOpNorm_le_iff {C : ℝ} (hC : 0 ≤ C) (A : Matrix m n ℝ) :
    rowSumOpNorm A ≤ C ↔ ∀ i, ∑ j, |A i j| ≤ C := by
  rw [rowSumOpNorm_eq_sup]
  constructor
  · intro h
    have h' : ((Finset.univ : Finset m).sup fun k => Real.toNNReal (∑ j, |A k j|) : ℝ≥0) ≤
        Real.toNNReal C := NNReal.coe_le_coe.mp (by rwa [Real.coe_toNNReal C hC])
    exact fun i =>
      Real.toNNReal_le_toNNReal_iff hC |>.1 ((Finset.le_sup (Finset.mem_univ i)).trans h')
  · intro h
    rw [← Real.coe_toNNReal C hC]
    exact NNReal.coe_le_coe.mpr
      (Finset.sup_le fun k _ => Real.toNNReal_le_toNNReal_iff hC |>.2 (h k))

/-- A bound by a uniform row bound, on Mathlib's `L∞` operator norm directly. -/
theorem norm_rowSumOpNorm_le {C : ℝ} (hC : 0 ≤ C) (A : Matrix m n ℝ)
    (h : ∀ i, ∑ j, |A i j| ≤ C) :
    @Norm.norm (Matrix m n ℝ)
      (Matrix.linftyOpSeminormedAddCommGroup (m := m) (n := n) (α := ℝ)).toNorm A ≤ C :=
  show rowSumOpNorm A ≤ C from (rowSumOpNorm_le_iff hC A).2 h

/-- For a nonempty row type, the supremum of row absolute sums is realized as
a `sup'` in `ℝ`. -/
theorem rowSumOpNorm_eq_sup' (A : Matrix m n ℝ) (hne : Nonempty m) :
    rowSumOpNorm A =
      (Finset.univ : Finset m).sup' (Finset.univ_nonempty) fun i => ∑ j, |A i j| := by
  have h0 : 0 ≤ (Finset.univ : Finset m).sup' (Finset.univ_nonempty) fun i => ∑ j, |A i j| := by
    exact le_trans (Finset.sum_nonneg fun j _ => abs_nonneg _)
      (Finset.le_sup' (fun i : m => ∑ j, |A i j|)
        (Finset.mem_univ (Classical.choice hne)))
  have h2 : (Finset.univ : Finset m).sup' (Finset.univ_nonempty) (fun i : m => ∑ j, |A i j|)
      ≤ rowSumOpNorm A :=
    (Finset.sup'_le_iff (Finset.univ_nonempty) (fun i : m => ∑ j, |A i j|)).mpr
      fun k _ => rowSumOpNorm_row_le A k
  refine le_antisymm
    ((rowSumOpNorm_le_iff h0 A).2 fun i =>
      Finset.le_sup' (fun i : m => ∑ j, |A i j|) (Finset.mem_univ i))
    h2

omit [Fintype m] in
/-- The `mulVec` action of a real matrix is controlled row-wise by the
absolute entries of the row and of the vector. -/
theorem mulVec_row_bound (A : Matrix m n ℝ) (x : n → ℝ) (i : m) :
    |Matrix.mulVec A x i| ≤ ∑ j, |A i j| * |x j| := by
  calc |Matrix.mulVec A x i| = |∑ j, A i j * x j| := rfl
    _ ≤ ∑ j, |A i j * x j| :=
      Finset.abs_sum_le_sum_abs (fun j => A i j * x j) Finset.univ
    _ = ∑ j, |A i j| * |x j| := Finset.sum_congr rfl fun j _ => abs_mul _ _

/-- The `L∞` operator-norm `mulVec` bound: `‖A *ᵥ v‖∞ ≤ rowSumOpNorm A * ‖v‖∞`. -/
theorem rowSumOpNorm_mulVec (A : Matrix m n ℝ) (v : n → ℝ) :
    ‖Matrix.mulVec A v‖ ≤ rowSumOpNorm A * ‖v‖ :=
  Matrix.linfty_opNorm_mulVec A v

end RowSumNorm

/-! ## Stage 2: eventual uniform bounds from bounded row sums

The actual long-memory weighted matrices of the model are indexed by a row
type `κ n` growing with `n` (e.g. `Fin (localWeightActiveSet n q (δ n) t).card`),
so the reduction below is stated for a whole sequence of matrices with varying
finite index types. -/

section EventualBound

open Filter

variable {κ : ℕ → Type*} [∀ n, Fintype (κ n)]

/-- **Stage 2 reduction (row-sum form).** If, eventually, every absolute row
sum of `A n` is at most `C`, then the row-sum operator norms are eventually
uniformly bounded. -/
theorem rowSumOpNorm_eventually_bound (A : ∀ n, Matrix (κ n) (κ n) ℝ) (C : ℝ)
    (h : ∀ᶠ n in atTop, ∀ i, ∑ j, |A n i j| ≤ C) :
    ∃ C' : ℝ, ∀ᶠ n in atTop, rowSumOpNorm (A n) ≤ C' :=
  ⟨max C 0, h.mono fun n hn =>
    (rowSumOpNorm_le_iff (le_max_right C 0) (A n)).2
      fun i => le_trans (hn i) (le_max_left C 0)⟩

/-- **Stage 2 reduction (entrywise form).** If, eventually, every entry of
`A n` is at most `r` in absolute value and the row type is a fixed finite
type of cardinality `N`, then `rowSumOpNorm (A n)` is eventually bounded by
`N * r`. -/
theorem rowSumOpNorm_eventually_bound_of_entry {ι : Type*} [Fintype ι]
    (A : ℕ → Matrix ι ι ℝ) (r : ℝ)
    (h : ∀ᶠ n in atTop, ∀ i j, |A n i j| ≤ r) :
    ∃ C : ℝ, ∀ᶠ n in atTop, rowSumOpNorm (A n) ≤ C := by
  refine ⟨((Finset.univ : Finset ι).card : ℝ) * max r 0, ?_⟩
  have hC0 : (0:ℝ) ≤ ((Finset.univ : Finset ι).card : ℝ) * max r 0 :=
    mul_nonneg (Nat.cast_nonneg (Finset.univ.card : ℕ)) (le_max_right r 0)
  filter_upwards [h] with n hn
  exact (rowSumOpNorm_le_iff hC0 (A n)).2 fun i =>
    le_trans (Finset.sum_le_sum fun j _ => le_trans (hn i j) (le_max_left r 0))
      (by rw [Finset.sum_const, nsmul_eq_mul])

end EventualBound

end Hurst
