import Hurst.DiscreteRieszCycleBridge

/-!
# Explicit vertex-tuple forms of finite Riesz cycle sums

This file rewrites the recursive closed-walk coordinate sum of
`DiscreteRieszCycleBridge` as finite sums over vertex tuples
`Fin k -> Fin m`, which is the form needed for lattice reindexing and
for uniform band estimates.
-/

noncomputable section

open Filter Matrix Set
open scoped Topology

namespace Hurst

variable {m : ℕ}

/-- The vertex sequence `(i, z 0, ..., z (k - 1), j)` of an open path with
`k` interior vertices and endpoints `i`, `j`. -/
def rieszVertexSeq {m : ℕ} {k : ℕ} (i j : Fin m) (z : Fin k → Fin m) :
    Fin (k + 2) → Fin m :=
  @Fin.cons (k + 1) (fun _ => Fin m) i (Fin.snoc z j)

theorem rieszVertexSeq_start {m k : ℕ} {i j : Fin m} {z : Fin k → Fin m} :
    rieszVertexSeq i j z 0 = i := rfl

theorem rieszVertexSeq_succ {m k : ℕ} (i j : Fin m) (z : Fin k → Fin m)
    (t : Fin (k + 1)) :
    rieszVertexSeq i j z (Fin.succ t) = @Fin.snoc k (fun _ => Fin m) z j t :=
  Fin.cons_succ ..

theorem rieszVertexSeq_end {m k : ℕ} {i j : Fin m} {z : Fin k → Fin m} :
    rieszVertexSeq i j z (Fin.last (k + 1)) = j := by
  rw [show (Fin.last (k + 1) : Fin (k + 2)) = Fin.succ (Fin.last k) from rfl,
    rieszVertexSeq_succ, Fin.snoc_last]

theorem rieszVertexSeq_castSucc_zero {m k : ℕ} {i j : Fin m} {z : Fin k → Fin m} :
    rieszVertexSeq i j z (Fin.castSucc 0) = i := rfl

theorem rieszVertexSeq_castSucc_succ {m k : ℕ} {i j : Fin m} {z : Fin k → Fin m}
    (s : Fin k) :
    rieszVertexSeq i j z (Fin.castSucc (Fin.succ s)) = z s := by
  rw [Fin.castSucc_succ, rieszVertexSeq_succ, Fin.snoc_castSucc]

/-- The shift relation: adjoining an interior vertex `x` at the start
shifts every vertex position by one. -/
theorem rieszVertexSeq_shift {m k : ℕ} {i x j : Fin m} {z : Fin k → Fin m}
    (c : Fin (k + 2)) :
    rieszVertexSeq (k := k + 1) i j (Fin.cons x z) (Fin.succ c) =
      rieszVertexSeq (k := k) x j z c := by
  simp only [rieszVertexSeq, Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]

/-! ### Open path sums over interior vertex tuples -/

/-- Sum over the `k` interior vertices of a path of `k + 1` edges running
from `i` to `j`, with edge weights `f 0, ..., f k`. -/
def rieszOpenPathSum {m : ℕ} (f : ℕ → Fin m → Fin m → ℝ) (k : ℕ)
    (i j : Fin m) : ℝ :=
  ∑ z : Fin k → Fin m, ∏ t : Fin (k + 1),
    f t (rieszVertexSeq i j z (Fin.castSucc t))
        (rieszVertexSeq i j z (Fin.succ t))

theorem rieszOpenPathSum_zero {m : ℕ} (f : ℕ → Fin m → Fin m → ℝ)
    (i j : Fin m) :
    rieszOpenPathSum f 0 i j = f 0 i j := by
  unfold rieszOpenPathSum
  rw [Finset.sum_eq_single_of_mem (fun z : Fin 0 => z.elim0)
    (Finset.mem_univ _)
    (fun b _ hb => absurd (Subsingleton.elim b (fun z : Fin 0 => z.elim0)) hb),
    Fin.prod_univ_one]
  rw [rieszVertexSeq_castSucc_zero]
  rw [show (Fin.succ (0 : Fin 1) : Fin 2) = Fin.last 1 from rfl]
  rw [rieszVertexSeq_end]
  rfl

/-- The `t`-th level matrix. -/
def rieszLevelMatrix {m : ℕ} (f : ℕ → Fin m → Fin m → ℝ) (t : ℕ) :
    Matrix (Fin m) (Fin m) ℝ := Matrix.of (f t)

/-- The ordered product of the first `k` level matrices, left-associated. -/
def rieszLevelProd {m : ℕ} (f : ℕ → Fin m → Fin m → ℝ) : ℕ →
    Matrix (Fin m) (Fin m) ℝ
  | 0 => 1
  | k + 1 => rieszLevelProd f k * rieszLevelMatrix f k

theorem rieszLevelProd_one_apply {m : ℕ} (f : ℕ → Fin m → Fin m → ℝ)
    (i j : Fin m) :
    (rieszLevelProd f 1) i j = f 0 i j := by
  simp [rieszLevelProd, rieszLevelMatrix, Matrix.mul_apply, Matrix.of_apply,
    Matrix.one_apply]

end Hurst
