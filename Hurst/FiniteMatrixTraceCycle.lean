import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite-matrix trace cyclicity (A8)

This file proves the **finite-dimensional step A8 of the M1-D cycle-integral
bridge**: the general identity `trace (M ^ (k+1)) = ∑ cycles` for a matrix
`M : Matrix (Fin n) (Fin n) ℝ`, together with its two specialisations used
downstream (spec §5, M1-D2):

* **B-matrix (√ structure)**: for `κ ≥ 0` and a weight `w`,
  `trace ((fun i j => √(κ i * κ j) * w i j) ^ (k+1))
     = ∑ c, ∏ j, κ (c j) * w (c j) (c (j + 1))` — on each closed cycle the
  adjacent square roots pair up and cancel, so the product telescopes to `∏ κ`
  (this is where `κ ≥ 0` is used, factorwise via `Real.sqrt_mul`);
* **WK-matrix (diagonal right multiplication)**:
  `trace ((fun i j => w i j * κ j) ^ (k+1))
     = ∑ c, ∏ j, κ (c j) * w (c j) (c (j + 1))` — a pure reindexing of the
  product around the cycle, valid with no sign hypothesis on `κ`.

Both specialisations produce **the same** weighted cycle sum, which is the
abstract equality consumed by the D2 bridge.  The file is deliberately free of
any infinite-dimensional objects (no `L2`, no `S`/`B` operators): the
infinite-dimensional route goes through finite spectral compression + limits
instead, and consumes A8 through the compression map.

## Indexing convention

Cycles are functions `c : Fin (k + 1) → Fin n` (so the power `k + 1` is ≥ 1 by
construction; the literal `k = 0` instance of a `Fin k`-indexed statement is
false since `trace (M ^ 0) = n ≠ 1`), and the cyclic successor of `j` is the
`Fin`-addition `j + 1` (wraparound to `0` at `Fin.last`), the plain-mathlib
analogue of the landed `Hurst.finCyclicSucc`.

## Route

1. `trace_mulPow_eq_cycleSum` (private engine), by induction on `k`: the trace
   of `Matrix.of g ^ k * Matrix.of h` is the sum over `(k+1)`-vertex cycles
   whose first `k` edges are `g`-edges (in `castSucc`/`succ` form) and whose
   closing edge is `h`.  The step reassociates
   `Matrix.of g ^ (k+1) * Matrix.of h = Matrix.of g ^ k * (product matrix)`,
   expands the single product-matrix entry (`Matrix.mul_apply`), and reindexes
   the vertex tuples along the plain append `cycSnoc`
   (`Fintype.sum_bijective` + `Fin.prod_univ_castSucc`).  Everything is stated
   over raw entry functions to keep rewriting on plain function applications.
2. `trace_pow_eq_cycleSum`: the engine at `h := g`, with the closing `g`-edge
   folded back into the `Fin (k+1)`-product.
3. `trace_Bm_eq_cycleSum` / `trace_WKm_eq_cycleSum`: entrywise reduction plus
   the per-cycle product manipulation (AM–GM-free telescoping /
   `Finset.prod_mul_distrib` + the cyclic shift `prod_cyc_shift`).
-/

namespace HS

/-! ### Cyclic index bookkeeping -/

private theorem succ_castSucc_eq {k : ℕ} (j : Fin k) :
    (Fin.succ (Fin.castSucc j) : Fin (k + 2)) = Fin.castSucc (Fin.succ j) := by
  ext
  simp

private theorem succ_last_eq {k : ℕ} :
    (Fin.succ (Fin.last k) : Fin (k + 2)) = Fin.last (k + 1) := by
  ext
  simp

private theorem castSucc_add_one_eq {k : ℕ} (i : Fin k) :
    (Fin.castSucc i + 1 : Fin (k + 1)) = Fin.succ i := by
  ext
  rw [Fin.val_add]
  simp

private theorem last_add_one_eq {k : ℕ} :
    (Fin.last k + 1 : Fin (k + 1)) = 0 := by
  ext
  simp

/-- Evaluating a `Fin 1`-indexed family at its single point is a bijection. -/
private theorem fin_one_eval_bijective {α : Type*} :
    Function.Bijective (fun x : α => (fun _ => x : Fin 1 → α)) := by
  constructor
  · intro a b h
    exact congrFun h 0
  · intro c
    refine ⟨c 0, ?_⟩
    funext j
    rw [Fin.eq_zero j]

/-- Plain (non-dependent) append of a final vertex to a cycle prefix. -/
private def cycSnoc {k n : ℕ} (c : Fin k → Fin n) (t : Fin n) : Fin (k + 1) → Fin n :=
  fun i => if h : i.val < k then c ⟨i.val, h⟩ else t

private theorem cycSnoc_castSucc {k n : ℕ} (c : Fin k → Fin n) (t : Fin n) (i : Fin k) :
    cycSnoc c t (Fin.castSucc i) = c i := by
  have hv : (Fin.castSucc i).val < k := i.isLt
  rw [cycSnoc, dif_pos hv]
  exact congrArg c (by ext; simp [Fin.val_castSucc])

private theorem cycSnoc_last {k n : ℕ} (c : Fin k → Fin n) (t : Fin n) :
    cycSnoc c t (Fin.last k) = t := by
  have hv : ¬((Fin.last k).val < k) := by rw [Fin.val_last]; omega
  rw [cycSnoc, dif_neg hv]

/-- Appending a final vertex to a cycle prefix is injective. -/
private theorem cycSnoc_injective {k n : ℕ} :
    ∀ (p q : (Fin k → Fin n) × Fin n), cycSnoc p.1 p.2 = cycSnoc q.1 q.2 → p = q := by
  intro p q hpq
  refine Prod.ext ?_ ?_
  · funext i
    have h := congrFun hpq (Fin.castSucc i)
    simp only [cycSnoc_castSucc] at h
    exact h
  · have h := congrFun hpq (Fin.last k)
    simp only [cycSnoc_last] at h
    exact h

/-- Appending a final vertex to a cycle prefix is surjective. -/
private theorem cycSnoc_surjective {k n : ℕ} :
    ∀ d : Fin (k + 1) → Fin n, ∃ p : (Fin k → Fin n) × Fin n, cycSnoc p.1 p.2 = d := by
  intro d
  refine ⟨(fun i => d (Fin.castSucc i), d (Fin.last k)), ?_⟩
  funext j
  by_cases hj : j = Fin.last k
  · subst hj
    rw [cycSnoc_last]
  · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    rw [cycSnoc_castSucc]

/-- The cyclic shift `j ↦ j + 1` is a permutation of `Fin (k + 1)`, so a
product along it is unchanged. -/
private theorem prod_cyc_shift {k : ℕ} {α : Type*} [CommMonoid α] (F : Fin (k + 1) → α) :
    (∏ j : Fin (k + 1), F (j + 1)) = ∏ j : Fin (k + 1), F j := by
  refine Fintype.prod_bijective (fun i : Fin (k + 1) => i + 1) ⟨?_, ?_⟩ (fun j => F (j + 1)) F
    (fun _ => rfl)
  · intro a b hab
    have h : a + 1 = b + 1 := hab
    have h2 : (a + 1) - 1 = (b + 1) - 1 := by rw [h]
    simpa using h2
  · intro b
    exact ⟨b - 1, by simp⟩

/-! ### The engine and the three deliverables -/

/-- Private engine: the trace of `Matrix.of g ^ k * Matrix.of h` is the sum over
`(k+1)`-vertex cycles whose first `k` edges are `g`-edges (in `castSucc`/`succ`
form) and whose closing edge is `h`.  Stated over raw entry functions so that
all rewriting happens on plain function applications. -/
private theorem trace_mulPow_eq_cycleSum {n : ℕ} (g : Fin n → Fin n → ℝ) :
    ∀ (k : ℕ) (h : Fin n → Fin n → ℝ), Matrix.trace (Matrix.of g ^ k * Matrix.of h)
      = ∑ c : Fin (k + 1) → Fin n,
          (∏ j : Fin k, g (c (Fin.castSucc j)) (c (Fin.succ j)))
            * h (c (Fin.last k)) (c 0) := by
  intro k
  induction k with
  | zero =>
    intro h
    rw [pow_zero, Matrix.one_mul]
    have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hlast]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact Fintype.sum_bijective (fun x : Fin n => (fun _ => x : Fin 1 → Fin n))
      fin_one_eval_bijective (fun i => h i i) (fun c => h (c 0) (c 0)) (fun _ => rfl)
  | succ k ih =>
    intro h
    have hprod : Matrix.of g * Matrix.of h
        = Matrix.of (fun i j => ∑ t, g i t * h t j) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [pow_succ, mul_assoc, hprod, ih (fun i j => ∑ t, g i t * h t j)]
    rw [Finset.sum_congr rfl fun c _ => Finset.mul_sum _ _ _]
    have hsp : ∑ p : (Fin (k + 1) → Fin n) × Fin n,
          (∏ j : Fin k, g (p.1 (Fin.castSucc j)) (p.1 (Fin.succ j)))
            * (g (p.1 (Fin.last k)) p.2 * h p.2 (p.1 0))
        = ∑ c : Fin (k + 1) → Fin n, ∑ t : Fin n,
            (∏ j : Fin k, g (c (Fin.castSucc j)) (c (Fin.succ j)))
              * (g (c (Fin.last k)) t * h t (c 0)) :=
      Fintype.sum_prod_type _
    rw [← hsp]
    refine Fintype.sum_bijective
      (fun p : (Fin (k + 1) → Fin n) × Fin n => (cycSnoc p.1 p.2 : Fin (k + 2) → Fin n))
      ⟨cycSnoc_injective, cycSnoc_surjective⟩ _ _ (fun p => ?_)
    obtain ⟨c, t⟩ := p
    simp only []
    rw [Fin.prod_univ_castSucc
      (f := fun j => g (cycSnoc c t (Fin.castSucc j)) (cycSnoc c t (Fin.succ j)))]
    have h0 : (0 : Fin (k + 2)) = Fin.castSucc (0 : Fin (k + 1)) := rfl
    rw [h0]
    simp only [cycSnoc_castSucc, succ_castSucc_eq, succ_last_eq, cycSnoc_last]
    simp only [mul_assoc]

/-- **通用有限恒等式(A8 引擎)**:矩阵幂的迹 = 循环乘积和.  The trace of the
`(k+1)`-st power of a finite matrix is the sum of the cycle products over all
`(k+1)`-vertex cycles, each edge taken at the cyclic successor `j + 1`
(`Fin`-addition, wrapping around at `Fin.last`). -/
theorem trace_pow_eq_cycleSum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix.trace (M ^ (k + 1))
      = ∑ c : Fin (k + 1) → Fin n, ∏ j : Fin (k + 1), M (c j) (c (j + 1)) := by
  obtain ⟨g, rfl⟩ : ∃ g : Fin n → Fin n → ℝ, Matrix.of g = M := ⟨M, rfl⟩
  simp only [Matrix.of_apply]
  rw [pow_succ, trace_mulPow_eq_cycleSum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fin.prod_univ_castSucc (f := fun j => g (c j) (c (j + 1)))]
  simp only [castSucc_add_one_eq, last_add_one_eq]

/-- **A8 左半:B-矩阵(√ 结构)的迹 = 加权 κ-循环和**.  For `κ ≥ 0` the adjacent
square roots on each closed cycle pair up and cancel
(`Real.sqrt_mul` factorwise, cyclic reindexing, `Real.mul_self_sqrt`), so the
product telescopes to `∏ κ`.  This needs `κ ≥ 0` only to split
`√(κ i * κ j) = √(κ i) * √(κ j)`. -/
theorem trace_Bm_eq_cycleSum {n : ℕ} (κ : Fin n → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (w : Fin n → Fin n → ℝ) (k : ℕ) :
    Matrix.trace (Matrix.of (fun i j => Real.sqrt (κ i * κ j) * w i j) ^ (k + 1))
      = ∑ c : Fin (k + 1) → Fin n, ∏ j : Fin (k + 1), κ (c j) * w (c j) (c (j + 1)) := by
  rw [trace_pow_eq_cycleSum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.of_apply]
  have hsqrt : ∀ j : Fin (k + 1),
      Real.sqrt (κ (c j) * κ (c (j + 1))) = Real.sqrt (κ (c j)) * Real.sqrt (κ (c (j + 1))) :=
    fun j => Real.sqrt_mul (hκ (c j)) (κ (c (j + 1)))
  have hSS : (∏ j : Fin (k + 1), Real.sqrt (κ (c j))) *
        (∏ j : Fin (k + 1), Real.sqrt (κ (c j))) = ∏ j : Fin (k + 1), κ (c j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => Real.mul_self_sqrt (hκ (c j))
  rw [Finset.prod_congr rfl (fun j _ => by rw [hsqrt j]), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, prod_cyc_shift (F := fun j => Real.sqrt (κ (c j))), hSS,
    Finset.prod_mul_distrib]

/-- **A8 右半:WK-矩阵(w·κ 对角右乘)的迹 = 同一循环和**.  Pure index
reindexing along the cycle (`Finset.prod_mul_distrib` + `prod_cyc_shift`); no
sign hypothesis on `κ` is needed. -/
theorem trace_WKm_eq_cycleSum {n : ℕ} (κ : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (k : ℕ) :
    Matrix.trace (Matrix.of (fun i j => w i j * κ j) ^ (k + 1))
      = ∑ c : Fin (k + 1) → Fin n, ∏ j : Fin (k + 1), κ (c j) * w (c j) (c (j + 1)) := by
  rw [trace_pow_eq_cycleSum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.of_apply]
  rw [Finset.prod_mul_distrib, prod_cyc_shift (F := fun j => κ (c j)), Finset.prod_mul_distrib,
    mul_comm]

end HS
