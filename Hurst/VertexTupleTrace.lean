import Hurst.DiscreteRieszCycleBridge
import Hurst.RieszCutoffWalk

/-!
# Vertex-tuple form of the closed-walk coordinate sum

This file rewrites the closed-walk coordinate sum
`matrixClosedWalkCoordinateSum` (equivalently the power trace) as a finite
sum over vertex tuples `Fin (k+1) → Fin m` with the cyclic edge product
`∏ c, A (w c) (w (cycleSucc c))`, where `cycleSucc` is the cyclic successor
on `Fin (k+1)` (including the wraparound step `last ↦ 0`).

Two forms are provided:

* the fully reindexed form over tuples `w : Fin (k+1) → Fin m`
  (`matrixClosedWalkCoordinateSum_vertexTuple`), and
* the intermediate form over endpoints and interior vertices
  `∑ i, ∑ z, ∏ t, A (rieszVertexSeq i i z (castSucc t)) (rieszVertexSeq i i z (succ t))`
  (`matrixClosedWalkCoordinateSum_vertexTuple_iz`),

together with the open-path identity
`matrixPathCoordinateSum_openPathSum` feeding both.
-/

noncomputable section

namespace Hurst

variable {m : ℕ}

/-! ### The cyclic successor on `Fin n` -/

/-- Cyclic successor on `Fin n`: `c ↦ c + 1`, wrapping around to `0`. -/
def cycleSucc {n : ℕ} (c : Fin n) : Fin n :=
  if h : c.val + 1 < n then ⟨c.val + 1, h⟩ else ⟨0, by have := c.isLt; omega⟩

theorem cycleSucc_last {n : ℕ} : cycleSucc (Fin.last n) = 0 := by
  apply Fin.ext
  rw [cycleSucc, dif_neg (by rw [Fin.val_last]; omega)]
  rfl

theorem castSucc_cycleSucc {n : ℕ} {c : Fin n} (h : c.val + 1 < n) :
    Fin.castSucc (cycleSucc c) = Fin.succ c := by
  apply Fin.ext
  rw [cycleSucc, dif_pos h, Fin.val_castSucc, Fin.val_succ]

/-! ### Bijections used for the reindexing -/

/-- `Fin.snoc` identifies pairs `x : Fin m`, `z : Fin k → Fin m` with functions
on `Fin (k + 1)`. -/
theorem bijective_fin_snoc {m k : ℕ} :
    Function.Bijective (fun p : Fin m × (Fin k → Fin m) =>
      @Fin.snoc k (fun _ => Fin m) p.2 p.1) :=
  (Fin.snocEquiv (fun _ => Fin m) (n := k)).bijective

/-- The map `(i, z) ↦ (vertex sequence of the path `i → z 0 → ... → z (k-1) → i)`,
indexed by `Fin (k+1)`, is a bijection onto vertex tuples `Fin (k+1) → Fin m`. -/
theorem bijective_vertexTuple {m k : ℕ} :
    Function.Bijective (fun (p : Fin m × (Fin k → Fin m)) c =>
      rieszVertexSeq p.1 p.1 p.2 (Fin.castSucc c)) := by
  constructor
  · rintro ⟨a, z⟩ ⟨b, w⟩ hpq
    have h1 : a = b := congrFun hpq (0 : Fin (k + 1))
    have h2 : z = w := by
      funext t
      have h : rieszVertexSeq a a z (Fin.castSucc (Fin.succ t)) =
          rieszVertexSeq b b w (Fin.castSucc (Fin.succ t)) := congrFun hpq (Fin.succ t)
      rwa [rieszVertexSeq_castSucc_succ, rieszVertexSeq_castSucc_succ] at h
    subst h1
    exact congrArg (Prod.mk a) h2
  · intro f
    refine ⟨(f 0, fun t => f (Fin.succ t)), funext fun c => ?_⟩
    show rieszVertexSeq (f 0) (f 0) (fun t => f (Fin.succ t)) (Fin.castSucc c) = f c
    cases c using Fin.cases with
    | zero => rfl
    | succ t => rw [rieszVertexSeq_castSucc_succ]

/-! ### The open-path product splits off the last edge -/

/-- Adjoining a last interior vertex `x` splits the open-path product into
the open-path product from `i` to `x` and the last edge `A x j`. -/
theorem rieszVertexSeq_snoc_prod (A : Fin m → Fin m → ℝ) {k : ℕ} (i x j : Fin m)
    (z : Fin k → Fin m) :
    (∏ t : Fin (k + 2), A (rieszVertexSeq i j (Fin.snoc z x) (Fin.castSucc t))
        (rieszVertexSeq i j (Fin.snoc z x) (Fin.succ t))) =
      (∏ t : Fin (k + 1), A (rieszVertexSeq i x z (Fin.castSucc t))
          (rieszVertexSeq i x z (Fin.succ t))) * A x j := by
  have hlast : A (rieszVertexSeq i j (Fin.snoc z x) (Fin.castSucc (Fin.last (k + 1))))
      (rieszVertexSeq i j (Fin.snoc z x) (Fin.succ (Fin.last (k + 1)))) = A x j := by
    rw [show (Fin.last (k + 1) : Fin (k + 2)) = Fin.succ (Fin.last k) from rfl,
      show (Fin.succ (Fin.succ (Fin.last k)) : Fin (k + 3)) = Fin.last (k + 2) from rfl,
      rieszVertexSeq_end, Fin.castSucc_succ (i := Fin.last k), rieszVertexSeq_succ,
      Fin.snoc_castSucc, Fin.snoc_last]
  have hsplit : (∏ t : Fin (k + 2), A (rieszVertexSeq i j (Fin.snoc z x) (Fin.castSucc t))
      (rieszVertexSeq i j (Fin.snoc z x) (Fin.succ t))) =
    (∏ t : Fin (k + 1), A (rieszVertexSeq i j (Fin.snoc z x)
          (Fin.castSucc (Fin.castSucc t)))
        (rieszVertexSeq i j (Fin.snoc z x) (Fin.succ (Fin.castSucc t)))) *
      A (rieszVertexSeq i j (Fin.snoc z x) (Fin.castSucc (Fin.last (k + 1))))
          (rieszVertexSeq i j (Fin.snoc z x) (Fin.succ (Fin.last (k + 1)))) := by
    rw [Fin.prod_univ_castSucc
      (f := fun t : Fin (k + 2) => A (rieszVertexSeq i j (Fin.snoc z x) (Fin.castSucc t))
        (rieszVertexSeq i j (Fin.snoc z x) (Fin.succ t)))]
  have hL0 : rieszVertexSeq i j (Fin.snoc z x)
      (Fin.castSucc (Fin.castSucc (0 : Fin (k + 1)))) = i := by
    rw [show (Fin.castSucc (Fin.castSucc (0 : Fin (k + 1))) : Fin (k + 3)) = (0 : Fin (k + 3)) from rfl]
    exact rieszVertexSeq_start
  have hL0' : rieszVertexSeq i j (Fin.snoc z x)
      (Fin.succ (Fin.castSucc (0 : Fin (k + 1)))) =
      rieszVertexSeq i x z (Fin.succ (0 : Fin (k + 1))) := by
    rw [rieszVertexSeq_succ, rieszVertexSeq_succ, Fin.snoc_castSucc]
  have hR0 : rieszVertexSeq i x z (Fin.castSucc (0 : Fin (k + 1))) = i := by
    rw [show (Fin.castSucc (0 : Fin (k + 1)) : Fin (k + 2)) = (0 : Fin (k + 2)) from rfl]
    exact rieszVertexSeq_start
  have hR0' : rieszVertexSeq i x z (Fin.succ (0 : Fin (k + 1))) =
      @Fin.snoc k (fun _ => Fin m) z x (0 : Fin (k + 1)) :=
    rieszVertexSeq_succ i x z (0 : Fin (k + 1))
  have hLs (s : Fin k) : rieszVertexSeq i j (Fin.snoc z x)
      (Fin.castSucc (Fin.castSucc (Fin.succ s))) = z s := by
    rw [show (Fin.castSucc (Fin.castSucc (Fin.succ s)) : Fin (k + 3)) =
      Fin.castSucc (Fin.succ (Fin.castSucc s)) from rfl,
      rieszVertexSeq_castSucc_succ, Fin.snoc_castSucc]
  have hLs' (s : Fin k) : rieszVertexSeq i j (Fin.snoc z x)
      (Fin.succ (Fin.castSucc (Fin.succ s))) =
      @Fin.snoc (k + 1) (fun _ => Fin m) (Fin.snoc z x) j (Fin.castSucc (Fin.succ s)) :=
    rieszVertexSeq_succ i j (Fin.snoc z x) (Fin.castSucc (Fin.succ s))
  have hRs (s : Fin k) : rieszVertexSeq i x z (Fin.castSucc (Fin.succ s)) = z s := by
    rw [Fin.castSucc_succ (i := s), rieszVertexSeq_succ, Fin.snoc_castSucc]
  have hRs' (s : Fin k) : rieszVertexSeq i x z (Fin.succ (Fin.succ s)) =
      @Fin.snoc k (fun _ => Fin m) z x (Fin.succ s) :=
    rieszVertexSeq_succ i x z (Fin.succ s)
  have hpt : ∀ t ∈ Finset.univ, A (rieszVertexSeq i j (Fin.snoc z x)
        (Fin.castSucc (Fin.castSucc t)))
      (rieszVertexSeq i j (Fin.snoc z x) (Fin.succ (Fin.castSucc t))) =
    A (rieszVertexSeq i x z (Fin.castSucc t)) (rieszVertexSeq i x z (Fin.succ t)) := by
    intro t _
    cases t using Fin.cases with
    | zero => rw [hL0, hL0', hR0, hR0']
    | succ s => rw [hLs, hLs', hRs, hRs', Fin.snoc_castSucc]
  rw [hsplit, hlast, Finset.prod_congr rfl hpt]

/-! ### Step 1: open paths -/

/-- The matrix-power coordinate sum of `k + 1` steps is exactly the open-path
sum over interior vertex tuples. -/
theorem matrixPathCoordinateSum_openPathSum (A : Fin m → Fin m → ℝ) :
    ∀ (k : ℕ) (i j : Fin m), matrixPathCoordinateSum A (k + 1) i j =
      rieszOpenPathSum (fun _ => A) k i j := by
  intro k
  induction k with
  | zero =>
    intro i j
    rw [matrixPathCoordinateSum,
      Finset.sum_eq_single i
        (by
          intro b _ hb
          rw [matrixPathCoordinateSum, if_neg (fun h => hb h.symm), zero_mul])
        (by intro h; exact (h (Finset.mem_univ i)).elim)]
    rw [matrixPathCoordinateSum, if_pos rfl, one_mul, rieszOpenPathSum_zero]
  | succ k ih =>
    intro i j
    have h1 : matrixPathCoordinateSum A (k + 1 + 1) i j =
        ∑ x : Fin m, ∑ z : Fin k → Fin m,
          (∏ t : Fin (k + 1), A (rieszVertexSeq i x z (Fin.castSucc t))
              (rieszVertexSeq i x z (Fin.succ t))) * A x j := by
      rw [matrixPathCoordinateSum]
      simp only [ih]
      unfold rieszOpenPathSum
      dsimp only
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact Finset.sum_mul Finset.univ _ (A x j)
    have h2 : (∑ x : Fin m, ∑ z : Fin k → Fin m,
          (∏ t : Fin (k + 1), A (rieszVertexSeq i x z (Fin.castSucc t))
              (rieszVertexSeq i x z (Fin.succ t))) * A x j) =
        ∑ p : Fin m × (Fin k → Fin m),
          (∏ t : Fin (k + 1), A (rieszVertexSeq i p.1 p.2 (Fin.castSucc t))
              (rieszVertexSeq i p.1 p.2 (Fin.succ t))) * A p.1 j :=
      (Fintype.sum_prod_type (fun p : Fin m × (Fin k → Fin m) =>
        (∏ t : Fin (k + 1), A (rieszVertexSeq i p.1 p.2 (Fin.castSucc t))
            (rieszVertexSeq i p.1 p.2 (Fin.succ t))) * A p.1 j)).symm
    rw [h1, h2]
    refine Fintype.sum_bijective _ bijective_fin_snoc _ _ (fun p => ?_)
    dsimp only
    rw [rieszVertexSeq_snoc_prod]

/-! ### Step 2: closed walks as vertex tuples -/

/-- Endpoints-and-interior-vertices form of the closed-walk sum. -/
theorem matrixClosedWalkCoordinateSum_vertexTuple_iz (A : Fin m → Fin m → ℝ) (k : ℕ) :
    matrixClosedWalkCoordinateSum A (k + 1) =
      ∑ i : Fin m, ∑ z : Fin k → Fin m, ∏ t : Fin (k + 1),
        A (rieszVertexSeq i i z (Fin.castSucc t))
            (rieszVertexSeq i i z (Fin.succ t)) := by
  rw [matrixClosedWalkCoordinateSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact matrixPathCoordinateSum_openPathSum A k i i

/-- The vertex-tuple form of the closed-walk sum: the closed-walk coordinate
sum at length `k + 1` is the sum over all vertex tuples `w : Fin (k + 1) → Fin m`
of the cyclic edge product `∏ c : Fin (k + 1), A (w c) (w (cycleSucc c))`,
where `cycleSucc` is the cyclic successor (including the wraparound
`w (Fin.last k) ↦ w 0`). -/
theorem matrixClosedWalkCoordinateSum_vertexTuple (A : Fin m → Fin m → ℝ) (k : ℕ) :
    matrixClosedWalkCoordinateSum A (k + 1) =
      ∑ w : Fin (k + 1) → Fin m, ∏ c : Fin (k + 1),
        A (w c) (w (cycleSucc c)) := by
  have h1 := matrixClosedWalkCoordinateSum_vertexTuple_iz A k
  have h2 : (∑ i : Fin m, ∑ z : Fin k → Fin m, ∏ t : Fin (k + 1),
      A (rieszVertexSeq i i z (Fin.castSucc t))
          (rieszVertexSeq i i z (Fin.succ t))) =
      ∑ p : Fin m × (Fin k → Fin m), ∏ t : Fin (k + 1),
        A (rieszVertexSeq p.1 p.1 p.2 (Fin.castSucc t))
            (rieszVertexSeq p.1 p.1 p.2 (Fin.succ t)) :=
    (Fintype.sum_prod_type (fun p : Fin m × (Fin k → Fin m) => ∏ t : Fin (k + 1),
      A (rieszVertexSeq p.1 p.1 p.2 (Fin.castSucc t))
          (rieszVertexSeq p.1 p.1 p.2 (Fin.succ t)))).symm
  rw [h1, h2]
  refine Fintype.sum_bijective _ bijective_vertexTuple _ _ (fun p => ?_)
  refine Finset.prod_congr rfl (fun c _ => ?_)
  dsimp only
  by_cases hc : c.val + 1 < k + 1
  · rw [castSucc_cycleSucc hc]
  · have hc2 : c = Fin.last k := Fin.ext (by have := c.isLt; show c.val = k; omega)
    subst hc2
    rw [cycleSucc_last,
      show (Fin.succ (Fin.last k) : Fin (k + 2)) = Fin.last (k + 1) from rfl,
      rieszVertexSeq_end, Fin.castSucc_zero, rieszVertexSeq_start]

/-- The vertex-tuple form for a positive number of steps `k`, in the shape
`∑ w : Fin k → Fin m, ∏ c : Fin k, A (w c) (w (cycleSucc c))`. -/
theorem matrixClosedWalkCoordinateSum_vertexTuple_of_pos (A : Fin m → Fin m → ℝ)
    (k : ℕ) (hk : 0 < k) :
    matrixClosedWalkCoordinateSum A k =
      ∑ w : Fin k → Fin m, ∏ c : Fin k, A (w c) (w (cycleSucc c)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact matrixClosedWalkCoordinateSum_vertexTuple A k'

/-- Composed with the trace identity, the vertex-tuple form reads directly
on the matrix power. -/
theorem trace_pow_vertexTuple (A : Matrix (Fin m) (Fin m) ℝ) (k : ℕ) :
    Matrix.trace (A ^ (k + 1)) =
      ∑ w : Fin (k + 1) → Fin m, ∏ c : Fin (k + 1),
        A (w c) (w (cycleSucc c)) := by
  rw [← matrixClosedWalkCoordinateSum_eq_trace_pow]
  exact matrixClosedWalkCoordinateSum_vertexTuple A k

end Hurst
