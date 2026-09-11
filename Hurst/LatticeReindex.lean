import Hurst.DiscreteRieszCycleBridge
import Hurst.RieszCutoffWalk
import Hurst.VertexTupleTrace
import Hurst.TruncatedRieszCycleBridge

/-!
# Exact affine lattice reindexing at a fixed cutoff

This file is the algebraic core of the predicate
`HasFixedCutoffMatrixLatticeReindex`: it identifies the finite cyclic trace of
the truncated weighted Riesz matrix at mesh `m` with the lattice sum of the
unit-cube integrand over the *right-endpoint* grid
`y i = (w i + 1) / m`, exactly, for every mesh `m`, cutoff level `R`, scale
`S`, exponent `psi`, amplitude `c` and weight `omega`.

The per-edge algebra is definitional: the truncated matrix entry is
`S⁻¹ * omega (rieszCycleGridPoint m (w i)) * truncatedRieszKernel R psi c
  (rieszCycleGridPoint m (w i)) (rieszCycleGridPoint m (w (cycleSucc i)))`,
while the unit-cube integrand at the right-endpoint point is the product of
exactly the same weight/kernel factors at the affine points
`2 * y i - 1 = rieszCycleGridPoint m (w i)` (and `finCyclicSucc = cycleSucc`),
so each matrix edge equals `S⁻¹` times the corresponding integrand edge.
Consequently
`weightedTruncatedRieszDiscreteCycleValue m (K+1) R S psi c omega
  = (S : ℝ)⁻¹ ^ (K + 1) * offsetLatticeSum m (K + 1) R psi c omega`.

The remaining gap to `HasFixedCutoffMatrixLatticeReindex` is purely the
boundary-face bookkeeping between the right-endpoint grid (upper vertices of
each mesh cell, `(w i + 1) / m` with `w i < m`) and the full lattice
`[0, m]^k / m` appearing in `unitCubeTruncatedRieszLatticeSum` (which also
contains the lower boundary faces `x i = 0`); this file supplies the exact
reindexing term of that comparison, in both raw and mesh-normalized form.

The untruncated pair is treated as well: `rankRieszKernel S psi c i j`
samples the *integer* distance `Nat.dist i.val j.val` (not the grid
distance), so against the real-distance unit-cube integrand the exact
per-edge prefactor is `(S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)` (note
`S⁻¹ * S ^ psi = S ^ (psi - 1)`, not `S ^ (-psi)`), and the diagonal rule
forces `psi ≠ 0` there.
-/

noncomputable section

namespace Hurst

variable {m : ℕ}

/-! ### The cyclic successors agree -/

theorem finCyclicSucc_eq_cycleSucc {k : ℕ} (i : Fin k) :
    finCyclicSucc i = cycleSucc i := by
  by_cases h : i.val + 1 < k
  · simp only [finCyclicSucc, cycleSucc, dif_pos h]
  · simp only [finCyclicSucc, cycleSucc, dif_neg h]

/-! ### The right-endpoint lattice point and sum -/

/-- The right-endpoint point of the mesh-`m` grid in `[0,1]^k` associated to
the vertex tuple `w`: coordinate `i` is `(w i + 1) / m`. -/
def offsetLatticePoint {m k : ℕ} (w : Fin k → Fin m) : Fin k → ℝ :=
  fun i => ((((w i : ℕ) + 1 : ℕ) : ℝ)) / (m : ℝ)

/-- The lattice sum of the fixed-cutoff unit-cube integrand over the
right-endpoint grid of mesh `m`: every upper vertex `(w i + 1) / m` of the
mesh cells, `w : Fin k → Fin m`. -/
def offsetLatticeSum (m k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) : ℝ :=
  ∑ w : Fin k → Fin m,
    unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
      (offsetLatticePoint w)

/-- The affine coordinate of the right-endpoint grid is exactly the cyclic
grid point. -/
theorem rieszCycleGridPoint_eq_affine (m : ℕ) (i : Fin m) :
    rieszCycleGridPoint m i =
      2 * ((((i : ℕ) + 1 : ℕ) : ℝ) / (m : ℝ)) - 1 := rfl

theorem offsetLatticePoint_affine (m k : ℕ) (w : Fin k → Fin m) (i : Fin k) :
    2 * offsetLatticePoint w i - 1 = rieszCycleGridPoint m (w i) := rfl

/-! ### Per-edge factorization of the truncated matrix -/

/-- Per-edge factor lemma: the truncated matrix edge is exactly `S⁻¹` times
the corresponding edge of the fixed-cutoff unit-cube integrand at the
right-endpoint point (weight at the left endpoint, capped kernel on the same
grid pair). -/
theorem truncatedMatrix_edge_eq (m R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ)
    (i j : Fin m) :
    weightedTruncatedRieszDiscreteMatrix m R S psi c omega i j
      = (S : ℝ)⁻¹ * omega (rieszCycleGridPoint m i) *
          truncatedRieszKernel R psi c
            (rieszCycleGridPoint m i) (rieszCycleGridPoint m j) := rfl

/-- The vertex-tuple edge product of the truncated matrix is `S⁻¹ ^ k` times
the unit-cube integrand at the right-endpoint point. -/
theorem truncatedMatrix_vertexTuple_prod_eq (m k R : ℕ) (S psi c : ℝ)
    (omega : ℝ → ℝ) (w : Fin k → Fin m) :
    ∏ i : Fin k,
        weightedTruncatedRieszDiscreteMatrix m R S psi c omega
          (w i) (w (cycleSucc i))
      = (S : ℝ)⁻¹ ^ k *
        unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
          (offsetLatticePoint w) := by
  have hA : ∀ i : Fin k,
      weightedTruncatedRieszDiscreteMatrix m R S psi c omega
          (w i) (w (cycleSucc i))
        = (S : ℝ)⁻¹ * (omega (rieszCycleGridPoint m (w i)) *
            truncatedRieszKernel R psi c
              (rieszCycleGridPoint m (w i))
              (rieszCycleGridPoint m (w (cycleSucc i)))) := fun i => by
    rw [truncatedMatrix_edge_eq]
    ring
  have hint :
      unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
          (offsetLatticePoint w)
        = ∏ i : Fin k, omega (rieszCycleGridPoint m (w i)) *
            truncatedRieszKernel R psi c
              (rieszCycleGridPoint m (w i))
              (rieszCycleGridPoint m (w (cycleSucc i))) := by
    simp only [unitCubeWeightedTruncatedRieszIntegrand,
      weightedTruncatedRieszCycleIntegrand, rieszUnitToSymmetricCube,
      offsetLatticePoint, finCyclicSucc_eq_cycleSucc, rieszCycleGridPoint]
  calc ∏ i : Fin k,
        weightedTruncatedRieszDiscreteMatrix m R S psi c omega
          (w i) (w (cycleSucc i))
    = ∏ i : Fin k, ((S : ℝ)⁻¹ * (omega (rieszCycleGridPoint m (w i)) *
          truncatedRieszKernel R psi c
            (rieszCycleGridPoint m (w i))
            (rieszCycleGridPoint m (w (cycleSucc i))))) :=
      Finset.prod_congr rfl fun i _ => hA i
  _ = (S : ℝ)⁻¹ ^ k * ∏ i : Fin k, (omega (rieszCycleGridPoint m (w i)) *
          truncatedRieszKernel R psi c
            (rieszCycleGridPoint m (w i))
            (rieszCycleGridPoint m (w (cycleSucc i)))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
  _ = (S : ℝ)⁻¹ ^ k * unitCubeWeightedTruncatedRieszIntegrand k R psi c omega
        (offsetLatticePoint w) := by rw [hint]

/-! ### The exact reindex identity at mesh `m` -/

/-- **Exact fixed-cutoff lattice reindex.** The cyclic trace of the truncated
weighted Riesz matrix at mesh `m` equals `(S : ℝ)⁻¹ ^ (K + 1)` times the
right-endpoint lattice sum of the fixed-cutoff unit-cube integrand.  This is
the algebraic core of `HasFixedCutoffMatrixLatticeReindex`; no hypothesis on
`m`, `S`, `psi`, `c`, `omega` or the cutoff `R` is used. -/
theorem weightedTruncatedRieszDiscreteCycleValue_eq_offsetLatticeSum
    (m K R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) :
    weightedTruncatedRieszDiscreteCycleValue m (K + 1) R S psi c omega
      = (S : ℝ)⁻¹ ^ (K + 1) *
        offsetLatticeSum m (K + 1) R psi c omega := by
  unfold weightedTruncatedRieszDiscreteCycleValue offsetLatticeSum
  rw [matrixClosedWalkCoordinateSum_vertexTuple, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact truncatedMatrix_vertexTuple_prod_eq m (K + 1) R S psi c omega w

/-- The same identity for every positive number of steps. -/
theorem weightedTruncatedRieszDiscreteCycleValue_eq_offsetLatticeSum'
    (m k R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) (hk : 0 < k) :
    weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega
      = (S : ℝ)⁻¹ ^ k * offsetLatticeSum m k R psi c omega := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  exact weightedTruncatedRieszDiscreteCycleValue_eq_offsetLatticeSum m K R S
    psi c omega

/-- Comparison shape against the normalized object of
`HasFixedCutoffMatrixLatticeReindex`: the discrete cyclic value factors as
the mesh power `(2 / m) ^ k` (which pairs with
`2 ^ k * unitCubeTruncatedRieszLatticeSum` via `m ^ k`) times the scale
power `((m : ℝ) / (2 * S)) ^ k` times the right-endpoint lattice sum. -/
theorem weightedTruncatedRieszDiscreteCycleValue_eq_meshScaled
    (m k R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) (hS : S ≠ 0) (hm : 0 < m)
    (hk : 0 < k) :
    weightedTruncatedRieszDiscreteCycleValue m k R S psi c omega
      = ((2 : ℝ) / (m : ℝ)) ^ k *
        (((m : ℝ) / (2 * S)) ^ k * offsetLatticeSum m k R psi c omega) := by
  rw [weightedTruncatedRieszDiscreteCycleValue_eq_offsetLatticeSum' m k R S
    psi c omega hk, ← mul_assoc]
  congr 1
  rw [← mul_pow]
  have h2S : (2 : ℝ) * S ≠ 0 := mul_ne_zero two_ne_zero hS
  have h1 : ((2 : ℝ) / (m : ℝ)) * ((m : ℝ) / (2 * S)) = (S : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    field_simp
  rw [h1]

/-! ### The untruncated pair -/

/-- The (S-free) scaled unit-cube cyclic integrand with the real-distance
Riesz edge kernel `c * |y i - y (finCyclicSucc i)| ^ (-psi)` at the affine
point `2 * y - 1`. -/
def unitCubeWeightedRieszIntegrand (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (y : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, omega (2 * y i - 1) *
    (c * |y i - y (finCyclicSucc i)| ^ (-psi))

/-- The right-endpoint lattice sum for the untruncated scaled integrand. -/
def untruncatedOffsetLatticeSum (m k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) : ℝ :=
  ∑ w : Fin k → Fin m,
    unitCubeWeightedRieszIntegrand k psi c omega (offsetLatticePoint w)

/-- Grid-distance mesh identification: grid points sit `2 / m` apart per
unit of integer distance. -/
theorem abs_sub_rieszCycleGridPoint_eq (m : ℕ) (i j : Fin m) :
    |rieszCycleGridPoint m i - rieszCycleGridPoint m j|
      = (2 : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ) / (m : ℝ) := by
  have hm : (0 : ℝ) < (m : ℝ) :=
    by exact_mod_cast lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hsub : rieszCycleGridPoint m i - rieszCycleGridPoint m j
      = ((2 : ℝ) / (m : ℝ)) *
        (((i.val : ℕ) : ℝ) - ((j.val : ℕ) : ℝ)) := by
    unfold rieszCycleGridPoint
    push_cast
    ring
  rw [hsub, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos hm]
  rcases le_total (j.val : ℤ) (i.val : ℤ) with hle | hle
  · have hNat : j.val ≤ i.val := by exact_mod_cast hle
    have hji : ((j.val : ℕ) : ℝ) ≤ ((i.val : ℕ) : ℝ) := by exact_mod_cast hNat
    have hnonneg : (0 : ℝ) ≤ ((i.val : ℕ) : ℝ) - ((j.val : ℕ) : ℝ) := by linarith
    rw [abs_of_nonneg hnonneg, Nat.dist_comm, Nat.dist_eq_sub_of_le hNat,
      Nat.cast_sub hNat]
    ring
  · have hNat : i.val ≤ j.val := by exact_mod_cast hle
    have hij : ((i.val : ℕ) : ℝ) ≤ ((j.val : ℕ) : ℝ) := by exact_mod_cast hNat
    have hnonpos : (((i.val : ℕ) : ℝ) - ((j.val : ℕ) : ℝ)) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos, Nat.dist_eq_sub_of_le hNat, Nat.cast_sub hNat]
    ring

/-- Real distance at the right-endpoint point: `Nat.dist` of the vertex
tuple over the mesh. -/
theorem offsetLatticePoint_abs_sub (m k : ℕ) (w : Fin k → Fin m) (i : Fin k)
    (hm : 0 < m) :
    |offsetLatticePoint w i - offsetLatticePoint w (cycleSucc i)|
      = ((Nat.dist (w i).val (w (cycleSucc i)).val : ℕ) : ℝ) / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsub : offsetLatticePoint w i - offsetLatticePoint w (cycleSucc i)
      = ((((w i).val : ℕ) : ℝ) - (((w (cycleSucc i)).val : ℕ) : ℝ)) / (m : ℝ) := by
    simp only [offsetLatticePoint]
    push_cast
    ring
  rw [hsub, abs_div, abs_of_pos hmR]
  rcases le_total (w (cycleSucc i)).val (w i).val with hle | hle
  · have hNat : (w (cycleSucc i)).val ≤ (w i).val := hle
    have hji : (((w (cycleSucc i)).val : ℕ) : ℝ) ≤ (((w i).val : ℕ) : ℝ) :=
      by exact_mod_cast hNat
    have hnonneg : (0 : ℝ) ≤
        (((w i).val : ℕ) : ℝ) - (((w (cycleSucc i)).val : ℕ) : ℝ) := by linarith
    rw [abs_of_nonneg hnonneg, Nat.dist_comm, Nat.dist_eq_sub_of_le hNat,
      Nat.cast_sub hNat]
  · have hNat : (w i).val ≤ (w (cycleSucc i)).val := hle
    have hij : (((w i).val : ℕ) : ℝ) ≤ (((w (cycleSucc i)).val : ℕ) : ℝ) :=
      by exact_mod_cast hNat
    have hnonpos : ((((w i).val : ℕ) : ℝ) -
        (((w (cycleSucc i)).val : ℕ) : ℝ)) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos, Nat.dist_eq_sub_of_le hNat, Nat.cast_sub hNat]
    ring

/-- Per-edge factor at the right-endpoint point for the *untruncated* matrix:
`Nat.dist` of the vertex tuple is `m` times the real distance at the affine
point, so the matrix edge is `(S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)` times
the scaled integrand edge.  The diagonal rule `Nat.dist = 0 ↦ 0` forces
`psi ≠ 0`. -/
theorem rankRieszKernel_edge_at_offsetPoint (m k : ℕ) (S psi c : ℝ)
    (omega : ℝ → ℝ) (w : Fin k → Fin m) (i : Fin k) (hm : 0 < m)
    (hpsi : psi ≠ 0) :
    (S : ℝ)⁻¹ * omega (rieszCycleGridPoint m (w i)) *
        rankRieszKernel S psi c (w i) (w (cycleSucc i))
      = ((S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)) *
        (omega (2 * offsetLatticePoint w i - 1) *
          (c * |offsetLatticePoint w i -
            offsetLatticePoint w (cycleSucc i)| ^ (-psi))) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  show (S : ℝ)⁻¹ * omega (rieszCycleGridPoint m (w i)) *
      (c * S ^ psi * (if Nat.dist (w i).val (w (cycleSucc i)).val = 0 then 0
        else (((Nat.dist (w i).val (w (cycleSucc i)).val : ℕ) : ℝ)) ^ (-psi)))
    = ((S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)) *
      (omega (rieszCycleGridPoint m (w i)) *
        (c * |offsetLatticePoint w i -
          offsetLatticePoint w (cycleSucc i)| ^ (-psi)))
  by_cases hdz : Nat.dist (w i).val (w (cycleSucc i)).val = 0
  · have habs0 :
        |offsetLatticePoint w i - offsetLatticePoint w (cycleSucc i)| = 0 := by
      rw [offsetLatticePoint_abs_sub m k w i hm, hdz]
      simp
    rw [if_pos hdz, habs0, Real.zero_rpow (neg_ne_zero.mpr hpsi)]
    ring
  · have hdistrel : (m : ℝ) *
        |offsetLatticePoint w i - offsetLatticePoint w (cycleSucc i)|
        = ((Nat.dist (w i).val (w (cycleSucc i)).val : ℕ) : ℝ) := by
      rw [offsetLatticePoint_abs_sub m k w i hm]
      field_simp
    have hkey : (((Nat.dist (w i).val (w (cycleSucc i)).val : ℕ) : ℝ)) ^ (-psi)
        = (m : ℝ) ^ (-psi) *
          |offsetLatticePoint w i - offsetLatticePoint w (cycleSucc i)| ^ (-psi) := by
      rw [← hdistrel, Real.mul_rpow hmR.le (abs_nonneg _)]
    rw [if_neg hdz, hkey]
    ring

/-- **Exact untruncated reindex identity.** With the real-distance
normalization the per-edge prefactor is the mesh-scale
`(S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)`; the diagonal rule forces `psi ≠ 0`. -/
theorem weightedRieszDiscreteCycleValue_eq_untruncatedOffsetLatticeSum
    (m K : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) (hm : 0 < m) (hpsi : psi ≠ 0) :
    weightedRieszDiscreteCycleValue m (K + 1) S psi c omega
      = ((S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)) ^ (K + 1)
        * untruncatedOffsetLatticeSum m (K + 1) psi c omega := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold weightedRieszDiscreteCycleValue untruncatedOffsetLatticeSum
  rw [matrixClosedWalkCoordinateSum_vertexTuple, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hprod : ∀ i : Fin (K + 1),
      weightedRieszDiscreteMatrix m S psi c omega (w i) (w (cycleSucc i))
        = ((S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)) *
          (omega (2 * offsetLatticePoint w i - 1) *
            (c * |offsetLatticePoint w i -
              offsetLatticePoint w (cycleSucc i)| ^ (-psi))) := by
    intro i
    rw [show weightedRieszDiscreteMatrix m S psi c omega (w i) (w (cycleSucc i))
          = (S : ℝ)⁻¹ * omega (rieszCycleGridPoint m (w i)) *
              rankRieszKernel S psi c (w i) (w (cycleSucc i)) from rfl]
    exact rankRieszKernel_edge_at_offsetPoint m (K + 1) S psi c omega w i hm
      hpsi
  have hint :
      unitCubeWeightedRieszIntegrand (K + 1) psi c omega (offsetLatticePoint w)
        = ∏ i : Fin (K + 1), omega (2 * offsetLatticePoint w i - 1) *
            (c * |offsetLatticePoint w i -
              offsetLatticePoint w (cycleSucc i)| ^ (-psi)) := by
    simp only [unitCubeWeightedRieszIntegrand, finCyclicSucc_eq_cycleSucc]
  have h2 : ∏ i : Fin (K + 1),
      weightedRieszDiscreteMatrix m S psi c omega (w i) (w (cycleSucc i))
    = ∏ i : Fin (K + 1), ((S : ℝ)⁻¹ * S ^ psi * (m : ℝ) ^ (-psi)) *
        (omega (2 * offsetLatticePoint w i - 1) *
          (c * |offsetLatticePoint w i -
            offsetLatticePoint w (cycleSucc i)| ^ (-psi))) :=
    Finset.prod_congr rfl fun i _ => hprod i
  rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hint]

end Hurst
