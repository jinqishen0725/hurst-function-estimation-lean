import Hurst.ExternalSecondChaosLimit
import Hurst.MatrixFrobeniusTrace

noncomputable section

open Filter Matrix
open scoped Topology Matrix.Norms.Frobenius

namespace Hurst

/-- The right-endpoint grid on `[-1,1]` used in the article's active-row
parameterization.  Its mesh is `2 / m`; when `m / S -> 2`, this is
asymptotically the same as the operator mesh `1 / S`. -/
def rieszCycleGridPoint (m : ℕ) (i : Fin m) : ℝ :=
  2 * (((i.val + 1 : ℕ) : ℝ) / (m : ℝ)) - 1

theorem rieszCycleGridPoint_mem_Icc {m : ℕ} (hm : 0 < m) (i : Fin m) :
    rieszCycleGridPoint m i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hiR : (((i.val + 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
  have hfrac0 : 0 ≤ (((i.val + 1 : ℕ) : ℝ)) / (m : ℝ) := by positivity
  have hfrac1 : (((i.val + 1 : ℕ) : ℝ)) / (m : ℝ) ≤ 1 :=
    (div_le_one hmR).mpr hiR
  constructor <;> unfold rieszCycleGridPoint <;> linarith

/-- The finite weighted Riesz matrix whose powers give the discrete cyclic
traces.  The factor `S⁻¹` is the cell volume.  The weight is placed on the
left endpoint, so this matrix need not be symmetric when the equivalent
kernel changes sign. -/
def weightedRieszDiscreteMatrix (m : ℕ) (S psi c : ℝ)
    (omega : ℝ → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => S⁻¹ * omega (rieszCycleGridPoint m i) *
    rankRieszKernel S psi c i j

theorem weightedRieszDiscreteMatrix_apply (m : ℕ) (S psi c : ℝ)
    (omega : ℝ → ℝ) (i j : Fin m) :
    weightedRieszDiscreteMatrix m S psi c omega i j =
      S⁻¹ * omega (rieszCycleGridPoint m i) *
        rankRieszKernel S psi c i j := rfl

/-- The Riesz matrix is symmetric, including its deliberately zero diagonal. -/
theorem rankRieszKernel_symm {m : ℕ} (S psi c : ℝ) (i j : Fin m) :
    rankRieszKernel S psi c i j = rankRieszKernel S psi c j i := by
  unfold rankRieszKernel rankRieszUnitKernel
  rw [Nat.dist_comm]

/-- Recursive coordinate sum over paths of exactly `k` matrix edges from
`i` to `j`.  Unlike a matrix-power notation, this exposes every intermediate
finite summation needed by the cyclic Riemann sum. -/
def matrixPathCoordinateSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℕ → ι → ι → ℝ
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j => ∑ x : ι, matrixPathCoordinateSum A k i x * A x j

theorem matrixPathCoordinateSum_eq_pow_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (k : ℕ) (i j : ι) :
    matrixPathCoordinateSum A k i j = (A ^ k) i j := by
  induction k generalizing i j with
  | zero => rw [matrixPathCoordinateSum, pow_zero, Matrix.one_apply]
  | succ k ih =>
      rw [matrixPathCoordinateSum, pow_succ, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih]

/-- The fully finite closed-walk coordinate sum. -/
def matrixClosedWalkCoordinateSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  ∑ i : ι, matrixPathCoordinateSum A k i i

/-- Every finite closed-walk coordinate sum is exactly the corresponding
matrix-power trace.  This is the algebraic cyclic-coordinate formula, valid
without symmetry or positivity assumptions. -/
theorem matrixClosedWalkCoordinateSum_eq_trace_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (k : ℕ) :
    matrixClosedWalkCoordinateSum A k = Matrix.trace (A ^ k) := by
  simp only [matrixClosedWalkCoordinateSum,
    matrixPathCoordinateSum_eq_pow_apply, Matrix.trace, Matrix.diag_apply]

/-- The discrete weighted Riesz cyclic functional, in an explicitly
coordinate-based form. -/
def weightedRieszDiscreteCycleValue (m k : ℕ) (S psi c : ℝ)
    (omega : ℝ → ℝ) : ℝ :=
  matrixClosedWalkCoordinateSum
    (weightedRieszDiscreteMatrix m S psi c omega) k

/-- Exact identification of the discrete cyclic functional with a power
trace.  No limiting or regularity hypothesis is used here. -/
theorem weightedRieszDiscreteCycleValue_eq_trace_pow
    (m k : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) :
    weightedRieszDiscreteCycleValue m k S psi c omega =
      Matrix.trace ((weightedRieszDiscreteMatrix m S psi c omega) ^ k) := by
  exact matrixClosedWalkCoordinateSum_eq_trace_pow _ _

/-- The order-two cyclic trace is the expected double coordinate sum. -/
theorem matrixClosedWalkCoordinateSum_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    matrixClosedWalkCoordinateSum A 2 =
      ∑ i : ι, ∑ j : ι, A i j * A j i := by
  rw [matrixClosedWalkCoordinateSum_eq_trace_pow]
  simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- At order two, symmetry of the Riesz factor places one signed weight at
each vertex of the two-cycle. -/
theorem weightedRieszDiscreteCycleValue_two
    (m : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) :
    weightedRieszDiscreteCycleValue m 2 S psi c omega =
      ∑ i : Fin m, ∑ j : Fin m,
        S⁻¹ ^ 2 *
          (omega (rieszCycleGridPoint m i) *
            omega (rieszCycleGridPoint m j)) *
          rankRieszKernel S psi c i j ^ 2 := by
  rw [weightedRieszDiscreteCycleValue, matrixClosedWalkCoordinateSum_two]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [weightedRieszDiscreteMatrix_apply,
    weightedRieszDiscreteMatrix_apply, ← rankRieszKernel_symm S psi c i j]
  ring

/-- The part of the order-two cycle lying in a lattice band of radius `R`.
This is the discrete counterpart of a shrinking neighborhood of the
singular diagonal. -/
def weightedRieszDiscreteBandCycleTwo
    (m R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) : ℝ :=
  S⁻¹ ^ 2 * ∑ i : Fin m,
    ∑ j ∈ Finset.univ.filter
      (fun j : Fin m => Nat.dist j.val i.val ≤ R),
      (omega (rieszCycleGridPoint m i) *
        omega (rieszCycleGridPoint m j)) *
        rankRieszKernel S psi c i j ^ 2

/-- A bounded signed weight cannot make the absolute order-two diagonal-band
contribution larger than `B²` times the unweighted Riesz energy. -/
theorem abs_weightedRieszDiscreteBandCycleTwo_le
    (m : ℕ) (S psi c B : ℝ) (Rnat : ℕ) (omega : ℝ → ℝ)
    (hB : 0 ≤ B)
    (homega : ∀ i : Fin m, |omega (rieszCycleGridPoint m i)| ≤ B) :
    |weightedRieszDiscreteBandCycleTwo m Rnat S psi c omega| ≤
      B ^ 2 * realScaleMeshBandEnergy S Rnat
        (rankRieszKernel S psi c : Fin m → Fin m → ℝ) := by
  have hterm (i j : Fin m) :
      |(omega (rieszCycleGridPoint m i) *
          omega (rieszCycleGridPoint m j)) *
          rankRieszKernel S psi c i j ^ 2| ≤
        B ^ 2 * rankRieszKernel S psi c i j ^ 2 := by
    have hwprod :
        |omega (rieszCycleGridPoint m i)| *
            |omega (rieszCycleGridPoint m j)| ≤ B * B :=
      mul_le_mul (homega i) (homega j) (abs_nonneg _) hB
    calc
      _ = |omega (rieszCycleGridPoint m i)| *
          |omega (rieszCycleGridPoint m j)| *
            rankRieszKernel S psi c i j ^ 2 := by
        rw [abs_mul, abs_mul, abs_sq]
      _ ≤ (B * B) * rankRieszKernel S psi c i j ^ 2 :=
        mul_le_mul_of_nonneg_right hwprod (sq_nonneg _)
      _ = _ := by ring
  have hsum :
      |∑ i : Fin m,
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin m => Nat.dist j.val i.val ≤ Rnat),
            (omega (rieszCycleGridPoint m i) *
              omega (rieszCycleGridPoint m j)) *
              rankRieszKernel S psi c i j ^ 2| ≤
        B ^ 2 * ∑ i : Fin m,
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin m => Nat.dist j.val i.val ≤ Rnat),
            rankRieszKernel S psi c i j ^ 2 := by
    calc
      _ ≤ ∑ i : Fin m,
          |∑ j ∈ Finset.univ.filter
            (fun j : Fin m => Nat.dist j.val i.val ≤ Rnat),
            (omega (rieszCycleGridPoint m i) *
              omega (rieszCycleGridPoint m j)) *
              rankRieszKernel S psi c i j ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m,
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin m => Nat.dist j.val i.val ≤ Rnat),
            |(omega (rieszCycleGridPoint m i) *
              omega (rieszCycleGridPoint m j)) *
              rankRieszKernel S psi c i j ^ 2| := by
        gcongr with i
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m,
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin m => Nat.dist j.val i.val ≤ Rnat),
            B ^ 2 * rankRieszKernel S psi c i j ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hterm i j
      _ = _ := by simp only [Finset.mul_sum]
  rw [weightedRieszDiscreteBandCycleTwo, abs_mul,
    abs_of_nonneg (sq_nonneg _)]
  unfold realScaleMeshBandEnergy
  have hs := mul_le_mul_of_nonneg_left hsum (sq_nonneg S⁻¹)
  nlinarith

/-- Concrete near-diagonal bound for the order-two cyclic functional.  This
is the singular-diagonal estimate used before sending the lattice bandwidth
to zero. -/
theorem abs_weightedRieszDiscreteBandCycleTwo_le_rieszRate
    (m R : ℕ) (S psi c B : ℝ) (omega : ℝ → ℝ)
    (hS : 0 < S) (hpsi : 0 ≤ psi) (hB : 0 ≤ B)
    (homega : ∀ i : Fin m, |omega (rieszCycleGridPoint m i)| ≤ B) :
    |weightedRieszDiscreteBandCycleTwo m R S psi c omega| ≤
      B ^ 2 * c ^ 2 *
        (S ^ (2 * psi - 2) * (m : ℝ) * (2 * (R : ℝ) + 1)) := by
  calc
    _ ≤ B ^ 2 * realScaleMeshBandEnergy S R
        (rankRieszKernel S psi c : Fin m → Fin m → ℝ) :=
      abs_weightedRieszDiscreteBandCycleTwo_le
        m S psi c B R omega hB homega
    _ ≤ B ^ 2 * (c ^ 2 *
        (S ^ (2 * psi - 2) * (m : ℝ) * (2 * (R : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left
        (rankRieszKernel_band_energy_le S psi c hS hpsi) (sq_nonneg B)
    _ = _ := by ring

/-- Along a triangular array, the weighted order-two contribution of a
lattice band vanishes whenever the standard Riesz band rate vanishes.  This
form admits signed weights and a nonintegral real mesh scale. -/
theorem weightedRieszDiscreteBandCycleTwo_tendsto_zero
    (m R : ℕ → ℕ) (S : ℕ → ℝ) (psi c B : ℝ)
    (omega : ℝ → ℝ) (hpsi : 0 ≤ psi) (hB : 0 ≤ B)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (homega : ∀ᶠ n in atTop, ∀ i : Fin (m n),
      |omega (rieszCycleGridPoint (m n) i)| ≤ B)
    (hcut : Tendsto (fun n =>
      S n ^ (2 * psi - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto (fun n => weightedRieszDiscreteBandCycleTwo
      (m n) (R n) (S n) psi c omega) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop,
      |weightedRieszDiscreteBandCycleTwo
        (m n) (R n) (S n) psi c omega| ≤
        (B ^ 2 * c ^ 2) *
          (S n ^ (2 * psi - 2) * (m n : ℝ) *
            (2 * (R n : ℝ) + 1)) := by
    filter_upwards [hS, homega] with n hSn hωn
    simpa only [mul_assoc] using
      abs_weightedRieszDiscreteBandCycleTwo_le_rieszRate
        (m n) (R n) (S n) psi c B omega hSn hpsi hB hωn
  have hzero : Tendsto (fun n =>
      (B ^ 2 * c ^ 2) *
        (S n ^ (2 * psi - 2) * (m n : ℝ) *
          (2 * (R n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcut.const_mul (B ^ 2 * c ^ 2)
  have habs := squeeze_zero'
    (Eventually.of_forall (fun n =>
      abs_nonneg (weightedRieszDiscreteBandCycleTwo
        (m n) (R n) (S n) psi c omega))) hbound hzero
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, Real.norm_eq_abs] using habs

/-- The diagonal-band theorem with boundedness stated on the continuum
interval rather than separately at every grid point. -/
theorem weightedRieszDiscreteBandCycleTwo_tendsto_zero_of_boundedOn
    (m R : ℕ → ℕ) (S : ℕ → ℝ) (psi c B : ℝ)
    (omega : ℝ → ℝ) (hpsi : 0 ≤ psi) (hB : 0 ≤ B)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (homega : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |omega x| ≤ B)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (hcut : Tendsto (fun n =>
      S n ^ (2 * psi - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto (fun n => weightedRieszDiscreteBandCycleTwo
      (m n) (R n) (S n) psi c omega) atTop (𝓝 0) := by
  apply weightedRieszDiscreteBandCycleTwo_tendsto_zero
    m R S psi c B omega hpsi hB hS
  · filter_upwards [hm] with n hmn
    intro i
    exact homega _ (rieszCycleGridPoint_mem_Icc hmn i)
  · exact hcut

/-- The exact remaining deterministic analytic statement: all fixed cyclic
traces of the right-endpoint Riesz matrices converge to the singular cyclic
integrals.  Separating this predicate prevents the operator/probability layer
from concealing the multidimensional singular-quadrature argument.

The assumptions `0 < psi < 1/2`, bounded continuity of `omega`, and
`m / S -> 2` belong in proofs that construct this predicate; they are not
silently bundled into its definition. -/
def HasWeightedRieszCycleQuadrature
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ)
    (omega : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    Tendsto (fun n => weightedRieszDiscreteCycleValue
      (m n) k (S n) psi c omega) atTop
      (𝓝 (weightedRieszCycleIntegral k psi c omega))

/-- Precisely scoped analytic theorem still needed to construct
`HasWeightedRieszCycleQuadrature` from elementary assumptions.  The separate
`S -> infinity` hypothesis is essential: `m / S -> 2` alone does not force a
refining grid.  Continuity and boundedness are required only on `[-1,1]`,
because both the grid and the indicated limit kernel live there. -/
def WeightedRieszCycleQuadratureAnalyticStatement : Prop :=
  ∀ (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ) (omega : ℝ → ℝ),
    0 < psi → psi < 1 / 2 →
    ContinuousOn omega (Set.Icc (-1 : ℝ) 1) →
    (∃ B ≥ 0, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |omega x| ≤ B) →
    (∀ᶠ n in atTop, 0 < S n) →
    Tendsto S atTop atTop →
    Tendsto (fun n : ℕ => (m n : ℝ) / S n) atTop (𝓝 2) →
    HasWeightedRieszCycleQuadrature m S psi c omega

/-- Once the pure singular quadrature statement is available, convergence
of every finite weighted Riesz power trace follows immediately from the
exact finite-dimensional identity above. -/
theorem weightedRieszDiscrete_trace_pow_tendsto
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ) (omega : ℝ → ℝ)
    (hquad : HasWeightedRieszCycleQuadrature m S psi c omega)
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n => Matrix.trace
      ((weightedRieszDiscreteMatrix (m n) (S n) psi c omega) ^ k))
      atTop (𝓝 (weightedRieszCycleIntegral k psi c omega)) := by
  simpa only [weightedRieszDiscreteCycleValue_eq_trace_pow] using hquad k hk

/-- If `lambda` has the intended Riesz spectrum, the finite traces converge
to its power sums.  This is the deterministic bridge consumed by the
finite-dimensional spectral approximation. -/
theorem weightedRieszDiscrete_trace_pow_tendsto_spectrum
    (m : ℕ → ℕ) (S : ℕ → ℝ) (psi c : ℝ) (omega : ℝ → ℝ)
    (lambda : ℕ → ℝ)
    (hquad : HasWeightedRieszCycleQuadrature m S psi c omega)
    (hspec : IsWeightedRieszSpectrum psi c omega lambda)
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n => Matrix.trace
      ((weightedRieszDiscreteMatrix (m n) (S n) psi c omega) ^ k))
      atTop (𝓝 (∑' j, lambda j ^ k)) := by
  have hvalue : (∑' j, lambda j ^ k) =
      weightedRieszCycleIntegral k psi c omega :=
    (hspec.2 k hk).tsum_eq
  rw [hvalue]
  exact weightedRieszDiscrete_trace_pow_tendsto m S psi c omega hquad k hk

end Hurst
