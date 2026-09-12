import Mathlib
import Hurst.DiscreteRieszCycleBridge
import Hurst.TruncatedRieszCycleBridge
import Hurst.EdgeComparison
import Hurst.MeshFactorizationLimit
import Hurst.TruncatedCycleBound
import Hurst.MixedTraceBound
import Hurst.VertexTupleTrace
import Hurst.ProductTelescope

/-!
# Assembly: uniform discrete Riesz cutoff removal (partial rung)

This file assembles `Hurst.HasUniformDiscreteRieszCutoffRemoval`.  Write `A`
for the untruncated weighted Riesz matrix, `T` for the truncated one,
`rho = (2*S/m)^psi` for the mesh correction factor and `Dg = A - rho * T` for
the mesh-difference matrix: off the band and off the diagonal `Dg` vanishes
exactly (`rankRieszKernelEqRhoMulTruncated`), and on the band its entries are
`S^(-1) * B_omega * |c| * S^psi * d^(-psi)` (landed here).

Status (documented deviation from the requested full assembly):

* Landed here: the mesh-difference matrix, its exact entry structure, and the
  per-entry band bound `abs_rieszMeshDiffMatrix_le_of_dist`.
* The intended remaining route, verified on paper: for the vertex-tuple forms
  (`matrixClosedWalkCoordinateSum_vertexTuple`, `prod_telescope`),
  `|cycleValue(A) - cycleValue(T)| <= |rho^k - 1| * mu^k
     + k * ||Dg||_F * max(rho * mu, ||Dg||_F)^(k-1)` with
  `mu = (m/S) * (|c| * B_omega * cutoff^(-psi))` (Frobenius word/binomial
  expansion of `A^k = (rho*T + Dg)^k`, all non-rho terms carrying at least one
  `||Dg||_F` factor).  As `n -> infinity`: `|rho - 1| -> 0`
  (`tendsto_mesh_correction_rpow`) and `sqrt m / S -> 0` kill the scalar and
  diagonal parts; the band part of `||Dg||_F` is small in the cutoff *only*
  with the sharp weighted band sum
  `sum_{d <= D} d^(-2 psi) <= C_psi * D^(1-2 psi)` for `2 psi < 1` (the crude
  per-entry bound grows like `S^psi * sqrt(cutoff)` and does not suffice).
  The final `HasUniformDiscreteRieszCutoffRemoval` epsilon-assembly and this
  power-sum lemma remain to be supplied.
-/

noncomputable section

open Set Filter Matrix
open scoped Matrix.Norms.Frobenius Topology

namespace Hurst

/-- Mesh correction factor `rho = (2*S/m)^psi`. -/
def meshRho (m : ℕ) (S psi : ℝ) : ℝ := (2 * S / (m : ℝ)) ^ psi

/-- Truncated Frobenius scale `mu = (m/S) * (|c| * B_omega * cutoff^(-psi))`. -/
def truncScale (m R : ℕ) (S psi c B_omega : ℝ) : ℝ :=
  ((m : ℝ) / S) * (|c| * B_omega * (rieszCycleCutoff R) ^ (-psi))

/-- The mesh-difference matrix `A - rho * T`; this is the matrix whose
Frobenius norm must be small in the cutoff for the uniform removal. -/
def rieszMeshDiffMatrix (m R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  weightedRieszDiscreteMatrix m S psi c omega
    - meshRho m S psi • weightedTruncatedRieszDiscreteMatrix m R S psi c omega

/-- Entrywise expansion of the mesh-difference matrix. -/
theorem rieszMeshDiffMatrix_apply (m R : ℕ) (S psi c : ℝ) (omega : ℝ → ℝ)
    (i j : Fin m) :
    rieszMeshDiffMatrix m R S psi c omega i j
      = (S : ℝ)⁻¹ * omega (rieszCycleGridPoint m i) *
          (rankRieszKernel S psi c i j
            - meshRho m S psi * truncatedRieszKernel R psi c
                (rieszCycleGridPoint m i) (rieszCycleGridPoint m j)) := by
  unfold rieszMeshDiffMatrix weightedRieszDiscreteMatrix
    weightedTruncatedRieszDiscreteMatrix meshRho
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Per-entry band bound: on the band with `Nat.dist >= 1` the mesh-difference
entry is at most `S^(-1) * B_omega * |c| * S^psi * d^(-psi)` (by
`rankRieszKernelTruncatedComparison`; off the band it vanishes exactly). -/
theorem abs_rieszMeshDiffMatrix_le_of_dist {m R : ℕ} {S psi c B_omega : ℝ}
    (hS : 0 < S) (hpsi : 0 < psi) (hm : 0 < m) (omega : ℝ → ℝ)
    (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (i j : Fin m) (hD : 1 ≤ Nat.dist i.val j.val)
    (hband : (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ)
        < rieszCycleCutoff R) :
    |rieszMeshDiffMatrix m R S psi c omega i j|
      ≤ ((S : ℝ)⁻¹ * B_omega * |c|) * S ^ psi
          * ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi) := by
  have hgi : rieszCycleGridPoint m i ∈ Icc (-1 : ℝ) 1 :=
    rieszCycleGridPoint_mem_Icc hm i
  have hw : |omega (rieszCycleGridPoint m i)| ≤ B_omega := homegaB _ hgi
  have hcmp := rankRieszKernelTruncatedComparison (R := R) (psi := psi)
    (c := c) (m := m) (S := S) hS (by exact_mod_cast hm) hpsi i j hD
  rw [if_pos hband, mul_one] at hcmp
  have hinv : 0 ≤ (S : ℝ)⁻¹ := inv_nonneg.2 hS.le
  have hrpow : 0 ≤ ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) (-psi)
  have hfac : 0 ≤ |c| * S ^ psi * ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi) :=
    mul_nonneg (mul_nonneg (abs_nonneg c) (Real.rpow_nonneg hS.le psi)) hrpow
  have hassoc : (S : ℝ)⁻¹ * |omega (rieszCycleGridPoint m i)| *
      |rankRieszKernel S psi c i j - meshRho m S psi *
        truncatedRieszKernel R psi c (rieszCycleGridPoint m i)
          (rieszCycleGridPoint m j)|
      = (S : ℝ)⁻¹ * (|omega (rieszCycleGridPoint m i)| *
        |rankRieszKernel S psi c i j - meshRho m S psi *
          truncatedRieszKernel R psi c (rieszCycleGridPoint m i)
            (rieszCycleGridPoint m j)|) := by ring
  have h2 : ((S : ℝ)⁻¹ * B_omega * |c|) * S ^ psi
        * ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi)
      = (S : ℝ)⁻¹ * (B_omega * (|c| * S ^ psi *
          ((Nat.dist i.val j.val : ℕ) : ℝ) ^ (-psi))) := by ring
  rw [rieszMeshDiffMatrix_apply, abs_mul, abs_mul, abs_of_nonneg hinv,
    hassoc, h2]
  have hBnonneg : 0 ≤ B_omega := by
    linarith [abs_nonneg (omega (rieszCycleGridPoint m i))]
  refine mul_le_mul_of_nonneg_left
    (mul_le_mul hw hcmp (abs_nonneg _) hBnonneg) hinv

/-- Off the band (and with `Nat.dist >= 1`) the mesh-difference entry vanishes
exactly: this is Deliverable 1 of `Hurst.EdgeComparison` at the level of the
normalized matrix entries. -/
theorem rieszMeshDiffMatrix_apply_of_not_band {m R : ℕ} {S psi c : ℝ}
    (hS : 0 < S) (hm : 0 < m) (omega : ℝ → ℝ)
    (i j : Fin m) (hD : 1 ≤ Nat.dist i.val j.val)
    (hfar : rieszCycleCutoff R ≤
      (2 : ℝ) / (m : ℝ) * ((Nat.dist i.val j.val : ℕ) : ℝ)) :
    rieszMeshDiffMatrix m R S psi c omega i j = 0 := by
  have h := rankRieszKernelEqRhoMulTruncated (R := R) (psi := psi) (c := c)
    hS hm i j hfar
  rw [rieszMeshDiffMatrix_apply, h]
  simp only [meshRho]
  ring

end Hurst
