import Hurst.DiscreteRieszCycleBridge
import Hurst.TruncatedRieszCycleBridge
import Hurst.FixedCutoffReindexAssembly
import Hurst.BandRemovalComplete
import Hurst.ContinuumCutoffNuGlue

/-!
# The weighted Riesz cycle quadrature for the actual data, as a theorem

All three cutoff predicates are theorems by now:
`fixedCutoffMatrixLatticeReindex` (fixed-cutoff lattice reindexing),
`hasUniformDiscreteRieszCutoffRemoval` (discrete band removal), and
`hasContinuumRieszCutoffRemoval` (continuum cutoff removal).  This file
assembles them, through the elementary bridges already in the repository,
into `HasWeightedRieszCycleQuadrature` under the ordinary hypotheses of
the long-memory regime.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Hurst

theorem hasWeightedRieszCycleQuadrature_instance (m : ℕ → ℕ) (S : ℕ → ℝ)
    (psi c B_omega : ℝ) (omega : ℝ → ℝ)
    (hmtop : Tendsto (fun n => m n) atTop atTop)
    (hMS : Tendsto (fun n => (m n : ℝ) / S n) atTop (𝓝 2))
    (hpos : ∀ᶠ n in atTop, 0 < S n ∧ 0 < m n)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (homega : Continuous omega)
    (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    HasWeightedRieszCycleQuadrature m S psi c omega := by
  refine hasWeightedRieszCycleQuadrature_of_truncation m S psi c omega
    (hasFixedCutoffRieszCycleQuadrature_of_lattice m S psi c omega homega hmtop
      (fixedCutoffMatrixLatticeReindex m S psi c omega B_omega hmtop hMS hpos
        (le_of_lt hpsi1) homegaB))
    (hasUniformDiscreteRieszCutoffRemoval m S psi c B_omega omega hmtop hMS
      hpos hpsi1 hpsi2 homegaB)
    (hasContinuumRieszCutoffRemoval psi c omega hpsi1 hpsi2 homega B_omega
      homegaB)

end Hurst
