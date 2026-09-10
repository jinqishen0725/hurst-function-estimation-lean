import Hurst.DirectBiasRepair
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise
namespace Hurst

theorem matrix_inverse_uniform_near_compact {r : ℕ}
    (S : Set (Matrix (Fin r) (Fin r) ℝ)) (hS : IsCompact S)
    (hdet : ∀ A ∈ S, A.det ≠ 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ A ∈ S, ∀ B : Matrix (Fin r) (Fin r) ℝ,
      ‖B - A‖ ≤ δ → IsUnit B.det ∧ ∀ i j, |B⁻¹ i j| ≤ C := by
  have hopen : IsOpen {A : Matrix (Fin r) (Fin r) ℝ | A.det ≠ 0} :=
    isOpen_ne.preimage continuous_id.matrix_det
  obtain ⟨δ₁, hδ₁, hsubset⟩ := hS.exists_cthickening_subset_open hopen hdet
  obtain ⟨δ₂, hδ₂, hcompact⟩ := hS.exists_isCompact_cthickening
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hcompactδ : IsCompact (cthickening δ S) :=
    hcompact.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_right _ _) S)
  have hnonzero : ∀ A ∈ cthickening δ S, A.det ≠ 0 := fun A hA =>
    hsubset (cthickening_mono (min_le_left _ _) S hA)
  have hcont : ContinuousOn (Inv.inv : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ)
      (cthickening δ S) := by
    intro A hA
    apply (continuousAt_matrix_inv A _).continuousWithinAt
    convert! continuousAt_inv₀ (hnonzero A hA) using 1
    exact funext (fun x : ℝ => Ring.inverse_eq_inv x)
  obtain ⟨C, hC⟩ := hcompactδ.exists_bound_of_continuousOn hcont
  refine ⟨δ, hδ, max C 0, le_max_right _ _, ?_⟩
  intro A hA B hBA
  have hB : B ∈ cthickening δ S := mem_cthickening_of_dist_le B A δ S hA (by simpa [dist_eq_norm] using hBA)
  refine ⟨isUnit_iff_ne_zero.mpr (hnonzero B hB), ?_⟩
  intro i j
  let V : Matrix (Fin r) (Fin r) ℝ := B⁻¹
  exact (norm_le_pi_norm (V i) j).trans ((norm_le_pi_norm V i).trans ((hC B hB).trans (le_max_left _ _)))

end Hurst
