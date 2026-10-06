import Hurst.CompressionGeneralK
import Hurst.IntervalL2Basis

/-!
# The actual equivalent-kernel spectral theorem with all internal premises closed

The basis is constructed inside `IntervalL2Basis`. Distance-power measurability
and integrability follow from the model window. The only hypotheses below are
`0 < psi`, `2 * psi < 1`, and `0 < c`; no `hconst`, supplied Hilbert basis,
or analytic regularity package remains as a caller obligation.
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section
namespace HS

/-- M1 spectral existence for the actual equivalent kernel, assuming only the
true model parameter window. All basis and integrability premises are discharged. -/
theorem exists_weightedRieszSpectrum_equiv_closed (r : ℕ) {psi c : ℝ}
    (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1) (hc : 0 < c)
    :
    ∃ (ι : Type) (v : ι → L2) (κ : ι → ℝ) (B : L2 →L[ℝ] L2) (val : ℕ → ℝ)
      (vec : ℕ → L2) (MR : ℝ) (hMR : ∀ᵐ x ∂vol, |Hurst.equivalentKernel r x| ≤ MR)
      (hbd : ∀ x : ℝ, |Hurst.equivalentKernel r x| ≤ MR),
      Orthonormal ℝ v
      ∧ (∀ i, TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) (v i) = κ i • v i)
      ∧ ((span ℝ (Set.range v))ᗮ = ⊥)
      ∧ (∀ i, 0 ≤ κ i)
      ∧ Summable (fun i => κ i ^ 2)
      ∧ IsCompactOperator B
      ∧ (↑B : L2 →ₗ[ℝ] L2).IsSymmetric
      ∧ (∀ i j : ι, inner ℝ (v i) (B (v j))
          = Real.sqrt (κ i * κ j) * inner ℝ (v i)
              ((mulOperator (Hurst.equivalentKernel r)
                (measurable_equivalentKernel r) hMR) (v j)))
      ∧ (∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ g : HilbertBasis ℕ ℝ L2,
          Summable (fun p : ℕ × ℕ => (inner ℝ (g p.1) (B (g p.2))) ^ 2)
            ∧ (∑' p : ℕ × ℕ, (inner ℝ (g p.1) (B (g p.2))) ^ 2) ≤ Cbar)
      ∧ IsDiagEnum (↑B : L2 →ₗ[ℝ] L2) val vec
      ∧ (∀ μ : ℝ, Module.End.HasEigenvalue (↑B : L2 →ₗ[ℝ] L2) μ → μ ≠ 0 →
          Nat.card {m : ℕ // val m = μ}
            = Module.finrank ℝ (Module.End.eigenspace (↑B : L2 →ₗ[ℝ] L2) μ))
      ∧ Summable (fun m : ℕ => val m ^ 2)
      ∧ ∀ k : ℕ, 2 ≤ k → HasSum (fun m : ℕ => val m ^ k)
          (Hurst.weightedRieszCycleIntegral k psi c (Hurst.equivalentKernel r)) := by
  apply exists_weightedRieszSpectrum_min_equiv r hpsi0 hpsi2 hc
  · exact (measurable_abs_sub_rpow (r := psi)).aestronglyMeasurable
  · simpa only [neg_mul] using
      (integrable_abs_sub_rpow_vol2 (s := 2 * psi) (by positivity) hpsi2)
  · exact intervalL2Basis

end HS
