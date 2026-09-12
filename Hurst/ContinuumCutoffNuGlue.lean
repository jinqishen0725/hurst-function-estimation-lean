import Hurst.ContinuumCutoffAssembly
import Hurst.DominatorIntegrability
import Hurst.TwoFactorShiftBound

/-!
# Nu-glue: `HasContinuumRieszCutoffRemoval` from the uniform shift bounds

The peeling integrability theorem `continuumCutoffDominator_integrable`
consumes the uniform one-factor and two-factor shifted singular integral
bounds as hypotheses `hν1`/`hν2`.  Those bounds are exactly
`single_factor_bound` and `two_factor_shift_bound` of
`Hurst.TwoFactorShiftBound`.  This file performs the instantiation and
packages it with `hasContinuumRieszCutoffRemoval_of_integrable_dominator`,
closing `HasContinuumRieszCutoffRemoval` — the continuum cutoff-removal
predicate — as a theorem under ordinary hypotheses.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Hurst

/-- `HasContinuumRieszCutoffRemoval` as a theorem: the dominator is
integrable by the peeling bound instantiated with the uniform shift
bounds, and the dominated-convergence assembly removes the cutoff. -/
theorem hasContinuumRieszCutoffRemoval (psi c : ℝ) (omega : ℝ → ℝ)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1) (homega : Continuous omega)
    (B_omega : ℝ) (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega) :
    HasContinuumRieszCutoffRemoval psi c omega := by
  refine hasContinuumRieszCutoffRemoval_of_integrable_dominator psi c omega
    hpsi1 homega ?_
  intro k hk
  obtain ⟨ν₁, hν₁pos, hν₁⟩ := single_factor_bound psi hpsi1 (by linarith)
  obtain ⟨ν₂, hν₂pos, hν₂⟩ := two_factor_shift_bound psi hpsi1 hpsi2
  have homega_meas : Measurable omega := homega.measurable
  exact continuumCutoffDominator_integrable k psi c omega B_omega ν₁ ν₂ hk
    hpsi1 hpsi2 homega_meas homegaB hν₁ hν₂
    ⟨le_of_lt hν₁pos, le_of_lt hν₂pos⟩

end Hurst
