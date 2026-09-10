import Hurst.SecondChaosSeriesConvergence
import Hurst.TriangularApproximation

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

/-- Internal diagonal argument for a second-chaos limit.  Once every fixed
finite spectral truncation is obtained and the discarded spectral tail is
uniformly small in `L²`, convergence of the full triangular array follows.
This isolates the remaining work to deterministic spectral approximation of
the weighted mesh kernels. -/
theorem tendstoInDistribution_of_secondChaos_spectral_truncations
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)]
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Y : ∀ n, Omega n → ℝ) (YK : ℕ → ∀ n, Omega n → ℝ)
    (Q : Theta → ℝ) (lambda : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lambda)
    (hYmeas : ∀ n, AEMeasurable (Y n) (P n))
    (hYK : ∀ K, ∀ Z : ℕ → Theta → ℝ,
      (∀ j, AEMeasurable (Z j) P') → iIndepFun Z P' →
      (∀ j, P'.map (Z j) = gaussianReal 0 1) →
      TendstoInDistribution (YK K) atTop
        (secondChaosSeriesPartial lambda Z K) P P')
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ K, ∀ᶠ n in atTop,
      MemLp (fun x => Y n x - YK K n x) 2 (P n) ∧
      (∫ x, (Y n x - YK K n x) ^ 2 ∂P n) ≤ e K) :
    TendstoInDistribution Y atTop Q P P' := by
  rcases hQ.partial_tendstoInDistribution P' Q lambda with
    ⟨Z, hZmeas, hZi, hZlaw, hZlimit⟩
  exact triangular_L2_approximation P P' Y YK
    (fun K => secondChaosSeriesPartial lambda Z K) Q
    hYmeas (fun K => hYK K Z hZmeas hZi hZlaw)
    hZlimit e he hE

end Hurst
