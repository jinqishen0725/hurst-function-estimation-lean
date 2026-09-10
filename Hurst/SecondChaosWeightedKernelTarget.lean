import Hurst.ExternalSecondChaosLimit

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Exact remaining model-independent probability target after all
model-specific covariance and signed-weight conversions have been discharged.
The matrix represented by the mesh kernel is
`S⁻¹ * u_i * (S^psi * correlation_ij)`, while the corresponding centered
quadratic form is `S^(psi-1) * sum u_i (Y_i^2-1)`.

This target still requires an internal proof (for example by the spectral
series and moment argument in `direct_proofs/14_q1_long_memory_limit.md`).  It
is deliberately not labelled as a published theorem. -/
def GaussianQuadraticWeightedKernelContinuity : Prop :=
  ∀ (m : ℕ → ℕ)
    (v : ∀ n, Fin n → Lp ℂ 2 (volume : Measure ℝ))
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ (Fin n))
    (S : ℕ → ℝ) (psi c : ℝ)
    (u : ∀ n, Fin (m n) → ℝ) (omega : ℝ → ℝ)
    (P' : Measure ℝ) [IsProbabilityMeasure P'],
    0 < psi → psi < 1 / 2 →
    (∀ᶠ n in atTop, 0 < S n) → Tendsto S atTop atTop →
    Tendsto (fun n : ℕ => (m n : ℝ) / S n) atTop (𝓝 2) →
    (∀ᶠ n in atTop, ∀ i, ∑ j, a n i j • v n j ≠ 0) →
    Tendsto (fun n : ℕ =>
      realScaleMeshEnergy (S n) (fun i j =>
        u n i * (S n ^ psi * featureCorrelation (v n) (a n i) (a n j)) -
          omega (2 * (((i.val + 1 : ℕ) : ℝ) / (m n : ℝ)) - 1) *
            rankRieszKernel (S n) psi c i j)) atTop (𝓝 0) →
    IsWeightedRieszSecondChaosLaw P' id psi c omega →
    TendstoInDistribution (fun n x => S n ^ (psi - 1) * ∑ i,
      u n i * ((standardizedFeatureObservation (v n) (a n i) x) ^ 2 - 1))
      atTop id (fun n => featureGaussian (v n)) P'

end Hurst
