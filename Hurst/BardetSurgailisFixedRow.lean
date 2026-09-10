import Hurst.ShortMemoryVariancePositive
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- **External input (exact published theorem).** Bardet--Surgailis,
"Moment bounds and central limit theorems for Gaussian subordinated arrays",
JMVA 114 (2013), Theorem 1(ii), scalar (`ν = 1`) polynomial specialization.

The row indexed by `n` below has exactly `n` variables and is normalized by
`n⁻¹/²`.  The hypotheses are precisely (3.1), (3.2), (3.9), and (3.10): a
uniform correlation-power row bound, a uniform averaged far-lag tail, uniform
Gaussian-L2 convergence to a continuous profile, and convergence to a
strictly positive variance.  The Hilbert feature representation merely
constructs the centered standardized Gaussian row; it adds no probabilistic
assumption.

All passage from the paper's exact row length to the active local-window row
is kept outside this definition and proved in Lean. -/
def BardetSurgailisTheoremOnePartTwoScalarPolynomialHilbert : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rank : ℕ) (_hrank : 1 ≤ rank)
    (v : ∀ n, Fin n → E) (P : ∀ n, Fin n → Polynomial ℝ)
    (φ : ℝ → ℝ → ℝ) (V : ℝ),
    (∀ n i, ‖v n i‖ = 1) →
    (∀ n i, (∫ z : ℝ, (P n i).eval z ∂gaussianReal 0 1) = 0) →
    (∀ n i k, k < rank →
      (∫ z : ℝ, (P n i).eval z * (gaussianHermite k).eval z
        ∂gaussianReal 0 1) = 0) →
    (∃ C ≥ 0, ∀ n i,
      ∑ j, |featureCorrelation (v n)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)| ^ rank ≤ C) →
    (∀ ε > 0, ∃ K : ℕ, ∀ n : ℕ,
      (n : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist i.val j.val then
          |featureCorrelation (v n)
            (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)| ^ rank else 0) ≤ ε) →
    (∀ τ, MemLp (φ τ) 2 (gaussianReal 0 1)) →
    (∀ τ, (∫ z : ℝ, φ τ z ∂gaussianReal 0 1) = 0) →
    (∀ ε > 0, ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1, |s - t| < η →
        (∫ z : ℝ, (φ s z - φ t z) ^ 2 ∂gaussianReal 0 1) ≤ ε) →
    (∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin n,
      (∫ z : ℝ, ((P n i).eval z -
        φ (((i.val : ℝ) + 1) / n) z) ^ 2
        ∂gaussianReal 0 1) ≤ ε) →
    0 < V →
    Tendsto (fun n : ℕ => Var[fun x => (Real.sqrt n)⁻¹ * ∑ i,
      (P n i).eval
        (standardizedFeatureObservation (v n)
          (EuclideanSpace.basisFun (Fin n) ℝ i) x);
      featureGaussian (v n)]) atTop (𝓝 V) →
    TendstoInDistribution (fun n : ℕ => fun x => (Real.sqrt n)⁻¹ * ∑ i,
      (P n i).eval
        (standardizedFeatureObservation (v n)
          (EuclideanSpace.basisFun (Fin n) ℝ i) x)) atTop
      (fun z : ℝ => Real.sqrt V * z) (fun n => featureGaussian (v n))
      (gaussianReal 0 1)

end Hurst
