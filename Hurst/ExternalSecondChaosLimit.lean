import Hurst.ActualFirstLongQuadraticReindex
import Hurst.FirstLongRieszEnergy
import Mathlib.Probability.Independence.CharacteristicFunction

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- The next point of a finite cyclic index set. -/
def finCyclicSucc {k : ℕ} (i : Fin k) : Fin k :=
  if h : i.val + 1 < k then ⟨i.val + 1, h⟩ else ⟨0, by omega⟩

/-- The cyclic integral which is the `k`th trace of the weighted Riesz
operator on `[-1,1]`.  Writing the support by an indicator also covers signed
equivalent kernels. -/
def weightedRieszCycleIntegral (k : ℕ) (psi c : ℝ)
    (omega : ℝ → ℝ) : ℝ :=
  ∫ z : Fin k → ℝ, ∏ i : Fin k,
    (Icc (-1 : ℝ) 1).indicator omega (z i) * c *
      |z i - z (finCyclicSucc i)| ^ (-psi)

/-- The eigenvalue characterization of the weighted Riesz operator.  It is
stated by its cyclic traces, so it does not require choosing eigenvectors in
Lean. -/
def IsWeightedRieszSpectrum (psi c : ℝ) (omega : ℝ → ℝ)
    (lambda : ℕ → ℝ) : Prop :=
  Summable (fun j => (lambda j) ^ 2) ∧
    ∀ k : ℕ, 2 ≤ k →
      HasSum (fun j => (lambda j) ^ k)
        (weightedRieszCycleIntegral k psi c omega)

/-- A random variable has the centered second-chaos law with coefficients
`lambda` when it is the Gaussian `L²` limit of
`sum lambda_j (Z_j² - 1)`. -/
def IsSecondChaosSeriesLaw
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (Q : Omega → ℝ) (lambda : ℕ → ℝ) : Prop :=
  AEMeasurable Q P ∧ Summable (fun j => (lambda j) ^ 2) ∧
    ∃ Z : ℕ → Omega → ℝ,
      (∀ j, AEMeasurable (Z j) P) ∧ iIndepFun Z P ∧
      (∀ j, P.map (Z j) = gaussianReal 0 1) ∧
      (∀ K : ℕ, MemLp (fun x => Q x - ∑ j ∈ Finset.range K,
        lambda j * ((Z j x) ^ 2 - 1)) 2 P) ∧
      Tendsto (fun K : ℕ =>
        ∫ x, (Q x - ∑ j ∈ Finset.range K,
          lambda j * ((Z j x) ^ 2 - 1)) ^ 2 ∂P) atTop (𝓝 0) ∧
      ∀ᵐ x ∂P, Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K,
        lambda j * ((Z j x) ^ 2 - 1)) atTop (𝓝 (Q x))

/-- The stated long-memory limit law: the coefficients are the spectrum of
the signed-weight Riesz operator and the random variable is the associated
centered second Gaussian chaos. -/
def IsWeightedRieszSecondChaosLaw
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (Q : Omega → ℝ) (psi c : ℝ) (omega : ℝ → ℝ) : Prop :=
  ∃ lambda : ℕ → ℝ,
    IsWeightedRieszSpectrum psi c omega lambda ∧
      IsSecondChaosSeriesLaw P Q lambda

/-- General weighted quadratic-form convergence target.

This proposition packages several model-independent steps: realization of a
finite Gaussian quadratic form as a double Wiener integral, convergence of
the corresponding weighted Hilbert--Schmidt operators, and continuity of the
second Wiener integral.  It is **not** the verbatim statement of Taqqu (1975),
Proposition 6.1, nor of any single proposition in Nourdin--Peccati (2012).
In particular, Nourdin--Peccati Proposition 2.7.13 supplies the spectral
series representation of one double Wiener integral, but it does not by
itself prove this triangular-array convergence statement.

Consequently this definition is an explicit remaining internal proof target,
not an accepted published-theorem boundary.  All its hypotheses are displayed
so that the missing generic operator/probability argument cannot conceal an
mBm-, grid-, local-polynomial-, or estimator-specific assumption. -/
def WeightedGaussianQuadraticSecondChaosConvergence : Prop :=
  ∀ (m : ℕ → ℕ)
    (v : ∀ n, Fin n → Lp ℂ 2 (volume : Measure ℝ))
    (a : ∀ n, Fin (m n) → EuclideanSpace ℝ (Fin n))
    (S : ℕ → ℝ) (psi c : ℝ)
    (w : ∀ n, Fin (m n) → ℝ) (omega : ℝ → ℝ)
    (P' : Measure ℝ) [IsProbabilityMeasure P'],
    0 < psi → psi < 1 / 2 →
    (∀ᶠ n in atTop, 0 < S n) → Tendsto S atTop atTop →
    Tendsto (fun n : ℕ => (m n : ℝ) / S n) atTop (𝓝 2) →
    (∀ᶠ n in atTop, ∀ i, ∑ j, a n i j • v n j ≠ 0) →
    Tendsto (fun n : ℕ =>
      realScaleMeshEnergy (S n) (fun i j =>
        S n ^ psi * featureCorrelation (v n) (a n i) (a n j) -
          rankRieszKernel (S n) psi c i j)) atTop (𝓝 0) →
    (∀ eps > 0, ∀ᶠ n : ℕ in atTop, ∀ i,
      |S n * w n i -
        omega (2 * (((i.val + 1 : ℕ) : ℝ) / (m n : ℝ)) - 1)| ≤ eps) →
    IsWeightedRieszSecondChaosLaw P' id psi c omega →
    TendstoInDistribution (fun n x => S n ^ psi * ∑ i,
      w n i * ((standardizedFeatureObservation (v n) (a n i) x) ^ 2 - 1))
      atTop id (fun n => featureGaussian (v n)) P'

end Hurst
