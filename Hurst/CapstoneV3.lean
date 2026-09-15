import Hurst.CapstoneV2
import Hurst.P2SpectrumCloseout
import Hurst.SpectralWeightNonneg

/-!
# Capstone v3: the final composition under the honest spectral boundary

This file lands `actualQ1LongStatistic_tendsto_secondChaos_v3`: capstone v2
(`Hurst.CapstoneV2.actualQ1LongStatistic_tendsto_secondChaos_v2`) with the
spectrum NO LONGER a free hypothesized object but the CONSTRUCTED P2 enumeration
`HS.rieszSpectrumVal` of `Hurst.P2SpectrumCloseout`, instantiated at the matching
Riesz data `psi = 2 - 2 * f t`, `c = f t * (2 * f t - 1)`,
`omega = equivalentKernel r` (exactly the arguments of v2's `hRiesz` targets).

## What is DISCHARGED relative to v2 (all honest, all landed)

* **The spectrum object.**  v2's `lam` was a universally quantified variable
  ("the P2 construction obligation", DEFECT 4 of the audited capstone).  In v3
  `lam` IS the multiplicity-exact enumeration of the compact self-adjoint Riesz
  operator, built by `HS.rieszSpectrumVal` / `HS.rieszSpectrumVec` from
  `Hurst.FrozenSpectralCount.exists_multiplicity_enumeration`; the compactness
  input `isCompactOperator_TOp_riesz` is discharged INSIDE
  `exists_multiplicity_enumeration_summable_riesz` (no `hCompact` hypothesis
  appears here).
* **(ii) `Summable (fun j => val j ^ 2)`** — LANDED unconditionally (given only
  the Riesz-data hypotheses) by `HS.rieszSpectrum_sq_summable` (the
  spliced-family Bessel chain).  This is the FIRST conjunct of the v3
  conclusion: it holds with NO spectral-bridge hypothesis at all.  It is what
  constructs the law `Q` (`Hurst.P4GaussianSeriesLaw`), discharging v2's `hQ`
  from the P2 side rather than from `hRiesz` at `k = 2`.
* **(iii) the `k = 2` tsum bound** `∑' j, val j ^ 2 ≤ weightedRieszCycleIntegral
  2 …` — LANDED by `HS.rieszSpectrum_two_tsum_le_cycleIntegral` (tsum Bessel
  bound + the landed identification `weightedRieszCycleIntegral 2 … =
  hsNorm K_R²`).  Delivered as the SECOND conjunct of the v3 conclusion, again
  with no bridge hypothesis.
* **Nonnegativity `∀ j, 0 ≤ val j`** — discharged from the operator-positivity
  hypothesis `hPos` by the landed conditional clause (i)
  `HS.rieszSpectrum_nonneg_of_posTOp`.  (`hPos` is KEPT: the unconditional
  clause is FALSE in `omega` — the `omega ≡ -1` odd-cycle obstruction of
  `Hurst.P2SpectrumConstruction`; the PSD of the uniform-`ω` kernel is the
  documented Fourier-route deferral of `Hurst.HSOperatorLayer4`.)
* **`hcard`** — absent, as in v2 (derived eventual nonemptiness + padding).
* **`hQ`** — absent: `Q` is constructed by P4 from the landed (ii).
* **The feasible window** — v2's `δ n = n^{-γ}`, `0 < γ < 1`,
  `(1 - γ) * (2 - 2 * f t) < 2 - 2 * b` (nonempty for every `f t ≤ b < 1`).

## What is KEPT as explicit hypotheses (the honest boundary, documented)

* **`hAnti` : `Antitone val`.**  The decreasing order of the enumeration.  The
  peeling route consumes `cap2_paddedAbsRearranged_tendsto_of_eventualCard`,
  whose `hl` clause needs the limit spectrum antitone; for the
  `Classical.choose` enumeration the antitone re-sorting is NOT landed, so it is
  carried explicitly.  (v2 carried the identical clause inside `hlam`.)
* **`hTwo` : `HasSum (fun j => val j ^ 2) (weightedRieszCycleIntegral 2 …)`.**
  The `k = 2` EXACT spectral bridge.  The landed (iii) gives only the `≤` half;
  the `HasSum`-with-target clause additionally needs the reverse Parseval
  inequality `hsNorm K_R² ≤ ∑' val j²` — the kernel expansion
  `K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)` in `L²(vol2)`, documented as the isolated gap in
  `Hurst.HSNormIdentity` / `Hurst.CycleTraceIdentification` /
  `Hurst.RieszSpectralTrace`.  Kept as an explicit hypothesis (do not fake).
  It is genuinely consumed: the signed route's `hPow` at `k = 2` transports
  P1's limit `J_2` to `∑' val j²` through exactly this identification.
* **`hGen : ∀ k ≥ 3, HasSum (fun j => val j ^ k) (weightedRieszCycleIntegral
  k …)`.**  The general-`k` spectral bridge — DOCUMENTED-GRIDED on the
  composition peel induction `C_k(K) = C_{k-1}(compKernel K K)` architected in
  the gap report of `Hurst.HSCycleComposition` (analytic ingredients landed
  there: `hsNorm_comp_le`, `integral_compKernel_diag`, `cycleIntegral_two`,
  `cycle2_compKernel_eq_triple` modulo the `hA`/`hB` discharges).  Kept as an
  explicit hypothesis.  Together `hTwo` and `hGen` reassemble v2's `hRiesz`
  (`∀ k ≥ 2, HasSum …`) — the split is deliberate: the `k = 2` and the
  general-`k` clauses are gated on DIFFERENT missing identifications (reverse
  Parseval vs. peel induction), and the landed (ii)/(iii) close the
  square-summability and the `k = 2` mass bound AROUND them.
* **`hane`**, **`hwnn`** — v2's ordinary row nondegeneracy and eventual
  entrywise weight nonnegativity, unchanged.  In the `r = 1` degree-one
  variant `actualQ1LongStatistic_tendsto_secondChaos_v3_degreeOne` the `hwnn`
  clause is DISCHARGED by
  `Hurst.SpectralWeightNonneg.spectralWeight_nonneg_of_localLinearCriterion`
  from the balanced-window moment criterion `μ1 · x ≤ μ2` (hypothesis
  `hcrit`), exactly the pattern of
  `Hurst.SpectralWeightNonneg.actualQ1LongStatistic_tendsto_secondChaos_v2_degreeOne`.

## Conclusion

`(ii)` ∧ `(iii)` ∧ `∃ Q, IsSecondChaosSeriesLaw gaussianSeqMeasure Q val ∧
TendstoInDistribution (the actual q1 long-memory quadratic statistic at the
feasible window) atTop Q (featureGaussian …) gaussianSeqMeasure`.

The first two conjuncts are THEOREMS about the constructed spectrum (no bridge
hypothesis); the third is the v2 capstone conclusion with the spectrum object,
its square-summability, and its nonnegativity discharged, under the documented
`hAnti`/`hTwo`/`hGen` boundary.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter MeasureTheory Matrix ProbabilityTheory
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## THE CAPSTONE V3 (general `r`, `hwnn` kept) -/

set_option maxHeartbeats 10000000 in
/-- **THE CAPSTONE V3.**  Capstone v2 with the spectrum CONSTRUCTED: `lam` is
the P2 enumeration `HS.rieszSpectrumVal` at `psi = 2 - 2 * f t`,
`c = f t * (2 * f t - 1)`, `omega = equivalentKernel r` (v2's exact `hRiesz`
arguments).  Discharged: the spectrum object (with `isCompactOperator_TOp_riesz`
internal), the `Summable (λ²)` clause (landed (ii), first conclusion conjunct),
the `k = 2` tsum bound (landed (iii), second conclusion conjunct), and the
nonnegativity clause (conditional clause (i), from `hPos`).  Kept as the
documented honest boundary: `hAnti` (decreasing order of the enumeration),
`hTwo` (the `k = 2` exact `HasSum` — gated on the reverse Parseval inequality,
with the `≤` half landed), `hGen` (∀ `k ≥ 3` exact `HasSum` — gated on the
composition peel induction of `Hurst.HSCycleComposition`), plus v2's `hane`
and `hwnn`.  No `hcard`, no `hQ`, feasible window only. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v3
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    -- the Riesz-data hypotheses of the P2 enumeration (ordinary analysis data)
    (MR : ℝ)
    (hpow : AEStronglyMeasurable
      (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-(2 - 2 * f t))) HS.vol2)
    (homega : Measurable (equivalentKernel r))
    (hbdd : ∀ x : ℝ, |equivalentKernel r x| ≤ MR)
    (hg : Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-2 * (2 - 2 * f t))) HS.vol2)
    (hconst : ∀ x y : ℝ, (HS.I : Set ℝ).indicator (equivalentKernel r) x
      = (HS.I : Set ℝ).indicator (equivalentKernel r) y)
    -- operator positivity: the conditional clause (i) of P2
    -- (unconditional nonnegativity is FALSE in omega; PSD deferred, Fourier route)
    (hPos : ∀ g : HS.L2, 0 ≤ inner ℝ
      (HS.TOp (HS.rieszKernel (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel r))
        (HS.hsKernel_rieszKernel hpow homega hbdd hg) g) g)
    -- the honest boundary 1: decreasing order of the enumeration
    (hAnti : Antitone (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel r) MR hpow homega hbdd hg hconst))
    -- the honest boundary 2: the k = 2 EXACT bridge (reverse Parseval gap;
    -- the ≤ half is landed and delivered below as conclusion conjunct 2)
    (hTwo : HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ 2)
      (weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    -- the honest boundary 3: the general-k EXACT bridge (composition peel
    -- induction of Hurst.HSCycleComposition)
    (hGen : ∀ k : ℕ, 3 ≤ k → HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hwnn : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) :
    -- (ii), landed unconditionally in the Riesz data: the constructed spectrum
    -- is square-summable
    Summable (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ 2)
    -- (iii), landed: its k = 2 mass is bounded by the k = 2 cycle integral
      ∧ (∑' j : ℕ, HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ 2
        ≤ weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r))
    -- the capstone: the CONSTRUCTED second-chaos law is the distribution limit
      ∧ ∃ Q : (ℕ → ℝ) → ℝ,
          IsSecondChaosSeriesLaw gaussianSeqMeasure Q
            (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
              (equivalentKernel r) MR hpow homega hbdd hg hconst)
          ∧ TendstoInDistribution
              (fun (n : ℕ) x => gaussianLogQuadraticStatistic
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
                (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
                (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
              atTop Q
              (fun n => featureGaussian
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              gaussianSeqMeasure := by
  refine ⟨HS.rieszSpectrum_sq_summable (2 - 2 * f t) (f t * (2 * f t - 1))
    (equivalentKernel r) MR hpow homega hbdd hg hconst,
    HS.rieszSpectrum_two_tsum_le_cycleIntegral (2 - 2 * f t) (f t * (2 * f t - 1))
    (equivalentKernel r) MR hpow homega hbdd hg hconst, ?_⟩
  -- nonnegativity of the enumeration: conditional clause (i), from hPos
  have hnn : ∀ j : ℕ, 0 ≤ HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel r) MR hpow homega hbdd hg hconst j :=
    HS.rieszSpectrum_nonneg_of_posTOp (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel r) MR hpow homega hbdd hg hconst hPos
  -- the spectral bridge reassembled in the v2 shape (∀ k ≥ 2):
  -- k = 2 from hTwo, k ≥ 3 from hGen
  have hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)) := by
    intro k hk
    by_cases h2 : k = 2
    · subst h2
      exact hTwo
    · exact hGen k (by omega)
  -- the v2 capstone, instantiated at the CONSTRUCTED spectrum
  exact actualQ1LongStatistic_tendsto_secondChaos_v2 p a b M r hp ha hb hab hM f hf
    hF t ht hlong γ hγ0 hγ1 hgrid
    (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel r)
      MR hpow homega hbdd hg hconst)
    ⟨hAnti, hnn⟩ hRiesz hane hwnn

/-! ## The r = 1 degree-one variant (`hwnn` discharged) -/

set_option maxHeartbeats 10000000 in
/-- **THE CAPSTONE V3, degree-one (`r = 1`) variant with `hwnn` discharged.**
The balanced degree-one local-polynomial regime discharges the eventual
entrywise weight nonnegativity from the moment criterion `μ1 · x ≤ μ2` via
`Hurst.SpectralWeightNonneg.spectralWeight_nonneg_of_localLinearCriterion`
(the pattern of
`Hurst.SpectralWeightNonneg.actualQ1LongStatistic_tendsto_secondChaos_v2_degreeOne`).
All other hypotheses as in `actualQ1LongStatistic_tendsto_secondChaos_v3`
with `r := 1`. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v3_degreeOne
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (MR : ℝ)
    (hpow : AEStronglyMeasurable
      (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-(2 - 2 * f t))) HS.vol2)
    (homega : Measurable (equivalentKernel 1))
    (hbdd : ∀ x : ℝ, |equivalentKernel 1 x| ≤ MR)
    (hg : Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-2 * (2 - 2 * f t))) HS.vol2)
    (hconst : ∀ x y : ℝ, (HS.I : Set ℝ).indicator (equivalentKernel 1) x
      = (HS.I : Set ℝ).indicator (equivalentKernel 1) y)
    (hPos : ∀ g : HS.L2, 0 ≤ inner ℝ
      (HS.TOp (HS.rieszKernel (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel 1))
        (HS.hsKernel_rieszKernel hpow homega hbdd hg) g) g)
    (hAnti : Antitone (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel 1) MR hpow homega hbdd hg hconst))
    (hTwo : HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ 2)
      (weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1)))
    (hGen : ∀ k : ℕ, 3 ≤ k → HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    -- the balanced degree-one window criterion `μ1 · x ≤ μ2`
    (hcrit : ∀ n : ℕ, 1 ≤ n → ∀ j : Fin (n - 1),
      (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (0 : Fin 2) (1 : Fin 2)
          * ((grid n j.val - t) / ((n : ℝ) ^ (-γ)))
        ≤ (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (1 : Fin 2) (1 : Fin 2)) :
    Summable (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ 2)
      ∧ (∑' j : ℕ, HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ 2
        ≤ weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel 1))
      ∧ ∃ Q : (ℕ → ℝ) → ℝ,
          IsSecondChaosSeriesLaw gaussianSeqMeasure Q
            (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
              (equivalentKernel 1) MR hpow homega hbdd hg hconst)
          ∧ TendstoInDistribution
              (fun (n : ℕ) x => gaussianLogQuadraticStatistic
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
                (actualQ1SpectralWeight f 1 n ((n : ℝ) ^ (-γ)) t)
                (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
              atTop Q
              (fun n => featureGaussian
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              gaussianSeqMeasure :=
  actualQ1LongStatistic_tendsto_secondChaos_v3 p a b M 1 hp ha hb hab hM f hf hF
    t ht hlong γ hγ0 hγ1 hgrid MR hpow homega hbdd hg hconst hPos hAnti hTwo hGen
    hane (spectralWeight_nonneg_of_localLinearCriterion f t γ hcrit)

end Hurst
