import Hurst.P2SpectrumCloseout
import Hurst.GeneralKHasSum
import Hurst.GeneralKHasSumComplete
import Hurst.CapstoneV2

/-!
# P2 spectrum close-out v2: the capstone-v2-ready packaging and consumption

This file upgrades the Riesz-operator spectrum packaging from the
"Summable + `k = 2` tsum-bound" form of `Hurst.P2SpectrumCloseout` to the
"Summable + `k = 2` HasSum + general-`k` documented" form, and lands the exact
consumption interface of capstone v2's `hRiesz` hypothesis.

## What is landed here (all proofs complete, no placeholders)

* **The v2 bundle** (`HS.rieszSpectrumSequence_v2`): for the constructed
  multiplicity-exact spectrum `HS.rieszSpectrumVal` of the uniform-`ω` Riesz operator —
  1. the entry clause (`0` or an eigenvalue with unit eigenvector) and the
     multiplicity-exactness (landed, `Hurst.P2SpectrumCloseout`);
  2. **(ii)** `Summable (fun j => val j ^ 2)` (landed, re-exported through the bundle);
  3. **(iii, `k = 2`)** the honest HasSum pair: `HasSum (fun j => val j ^ 2) (∑' j, val j ^ 2)`
     (the enumerated spectrum's own tsum) together with the tsum-bound corollary
     `∑' j, val j ^ 2 ≤ weightedRieszCycleIntegral 2 psi c omega`;
  4. **general `k ≥ 2`**: `Summable (|val|^k)`, `HasSum (|val|^k → own tsum)`, and the two
     interpolation bounds `∑' |val|^k ≤ hsNorm K_R^(k-2) * J_2` and `∑' |val|^k ≤ hsNorm K_R^k`
     (the interpolation layer of `Hurst.GeneralKHasSum`, instantiated);
  5. **(i)** nonnegativity under the operator-positivity hypothesis (conditional;
     the unconditional clause is false in `omega`, `Hurst.P2SpectrumCloseout`).

* **The weaker pair, unconditional** (`HS.rieszSpectrum_weakerPair_v2`): the constructed
  spectrum satisfies `Summable (λ²) ∧ ∑' λ² ≤ J_2` with NO spectral hypothesis beyond the
  operator data.  This is the consumption-side usable form `Σ_j val_j² → (tsum) ≤ J_2`.

* **The documented boundary, as an iff** (`HS.hasSum_two_exact_iff_reverseParseval`):
  the exact-target `k = 2` HasSum `HasSum (val²) (J_2)` is EQUIVALENT to the reverse
  Parseval inequality `hsNorm K_R² ≤ ∑' val²` (given the landed forward direction).
  The reverse Parseval (the kernel expansion `K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)` in `L²(vol2)`)
  is the documented gap of `Hurst.HSNormIdentity` / `Hurst.CycleTraceIdentification` /
  `Hurst.RieszSpectralTrace` and is NOT forced here.

* **The consumption theorem** (`Hurst.actualQ1LongStatistic_tendsto_secondChaos_v2_of_pair`):
  the capstone v2 statement with `hRiesz` replaced by the pair
  `hlam2 : Summable (lam²)` (which the constructed spectrum supplies unconditionally)
  and the explicit documented clause `hHas : ∀ k ≥ 2, HasSum (lam^k) (J_k)`.

## Which pieces of `hRiesz` capstone v2 actually consumes (verified)

Reading the proof of `Hurst.CapstoneV2.actualQ1LongStatistic_tendsto_secondChaos_v2`,
`hRiesz` is consumed at EXACTLY two places, and nowhere else:

* **(α) the `k = 2` instance, `.summable` only**:
  `have hlam2 : Summable (fun j => lam j ^ 2) := (hRiesz 2 (by norm_num)).summable` —
  feeding the DEFECT-3 law construction `exists_isSecondChaosSeriesLaw_gaussSeq` and the
  `Summable` clause of the signed endpoint's `hlam`.  The `HasSum` CONTENT at `k = 2`
  (the target `J_2`) is NOT consumed here.
* **(β) every even `k ≥ 2`, `.tsum_eq`**: inside `hPow`,
  `rw [(hRiesz k hk).tsum_eq]` transports P1's power-sum limit `J_k` to `∑' lam ^ k`.
  This consumes the EQUALITY `∑' lam ^ k = J_k` at every even `k ≥ 2` — including
  `k = 2` and all `k ≥ 4` — i.e. the FULL general-`k` exact-target HasSum on even powers.

Consequences, stated honestly:

* the weaker pair (Summable + tsum-bound) closes (α) completely — and the constructed
  spectrum supplies (α) unconditionally (`HS.rieszSpectrum_weakerPair_v2`);
* the weaker pair does NOT close (β): the tsum-bound is only `≤`, while (β) consumes
  `=` at every even `k ≥ 2`.  Hence the general-k clause remains an EXPLICIT documented
  hypothesis of `actualQ1LongStatistic_tendsto_secondChaos_v2_of_pair`;
* at `k = 2` the missing equality is exactly the reverse Parseval
  (`HS.hasSum_two_exact_iff_reverseParseval`); at `k ≥ 3` the exact-target HasSum is
  gated on the composition peel induction (`Hurst.HSCycleComposition` residue: the
  `hA`/`hB` integrability discharges, the `chainCycleTriple` transport, the chain-level
  peel) plus the operator-side product-basis Parseval
  (`Hurst.CycleTraceIdentification` isolated gap).  The SUMMABILITY side for every
  `k ≥ 2` is fully landed (`HS.rieszSpectrum_hasSum_general_k`), so the exact statement
  closes the moment those two identifications land, via `HasSum` transport to the
  identified target.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter MeasureTheory Matrix ProbabilityTheory
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## The polynomial bandwidth data (public forms of capstone v2's private lemmas) -/

/-- `n^{-γ}` is eventually positive (the public form of capstone v2's
`cap2_powDelta_pos`, which is module-private there). -/
theorem v2powDelta_pos (γ : ℝ) (_hγ0 : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn1
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn1) _

/-- `n^{-γ} → 0` (the public form of capstone v2's `cap2_powDelta_tendsto_zero`). -/
theorem v2powDelta_tendsto_zero (γ : ℝ) (hγ0 : 0 < γ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop hγ0).comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) ^ γ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  rw [Real.rpow_neg hnR.le]

/-- `n · n^{-γ} → ∞` for `γ < 1` (the public form of capstone v2's
`cap2_mul_powDelta_tendsto_atTop`). -/
theorem v2mul_powDelta_tendsto_atTop (γ : ℝ) (hγ1 : γ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-γ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) - γ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 - γ by linarith)).comp
      tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
    Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]

/-! ## THE CONSUMPTION THEOREM: capstone v2 with `hRiesz` replaced by the pair -/

set_option maxHeartbeats 10000000 in
/-- **Capstone v2 with the `hRiesz` hypothesis REPLACED by its consumed content.**
This is `Hurst.CapstoneV2.actualQ1LongStatistic_tendsto_secondChaos_v2` verbatim except
that `hRiesz : ∀ k ≥ 2, HasSum (lam ^ k) (J_k)` is split into

* `hlam2 : Summable (fun j => lam j ^ 2)` — the consumption (α) (the `k = 2` `.summable`
  clause), which the CONSTRUCTED Riesz spectrum of `Hurst.P2SpectrumV2` supplies
  unconditionally (`HS.rieszSpectrum_weakerPair_v2`); and
* `hHas : ∀ k ≥ 2, HasSum (fun j => lam j ^ k) (J_k)` — the documented general-k clause
  (the consumption (β), the exact-target HasSum at every `k ≥ 2`).

The conclusion is IDENTICAL to capstone v2's.  The weaker pair (Summable + tsum-bound)
does not suffice: the `hPow` transport consumes the EQUALITY `∑' lam ^ k = J_k` via
`.tsum_eq` at every even `k ≥ 2`, which a `≤`-bound cannot supply. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v2_of_pair
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (lam : ℕ → ℝ)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j)
    (hlam2 : Summable (fun j : ℕ => lam j ^ 2))
    (hHas : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hwnn : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) :
    ∃ Q : (ℕ → ℝ) → ℝ, IsSecondChaosSeriesLaw gaussianSeqMeasure Q lam ∧
      TendstoInDistribution
        (fun (n : ℕ) x => gaussianLogQuadraticStatistic
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
        atTop Q (fun n => featureGaussian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) gaussianSeqMeasure := by
  -- (α): the law is CONSTRUCTED (P4) from the Summable clause — here a hypothesis,
  -- unconditionally supplied by the constructed Riesz spectrum
  obtain ⟨Q, hQ⟩ := exists_isSecondChaosSeriesLaw_gaussSeq lam hlam2
  refine ⟨Q, hQ, ?_⟩
  -- the feasible-window polynomial-bandwidth data (public re-derivations)
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ (-γ) := v2powDelta_pos γ hγ0
  have hδ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    v2powDelta_tendsto_zero γ hγ0
  have hN : Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ) ^ (-γ))) atTop atTop :=
    v2mul_powDelta_tendsto_atTop γ hγ1
  -- hPow: P1's power sums (ALL k ≥ 2, feasible window) + the documented clause (β)
  have hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)) := by
    intro k hk _
    have hP1 := actualQ1_eigenPowerSums_feasible p a b M r hp ha hb hab hM f hf hF
      t ht hlong γ hγ0 hγ1 hgrid k hk
    rw [(hHas k hk).tsum_eq]
    exact hP1
  -- hNegMass: discharged by hwnn via the PSD congruence (WeightedMatrixPSD)
  have hEv : ∀ n : ℕ, actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t
      = weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) := fun _ => rfl
  have hPt : ∀ (n : ℕ) (i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      (actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i
        = (weightedFeatureQuadraticMatrix_isHermitian
            (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
            (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).eigenvalues i :=
    fun n i => congrArg (fun H : (weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
        (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).IsHermitian =>
      H.eigenvalues i) (hEv n)
  have hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0) := by
    have hstep : ∀ᶠ n : ℕ in atTop,
        (∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (min ((actualQ1Hermitian f hf r n ((n : ℝ) ^ (-γ)) t).eigenvalues i) 0) ^ 2)
        = 0 := by
      filter_upwards [hwnn] with n hwn
      refine Finset.sum_eq_zero fun i _ => ?_
      have h0 : 0 ≤ (weightedFeatureQuadraticMatrix_isHermitian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)).eigenvalues i :=
        weightedFeatureQuadraticMatrix_eigenvalues_nonneg
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
          (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t) hwn i
      rw [← hPt n i, min_eq_right h0]
      ring
    exact tendsto_nhds_of_eventually_eq hstep
  -- the composition through the DEFECT-1-fixed signed endpoint
  exact actualQ1LongStatistic_tendsto_secondChaos_signed_eventualCard f hf r t
    (fun n : ℕ => (n : ℝ) ^ (-γ)) hδpos hδ0 hN ht gaussianSeqMeasure Q lam hQ
    ⟨hlam.1, fun j => ⟨hlam.2 j, hlam2⟩⟩ hPow hane hNegMass

end Hurst

namespace HS

open MeasureTheory Measure Real
open scoped Real

variable (psi c : ℝ) (omega : ℝ → ℝ) (M : ℝ)

/-! ### The k = 2 honest HasSum forms (standalone named versions of the bundle clauses) -/

/-- **(iii, `k = 2`) the HasSum to the own tsum**: the squared constructed Riesz spectrum
`HasSum`s to its own tsum — the enumerated-spectrum form of the degenerate/enumeration
HasSum patterns (`Hurst.GeneralKHasSum` anchor). -/
theorem rieszSpectrum_two_hasSum_ownTsum_v2
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
      (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2) :=
  (rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst).hasSum

/-- **(iii, `k = 2`) the tsum-bound corollary**:
`∑' j, val j² ≤ weightedRieszCycleIntegral 2 psi c omega` (landed in
`Hurst.P2SpectrumCloseout`, restated here as the v2 consumption-side usable form
`Σ_j val_j² → (tsum) ≤ J_2`). -/
theorem rieszSpectrum_two_tsum_le_cycleIntegral_v2
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
      ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega :=
  rieszSpectrum_two_tsum_le_cycleIntegral psi c omega M hpow homega hbdd hg hconst

/-- **The weaker pair, UNCONDITIONAL**: the constructed Riesz spectrum satisfies
`Summable (λ²) ∧ ∑' λ² ≤ J_2` with no hypothesis beyond the operator data.  This closes
capstone v2's consumption (α) (the `k = 2` `Summable` clause) outright; the exact
`k = 2` HasSum target additionally needs the reverse Parseval (see
`hasSum_two_exact_iff_reverseParseval`). -/
theorem rieszSpectrum_weakerPair_v2
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
      ∧ (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
        ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega) :=
  ⟨rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrum_two_tsum_le_cycleIntegral psi c omega M hpow homega hbdd hg hconst⟩

/-! ### The documented boundary, as an iff -/

/-- **The documented boundary, as a theorem**: the exact-target `k = 2` HasSum
`HasSum (fun j => val j ^ 2) (weightedRieszCycleIntegral 2 psi c omega)` is EQUIVALENT
to the reverse Parseval inequality `hsNorm K_R² ≤ ∑' j, val j²` (the forward `≤`
direction being landed).  The reverse Parseval — the kernel expansion
`K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)` in `L²(vol2)` — is the documented gap of
`Hurst.HSNormIdentity` / `Hurst.CycleTraceIdentification` / `Hurst.RieszSpectralTrace`;
it is NOT forced here. -/
theorem hasSum_two_exact_iff_reverseParseval
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
        (Hurst.weightedRieszCycleIntegral 2 psi c omega)
      ↔ hsNorm (rieszKernel psi c omega) ^ 2
        ≤ ∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2 := by
  constructor
  · intro h
    have h1 : (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
        = hsNorm (rieszKernel psi c omega) ^ 2 := by
      rw [h.tsum_eq, weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst]
    exact h1.symm.le
  · intro hrev
    have hle := rieszSpectrum_two_tsum_le_cycleIntegral psi c omega M hpow homega hbdd hg hconst
    rw [weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst] at hle
    have heq : (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
        = hsNorm (rieszKernel psi c omega) ^ 2 := le_antisymm hle hrev
    rw [weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst, ← heq]
    exact (rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst).hasSum

/-! ### The capstone-v2-ready packaging -/

/-- **P2 SPECTRUM CLOSE-OUT V2 — the capstone-v2-ready packaging** of the constructed
spectrum of the uniform-`ω` Riesz operator (`HS.rieszSpectrumVal`,
`Hurst.P2SpectrumCloseout`).  Clauses:

1. the entry clause: every entry is `0` or a nonzero eigenvalue with its unit
   eigenvector (the enumeration);
2. multiplicity-exactness: each nonzero eigenvalue occurs exactly
   `finrank (eigenspace μ)` times;
3. **(ii)** `Summable (fun j => val j ^ 2)` — the Bessel/spliced-family clause;
4. **(iii, `k = 2`)** `HasSum (fun j => val j ^ 2) (∑' j, val j ^ 2)` — the HasSum to
   the enumerated spectrum's own tsum;
5. **(iii, `k = 2`)** the tsum-bound `∑' val² ≤ weightedRieszCycleIntegral 2 psi c omega`;
6. **(i, conditional)** nonnegativity under the operator-positivity hypothesis
   (`hPos`); the unconditional clause is FALSE in `omega`
   (`Hurst.P2SpectrumCloseout`);
7. **general `k ≥ 2`** (the documented general-k layer): `Summable (|val|^k)`,
   `HasSum (|val|^k → own tsum)`, and the interpolation bounds
   `∑' |val|^k ≤ hsNorm K_R^(k-2) * J_2` and `∑' |val|^k ≤ hsNorm K_R^k`
   (`Hurst.GeneralKHasSum.rieszSpectrum_hasSum_general_k`).

The general-k EXACT-target clause
`∀ k ≥ 3, HasSum (fun j => val j ^ k) (weightedRieszCycleIntegral k psi c omega)` is the
documented boundary: at `k = 2` it is equivalent to the reverse Parseval
(`hasSum_two_exact_iff_reverseParseval`); at `k ≥ 3` it is gated on the composition peel
induction (`Hurst.HSCycleComposition` residue) plus the operator-side product-basis
Parseval (`Hurst.CycleTraceIdentification` gap).  The summability side for every `k ≥ 2`
IS landed (clause 7), so the exact clause closes the moment those identifications land,
via `HasSum` transport to the identified target. -/
theorem rieszSpectrumSequence_v2
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (∀ j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = 0 ∨
        Module.End.HasEigenvector
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
          (rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j)
          (rieszSpectrumVec psi c omega M hpow homega hbdd hg hconst j))
    ∧ (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ))
    ∧ Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
    ∧ HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
        (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
    ∧ (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
        ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega)
    ∧ ((∀ f : L2, 0 ≤ inner ℝ
          (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f) →
        ∀ j, 0 ≤ rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j)
    ∧ (∀ k : ℕ, 2 ≤ k →
        Summable (fun j => |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k)
        ∧ HasSum (fun j => |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k)
            (∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k)
        ∧ (∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k
            ≤ hsNorm (rieszKernel psi c omega) ^ (k - 2)
              * Hurst.weightedRieszCycleIntegral 2 psi c omega)
        ∧ (∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k
            ≤ hsNorm (rieszKernel psi c omega) ^ k)) := by
  refine ⟨rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst,
    fun μ hμ hμ0 =>
      rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0,
    rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrum_two_hasSum_ownTsum_v2 psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrum_two_tsum_le_cycleIntegral_v2 psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrum_nonneg_of_posTOp psi c omega M hpow homega hbdd hg hconst,
    fun k hk => ?_⟩
  have h := rieszSpectrum_hasSum_general_k psi c omega M hpow homega hbdd hg hconst k hk
  exact ⟨h.1.summable, h.1, h.2.1, h.2.2⟩

/-- **The consumption interface of capstone v2, from the constructed spectrum**: the
pieces that `Hurst.CapstoneV2.actualQ1LongStatistic_tendsto_secondChaos_v2_of_pair`
consumes from the spectral side are exactly
`Summable (fun j => val j ^ 2)` (clause (α), unconditional, `rieszSpectrum_weakerPair_v2`)
and the documented general-k clause
`∀ k ≥ 2, HasSum (fun j => val j ^ k) (weightedRieszCycleIntegral k psi c omega)`
(clause (β), the boundary — at `k = 2` equivalent to the reverse Parseval,
`hasSum_two_exact_iff_reverseParseval`; at `k ≥ 3` gated on the composition peel +
product-basis Parseval).  This theorem packages what the constructed spectrum DOES
supply: the Summable clause unconditionally, the HasSum-to-own-tsum for every `k ≥ 2`
(the summability side, `Hurst.GeneralKHasSumComplete.summable_pow_of_multEnum`), and the
closed tsum bound `∑' |val|^k ≤ hsNorm K_R ^ k`.  The exact-target identification of the
general-k HasSums remains the documented boundary. -/
theorem rieszSpectrum_consumptionPair_v2
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
      ∧ (∀ k : ℕ, 2 ≤ k → HasSum
          (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k)
          (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k))
      ∧ (∀ k : ℕ, 2 ≤ k →
          ∑' j, |rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j| ^ k
            ≤ hsNorm (rieszKernel psi c omega) ^ k) := by
  refine ⟨rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst,
    fun k hk => ?_, fun k hk => ?_⟩
  · exact (summable_pow_of_multEnum
      (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
      (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
      (rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst)
      (fun μ hμ hμ0 =>
        rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0)
      k hk).hasSum
  · exact tsum_abs_pow_le_multEnum
      (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
      (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
      (rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst)
      (fun μ hμ hμ0 =>
        rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0)
      k hk

end HS

end
