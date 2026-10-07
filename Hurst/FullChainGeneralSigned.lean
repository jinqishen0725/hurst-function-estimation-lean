import Hurst.ActualQ1SignedClosed
import Hurst.NormalizedActualRemainder
import Hurst.NormalizedLogProjection
import Hurst.P5SeamClosed
import Hurst.P5LogHLayers
import Hurst.P5TruthCenter
import Hurst.FirstStrideActualRows

/-!
# The full-chain endpoint on the repaired premises (blockers 2/3/4 closed)

This file rewires the `Hurst.FullChainEndpoint` composition onto the
blocker-2/3/4-repaired inputs.  It removes, from the endpoint signature:

* `hm : ∀ n, 0 < (localWeightActiveSet …).card` (blocker 2 — refutable at
  `n = 1`; the eventual form is derived inside the D3 `eventualCard` route,
  which this chain reaches through the general signed quadratic limit, whose
  row sizes tend to infinity by window geometry alone);
* `hE2 : ∃ C, ∑ i j ρ i j ^ 2 ≤ C` unnormalized (blocker 3 — divergent along
  the diagonal `ρ i i = 1` while the active card tends to infinity);
* `hNegMass`, the antitone/nonnegative package `hlam`, `hQ`, the even-only
  power sums `hPow`, and the weight-square-sum `hW0` (blocker 4 — the signed
  second-chaos limit is constructed from ALL power sums via the closed
  equivalent-kernel spectrum, with no vanishing-negative-mass input).

## How the new premises resolve in the actual model (contract table)

| premise | actual-model resolution | status |
|---|---|---|
| `hane` (active coefficient rows nonzero) | **RESOLVED IN LEAN** (`Hurst.FeatureRowNondegenerate`, takeover8): the harmonizable varying increment NEVER vanishes for all `h k ∈ Ioo 0 1`, `s`, `ℓ > 0` (`normalizedVaryingIncrement_ne_zero` — spectral route: a.e.-zero + continuity + integer-multiple + norm-balance argument), so `gridStrideFirstActual n d H i ≠ 0` for every parameter field and the positive scalar `(1/n)^{H_left}` factors out (`actualQ1_hane_discharged`/`actualQ1_hane_all`); discharged in the `FeasibleRates`/`CenterBandDischarge` endpoint variants | was data premise; RESOLVED (this endpoint keeps the general conditional form) |
| `hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b` | feasible window; nonempty for `γ` near `1` (with `2 - 2 * f t < 1/2`), it is the P1 feasible-bandwidth datum | data premise (window condition, satisfiable) |
| `hR` / `hcut` | **RESOLVED IN LEAN** (`Hurst.FeasibleRates`, takeover7): at `R n = ⌊n^β⌋₊` with `0 < β < (1-γ)(1-2ψ)`, `feasibleR_tendsto_atTop` / `feasibleR_cut_tendsto`. Math: `card ≤ 3 S` eventually (`S = n^{1-γ} ≥ 1`), `2⌊n^β⌋₊+1 ≤ 3n^β`, so the cut rate `≤ 9 n^{(1-γ)(2ψ-1)+β} → 0`, the exponent negative exactly by the β-window (deviation note: the single-squeeze bound `3n^β` needs `β > 0` — part of the window; the alternative `+1`-term split via `(1-γ)(2ψ-1) < 0` was not needed) | scalar rate, RESOLVED at the explicit `R n = ⌊n^β⌋₊` |
| `hEnv` (tail envelope → 0 for every fixed constants) | **RESOLVED IN LEAN** (`Hurst.FeasibleRates.feasibleR_env_tendsto`, takeover7): exact decomposition `q1ActualLongTailEnvelope_eq` = free part + `16/(R+1)`; five terms: `D → 0`, `D log n → 0` (`nat_log_power_div_rpow_tendsto`), `exp E → 1`, `16/(R+1) → 0` by `hR`, and `(2S)^ψ · gridCovarianceError` split into `(1+log 2n)·n^{(1-γ)ψ-1} → 0` (needs `ψ < 1/2`, i.e. the long-memory band) and `(1+log 2n)·n^{(1-γ)ψ+2b-2} → 0`, whose exponent is negative EXACTLY by `hgrid` | scalar rate, RESOLVED under `hgrid` + long-memory band (in fact for ALL fixed real constants — the envelope is linear in them, stronger than the `∀ ≥ 0` shape) |
| `cσ` / `d` / `hband` (projection-center band) | **RESOLVED IN LEAN** at the feasible bandwidth (`Hurst.CenterBandDischarge`, takeover8): the calibrated ratio `(cσ - E Ĝ_n)/(2 log n) → f t` for EVERY fixed `cσ` (`centerBand_ratio_tendsto` — exact expectation decomposition + weight stability + increment log bound), so the band holds with the explicit `d = (1 - f t)/2` (`centerBand_hband_discharged`); discharged in `…_feasible_centerBand` | was data premise; RESOLVED at γ = f t (this endpoint keeps the general conditional form) |
| `hE5` / `C` / `hBias` (E5 drift envelope) | E5 bias condition `(1 - γ) ψ < γ s`, `s = 1` | data premise (unchanged) |

Everything else (the quadratic limit, its limiting law, the fourth-order
Hermite remainder, the log-variance/clipping join) is discharged internally
from the closed theorems of `Hurst.ActualQ1SignedClosed`,
`Hurst.NormalizedActualRemainder` and `Hurst.NormalizedLogProjection`.
-/

set_option maxHeartbeats 2000000

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Real
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## Feasible-bandwidth window facts (replicated from FullChainEndpoint) -/

private theorem gs_bandwidth_pos (γ : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) ^ (-γ)) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

private theorem gs_bandwidth_tendsto (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ (-γ))) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop

private theorem gs_mesh_tendsto_atTop (γ : ℝ) (hγ : 0 < γ) (hγlt : γ < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) * ((n : ℝ) ^ (-γ)))) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 - γ))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  refine Tendsto.congr' ?_ h1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
    Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]

private theorem gs_mesh_pos (γ : ℝ) :
    ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * ((n : ℝ) ^ (-γ)) := by
  intro n hn
  have h0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact mul_pos h0 (Real.rpow_pos_of_pos h0 _)

/-! ## The weight/correlation identities behind the fourth energy -/

/-- The spectral weight is `S ^ ψ * w` with `ψ = 2 - 2 f t` and `w` the local
polynomial weight at the active index. -/
private theorem gs_spectralWeight_eq (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (hS : 0 < (n : ℝ) * δ) (i : Fin (localWeightActiveSet n 1 δ t).card) :
    actualQ1SpectralWeight f r n δ t i
      = ((n : ℝ) * δ) ^ (2 - 2 * f t) *
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) := by
  have h1 : ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * ((n : ℝ) * δ)
      = ((n : ℝ) * δ) ^ (2 - 2 * f t) := by
    have hrw : ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * ((n : ℝ) * δ)
        = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * ((n : ℝ) * δ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [hrw, ← Real.rpow_add hS,
      show (2 : ℝ) - 2 * f t - 1 + 1 = 2 - 2 * f t by ring]
  unfold actualQ1SpectralWeight actualQ1ChainWeight
  calc ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * (((n : ℝ) * δ) *
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i))
      = (((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * ((n : ℝ) * δ)) *
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) := by ring
    _ = _ := by rw [h1]

/-- The correlation of two active coefficient rows IS the vector correlation
of the corresponding first-stride actual increments (definitional on both
sides of `gridStrideFirst_correlation_identity`). -/
private theorem gs_correlation_eq (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    {n : ℕ} (hn : 0 < n) (δ t : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t j)
      = q1ActiveCorrelation f hf n δ t i j :=
  gridStrideFirst_correlation_identity n 1 hn (by norm_num)
    (midpointSampleHurst f hf.1 n) (localWeightActiveIndex n 1 δ t i)
    (localWeightActiveIndex n 1 δ t j)

/-- **The fourth-energy identity.**  The Layer-1' double-sum remainder at the
spectral weights equals the normalized actual fourth energy of
`Hurst.NormalizedActualRemainder` verbatim. -/
theorem gs_fourthEnergy_eq (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ)
    {n : ℕ} (hn : 0 < n) (δ t : ℝ) (hS : 0 < (n : ℝ) * δ) :
    (∑ i : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      |actualQ1SpectralWeight f r n δ t i * actualQ1SpectralWeight f r n δ t j| *
      |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t j)| ^ 4)
      = q1ActiveWeightedFourthEnergy f hf r n δ t := by
  have hpow : (((n : ℝ) * δ) ^ (2 - 2 * f t)) ^ (2 : ℕ)
      = ((n : ℝ) * δ) ^ (2 * (2 - 2 * f t)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS.le]
    congr 1
    ring
  have hscal : ∀ i : Fin (localWeightActiveSet n 1 δ t).card,
      actualQ1SpectralWeight f r n δ t i
      = ((n : ℝ) * δ) ^ (2 - 2 * f t) *
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) :=
    fun i => gs_spectralWeight_eq f r n δ t hS i
  have hnn : 0 ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t) := Real.rpow_nonneg hS.le _
  have hprod : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      actualQ1SpectralWeight f r n δ t i * actualQ1SpectralWeight f r n δ t j
      = (((n : ℝ) * δ) ^ (2 - 2 * f t)) ^ (2 : ℕ) *
        (localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) *
          localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)) := by
    intro i j
    rw [hscal i, hscal j]
    ring
  have habs : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      |actualQ1SpectralWeight f r n δ t i * actualQ1SpectralWeight f r n δ t j|
      = (((n : ℝ) * δ) ^ (2 - 2 * f t)) ^ (2 : ℕ) *
        |localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) *
          localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)| := by
    intro i j
    rw [hprod i j]
    simp only [abs_mul, abs_of_nonneg (pow_nonneg hnn _)]
  have hpt : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      (|actualQ1SpectralWeight f r n δ t i * actualQ1SpectralWeight f r n δ t j| *
      |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t j)| ^ 4)
      = (((n : ℝ) * δ) ^ (2 - 2 * f t)) ^ (2 : ℕ) *
        (|localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) *
          localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)| *
        |q1ActiveCorrelation f hf n δ t i j| ^ 4) := by
    intro i j
    rw [gs_correlation_eq f hf hn δ t i j, habs i j]
    ring
  calc (∑ i : Fin (localWeightActiveSet n 1 δ t).card,
        ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        |actualQ1SpectralWeight f r n δ t i * actualQ1SpectralWeight f r n δ t j| *
        |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t j)| ^ 4)
      = ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          (((n : ℝ) * δ) ^ (2 - 2 * f t)) ^ (2 : ℕ) *
          (|localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) *
            localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)| *
          |q1ActiveCorrelation f hf n δ t i j| ^ 4) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = (((n : ℝ) * δ) ^ (2 - 2 * f t)) ^ (2 : ℕ) *
        ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
          ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          |localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) *
            localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)| *
          |q1ActiveCorrelation f hf n δ t i j| ^ 4 := by
        simp only [← Finset.mul_sum]
    _ = _ := by rw [hpow]; rfl

/-- The Layer-1' fourth-energy premise, discharged at the actual model by the
normalized (W8-style) fourth-energy theorem under its scalar rate inputs. -/
theorem gs_fourthEnergy_tendsto_zero
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (R : ℕ → ℕ)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hR : Tendsto (fun n => (R n : ℝ)) atTop atTop)
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (hEnv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0,
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n) (R n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |actualQ1SpectralWeight f r n (δ n) t i *
          actualQ1SpectralWeight f r n (δ n) t j| *
        |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)| ^ 4)
      atTop (𝓝 0) := by
  have hcore := hurstHolder_q1_actual_weighted_fourth_tendsto_zero
    p a b M hp ha hb hab hM f hf hF r t ht hlong δ R hδpos hδ0 hN hR hcut hEnv
  have heq : ∀ᶠ n : ℕ in atTop,
      (∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |actualQ1SpectralWeight f r n (δ n) t i *
          actualQ1SpectralWeight f r n (δ n) t j| *
        |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)| ^ 4)
      = q1ActiveWeightedFourthEnergy f hf r n (δ n) t := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hδpos] with n hn hδ
    exact gs_fourthEnergy_eq f hf r hn (δ n) t (mul_pos (by exact_mod_cast hn) hδ)
  exact hcore.congr' (heq.mono fun n h => h.symm)

/-! ## The normalized L1 join at the actual chain objects -/

/-- The chain weights `u = S w` are eventually uniformly bounded (the scaled
local-polynomial weights are `O(1)` by full-row equivalent-kernel
approximation). -/
private theorem gs_chainWeight_bounded
    (f : ℝ → ℝ) (r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∃ U ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t i| ≤ U := by
  obtain ⟨U, hU, hUw⟩ := localPolynomialWeights_scaled_eventually_bounded
    r 1 t ht δ hδpos hδ0 hN
  refine ⟨U, hU, hUw.mono fun n hn i => ?_⟩
  exact hn (localWeightActiveIndex n 1 (δ n) t i)

/-- **The normalized L1 join (blocker-3 repair of the seam's `hJoin`).**
The projection-center band `hband` and the scaled-weight bound are the only
inputs beyond the NORMALIZED correlation energy; the old unnormalized `hE2`
route (`logProjection_L1_tendsto_instantiated`) is not used. -/
theorem gs_logProjection_L1_tendsto_instantiated
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hSpos : ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * δ n)
    (hlong : 3 / 4 < f t) (hfb : f t < 1)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (C₂ U : ℝ) (hU : 0 ≤ U)
    (hE : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        (∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t j) (actualQ1Coeff n (δ n) t k)) ^ 2) ≤ C₂)
    (hu : ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |actualQ1ChainWeight f r n (δ n) t j| ≤ U)
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n : ℕ in atTop,
      d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n (δ n) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n (δ n) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
        ≤ 1 - d) :
    Tendsto (fun n : ℕ => ∫ ω,
        |seamScaleC f t δ n *
            (p5KnownScaleEstimator f r n (δ n) t cσ ω -
              ∫ y, p5KnownScaleEstimator f r n (δ n) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) -
          -(gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) ω -
            ∫ y, gaussianLogStatistic (actualQ1SpectralWeight f r n (δ n) t)
              (actualQ1Coeff n (δ n) t) y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    atTop (𝓝 0) := by
  have hψ : 0 < 2 - 2 * f t := by linarith
  have hLtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hSmall := normalized_logProjection_L1_tendsto_zero
    (m := fun n => (localWeightActiveSet n 1 (δ n) t).card)
    (v := fun n => actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    (u := fun n i => actualQ1ChainWeight f r n (δ n) t i)
    (a := fun n => actualQ1Coeff n (δ n) t)
    (S := fun n => (n : ℝ) * δ n) (L := fun n => Real.log n)
    (ψ := 2 - 2 * f t) (U := U) (C := C₂) (d := d) (cσ := cσ)
    hψ hU hd hN hLtop
    (fun n j => hane n j) hu hE hband
  exact p5Seam_joinBridge f hf r t δ cσ hane hSpos hSmall

/-! ## Estimator regularity (replicated from FullChainEndpoint) -/

private theorem gs_estimator_aemeasurable (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ) (n : ℕ)
    (h : ∀ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0) :
    AEMeasurable (p5KnownScaleEstimator f r n (δ n) t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
  have hG : AEMeasurable (p5KnownScaleLogStatistic f r n (δ n) t)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
    (gaussianLogStatistic_memLp_two (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (fun i => ((n : ℝ) * δ n)⁻¹ * actualQ1ChainWeight f r n (δ n) t i)
      (actualQ1Coeff n (δ n) t) h).aemeasurable
  exact p5Trunc01_continuous.measurable.comp_aemeasurable
    ((aemeasurable_const.sub hG).div_const (2 * Real.log n))

private theorem gs_estimator_integrable (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ) (δ : ℕ → ℝ) (cσ : ℝ) (n : ℕ)
    (h : ∀ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0) :
    Integrable (p5KnownScaleEstimator f r n (δ n) t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
  refine Integrable.of_bound
    (gs_estimator_aemeasurable f hf r t δ cσ n h).aestronglyMeasurable (1 : ℝ)
    (Eventually.of_forall fun x => ?_)
  have hb : p5KnownScaleEstimator f r n (δ n) t cσ x ∈ Set.Icc 0 1 :=
    p5Trunc01_mem_Icc (p5KnownScaleHtilde f r n (δ n) t cσ x)
  obtain ⟨h1, h2⟩ := hb
  exact abs_le.mpr ⟨by linarith, h2⟩

/-! ## The full-chain endpoint on the repaired premises -/

/-- **The full-chain endpoint (truth-centered, general signed).**  At the
feasible bandwidth `δ n = n^{-γ}`, the clipped known-scale H estimator
satisfies

`2 n^{ψ (1 - γ)} log n * (Ĥ_n - f t) ⇒ -Q`,

where `Q` is CONSTRUCTED as the signed weighted-Riesz second-chaos law of the
closed equivalent-kernel spectrum (its existence and law are conclusions, not
hypotheses).  The premises are the model window, `hgrid`, `hane`, the scalar
rates (`hR`/`hcut`/`hEnv`, see the contract table), the center-band data, and
the E5 drift data — none of the refuted `hm`/`hE2`/`hNegMass`/
antitone-spectrum packages appears. -/
theorem actualQ1_knownScaleH_fullChain_generalSigned
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (R : ℕ → ℕ) (hR : Tendsto (fun n => (R n : ℝ)) atTop atTop)
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (hEnv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0,
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n ((n : ℝ) ^ (-γ))
          ((n : ℝ) * ((n : ℝ) ^ (-γ))) (R n)) atTop (𝓝 0))
    (cσ d : ℝ) (hd : 0 < d)
    (hband : ∀ᶠ n : ℕ in atTop,
      d ≤ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
      ∧ (cσ - ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) /
          (2 * Real.log n)
        ≤ 1 - d)
    (hE5 : (1 - γ) * (2 - 2 * f t) < γ * 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hBias : ∀ᶠ n : ℕ in atTop,
      |∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
        ≤ C * ((n : ℝ) ^ (-γ))) :
    ∃ Q : (ℕ → ℝ) → ℝ,
      IsWeightedRieszSecondChaosLaw gaussianSeqMeasure Q (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r) ∧
      TendstoInDistribution
        (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
          seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ x - f t))
        atTop (fun ω => -Q ω)
        (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
        gaussianSeqMeasure := by
  -- the window facts at the feasible bandwidth
  have hδpos := gs_bandwidth_pos γ
  have hδ0 := gs_bandwidth_tendsto γ hγ0
  have hN := gs_mesh_tendsto_atTop γ hγ0 hγ1
  have hSpos := gs_mesh_pos γ
  have hfb : f t < 1 := lt_of_le_of_lt (hF ht).2 hb
  -- 1. the quadratic side (blocker 4): the constructed signed law
  obtain ⟨Q, hLaw, hquad⟩ :=
    actualQ1LongStatistic_tendsto_secondChaos_generalSigned p a b M r hp ha hb hab hM
      f hf hF t ht hlong γ hγ0 hγ1 hgrid hane
  -- 2. the fourth-energy remainder (blocker 3) at the spectral weights
  have hFourth := gs_fourthEnergy_tendsto_zero p a b M hp ha hb hab hM f hf hF r t ht
    hlong (fun n => ((n : ℝ) ^ (-γ))) R hδpos hδ0 hN hR hcut hEnv
  -- 3. Layer 1' (double-sum form)
  have hL1 := actualQ1_logStatistic_tendsto_secondChaos_doubleSum f hf r t
    (fun n => ((n : ℝ) ^ (-γ))) ht gaussianSeqMeasure Q hane hquad hFourth
  -- 4. the normalized correlation energy (blocker 3, second half), in the
  --    featureCorrelation shape consumed by the join
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L₀, hL₀, C₂, hC₂, hEnergy⟩ :=
    hurstHolder_q1_actual_normalized_energy_eventually_bounded
      p a b M hp ha hb hab hM f hf hF t ht hlong
  have hRn : ∀ᶠ n : ℕ in atTop, 1 ≤ R n := by
    filter_upwards [hR.eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  have hEcore := hEnergy (fun n => ((n : ℝ) ^ (-γ))) R hδpos hδ0 hN hRn hcut
    (hEnv Ccov hCcov Ctail hCtail L₀ hL₀)
  have hE : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 * (2 - 2 * f t) - 2) *
        (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t j)
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k)) ^ 2) ≤ C₂ := by
    filter_upwards [hEcore, eventually_gt_atTop (0 : ℕ)] with n hEn hn
    have hsum : (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t j)
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k)) ^ 2)
        = ∑ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
            ∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
              (vectorCorrelation
                (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t i))
                (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j))) ^ 2 :=
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ =>
          congrArg (fun z => z ^ 2) (gs_correlation_eq f hf hn _ _ i j)
    rw [hsum]
    exact hEn
  -- 5. the scaled chain weights are eventually uniformly bounded
  obtain ⟨U, hU, huW⟩ := gs_chainWeight_bounded f r t ht
    (fun n => ((n : ℝ) ^ (-γ))) hδpos hδ0 hN
  -- 6. the normalized L1 join and the seam
  have hJoin := gs_logProjection_L1_tendsto_instantiated f hf r t
    (fun n => ((n : ℝ) ^ (-γ))) hN hSpos hlong hfb hane C₂ U hU hE huW cσ d hd hband
  have hSeam := logStatistic_knownScaleH_seam_of_logLimit f hf r t
    (fun n => ((n : ℝ) ^ (-γ))) gaussianSeqMeasure Q hane hL1 cσ hJoin
  -- 7. the E5 drift and the E4 center change
  have hDrift := p5_truthCenter_drift_s1 f hf r t cσ γ hγ0 hγ1 hlong hfb hE5 C hC hBias
  refine ⟨Q, hLaw, ?_⟩
  refine @p5_transport_truthCentered_of_drift
    (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    (fun n => featureGaussian_isProbability _) (ℕ → ℝ) _ gaussianSeqMeasure _ Q
    (fun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) =>
      p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ x)
    (fun n => seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n) (f t) hSeam ?_ ?_ ?_
  · intro n
    exact ((gs_estimator_aemeasurable f hf r t (fun n => ((n : ℝ) ^ (-γ))) cσ n
      (hane n)).sub aemeasurable_const).const_mul _
  · refine Eventually.of_forall fun n => ?_
    have hEstInt := gs_estimator_integrable f hf r t
      (fun n => ((n : ℝ) ^ (-γ))) cσ n (hane n)
    exact (((hEstInt.sub (integrable_const (f t))).const_mul _).sub
      ((hEstInt.sub (integrable_const _)).const_mul _))
  · have habscont : Continuous (fun z : ℝ => |z|) := by fun_prop
    have key : Tendsto (fun n : ℕ => |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
        ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
        atTop (𝓝 0) := by
      have h0 := (habscont.tendsto (0 : ℝ)).comp hDrift
      have h1 : Tendsto (fun n : ℕ => |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
          ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
              featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
          atTop (𝓝 (abs (0 : ℝ))) :=
        h0.congr (fun n => rfl)
      rwa [abs_zero] at h1
    have hint : ∀ n : ℕ, ∫ ω,
        |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
          - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
              - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
        ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        = |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
            ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|
        := by
      intro n
      have hpt : ∀ ω : EuclideanSpace ℝ (Fin n),
          |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
            - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
          = |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                - f t)|
          := fun ω => by
            rw [show seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
              - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              = seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                  ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                    - f t) by ring]
      calc ∫ ω,
            |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω - f t)
              - seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
                (p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ ω
                  - ∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          = ∫ ω, |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
                - f t)|
            ∂ featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) :=
            integral_congr_ae (Eventually.of_forall hpt)
        _ = |seamScaleC f t (fun m => ((m : ℝ) ^ (-γ))) n *
              ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-γ)) t cσ y ∂
                  featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)| := by
            rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    refine Tendsto.congr (fun n => ?_) key
    rw [hint n]

end Hurst
