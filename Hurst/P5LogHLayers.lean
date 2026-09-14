import Hurst.ActualQuadratureFinal
import Hurst.FeatureQuadraticLimit
import Hurst.TriangularL1Transfer

/-!
# P5 conditional layers: quadratic limit → log statistic → known-scale H estimator

This file builds the two DOWNSTREAM conditional layers of the q1 long-memory
chain, starting from the quadratic second-chaos limit of
`Hurst.ActualQuadratureFinal.actualQ1LongStatistic_tendsto_secondChaos_signed`,
whose hypotheses (`hPow`, `hane`, `hNegMass`, `hQ`, `hlam`, `hm`) are taken
VERBATIM as explicit inputs of every layer below (discharging them is the
upstream chain's job; see the file 22 / file 24 handoff notes).

## Layer 1 (file 22 W8, log statistic)

`actualQ1_logStatistic_tendsto_secondChaos_of_quadratic`: the quadratic limit
composed with the Hermite-truncation second-order layer
`featureGaussian_log_limit_of_quadratic_limit`.  The fourth-order remainder
inputs of that layer (file 24, E2–E3) are discharged internally from the
unweighted correlation-energy bound `hE2`, the uniform chain-weight bound
`hU` and the long-memory band `hlong : 3 / 4 < f t` (so `ψ = 2 - 2 f t < 1/2`).

## Layer 2 (file 22 W9 / file 24 E1–E4, known-scale H estimator)

`actualQ1_knownScaleH_tendsto_neg_secondChaos_expectationCentered`: the log
limit transported through the truncated inverse `p5Trunc01` (Lipschitz,
continuous) to the EXPECTATION-centered limit
`2 S^ψ log n (Ĥ - E Ĥ) ⇒ -Q`, with `Q` kept signed.  Inputs beyond layer 1:
the projection-center band `hd` (file 22 W9) and `hfb : f t < 1` (so `ψ > 0`).
The variance-scale input of file 22 (26) is reduced to `hE2` + `hU` via
`gaussianLogStatistic_variance_correlation_bound`.

`actualQ1_knownScaleH_tendsto_neg_secondChaos_truthCentered_of_drift`: the
file 24 E4 center-change rule: given the deterministic drift
`2 S^ψ log n (E Ĥ - h) → 0` (E5's bias condition with the conservative `s = 1`
is such a drift hypothesis, kept explicit upstream), the truth-centered limit
holds.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## The truncated inverse -/

/-- Truncation to `[0, 1]`: the truncated q1 calibration inverse. -/
def p5Trunc01 (x : ℝ) : ℝ := min 1 (max 0 x)

theorem p5Trunc01_mem_Icc (x : ℝ) : p5Trunc01 x ∈ Set.Icc 0 1 := by
  constructor
  · rcases min_cases 1 (max 0 x) with h | h
    · rw [p5Trunc01, h.1]; exact zero_le_one
    · rw [p5Trunc01, h.1]; exact le_max_left 0 x
  · rw [p5Trunc01]; exact min_le_left 1 _

theorem p5Trunc01_eq_self {x : ℝ} (hx : x ∈ Set.Icc 0 1) : p5Trunc01 x = x := by
  rw [p5Trunc01, max_eq_right hx.1, min_eq_right hx.2]

theorem p5Trunc01_mono : Monotone p5Trunc01 := by
  intro x y h
  unfold p5Trunc01
  exact min_le_min (le_refl 1) (max_le_max (le_refl 0) h)

/-! ## The actual known-scale log statistic and H estimator -/

/-- The actual weighted log-square increment statistic with the unit-sum
local weights `w_{n,i} = S⁻¹ u_{n,i}` (file 22 §1). -/
def p5KnownScaleLogStatistic (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  gaussianLogStatistic
    (fun i => ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t i)
    (actualQ1Coeff n δ t) x

/-- The untruncated known-scale H transform `(cσ - Ĝ) / (2 log n)`. -/
def p5KnownScaleHtilde (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ) (cσ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (cσ - p5KnownScaleLogStatistic f r n δ t x) / (2 * Real.log n)

/-- The known-scale H estimator: the truncated inverse of the actual weighted
log-square increment statistic (file 22 W9). -/
def p5KnownScaleEstimator (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ) (cσ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  p5Trunc01 (p5KnownScaleHtilde f r n δ t cσ x)

/-! ## A pointwise centering identity -/

/-- The pointwise identity behind the expectation-centered transfer: the
negated centered spectral log statistic equals the scaled centered
untruncated-H statistic. -/
private theorem p5_YX_identity (S ψ L est EI sx ES gx EL cσ : ℝ)
    (hS : 0 < S) (hL : 0 < L) (hgx : gx = S ^ (-ψ) * sx) (hEL : EL = S ^ (-ψ) * ES) :
    2 * S ^ ψ * L * (est - EI) + (sx - ES)
      = 2 * S ^ ψ * L *
        ((est - (cσ - gx) / (2 * L)) - (EI - (cσ - EL) / (2 * L))) := by
  rw [hgx, hEL]
  have hcancel : S ^ ψ * S ^ (-ψ) = 1 := by
    rw [← Real.rpow_add hS ψ (-ψ), show ψ + -ψ = (0 : ℝ) by ring, Real.rpow_zero]
  have hB : (cσ - S ^ (-ψ) * ES) / (2 * L) - (cσ - S ^ (-ψ) * sx) / (2 * L)
      = (S ^ (-ψ) * (sx - ES)) / (2 * L) := by ring
  have hprod : 2 * S ^ ψ * L * ((S ^ (-ψ) * (sx - ES)) / (2 * L)) = sx - ES := by
    calc 2 * S ^ ψ * L * ((S ^ (-ψ) * (sx - ES)) / (2 * L))
        = S ^ ψ * (S ^ (-ψ) * (sx - ES)) := by field_simp [hL.ne']
      _ = sx - ES := by rw [← mul_assoc, hcancel, one_mul]
  rw [show (2 : ℝ) * S ^ ψ * L *
      (est - (cσ - S ^ (-ψ) * sx) / (2 * L) - (EI - (cσ - S ^ (-ψ) * ES) / (2 * L)))
      = 2 * S ^ ψ * L * (est - EI) + 2 * S ^ ψ * L *
        ((cσ - S ^ (-ψ) * ES) / (2 * L) - (cσ - S ^ (-ψ) * sx) / (2 * L)) by ring]
  rw [hB, hprod]

/-! ## Layer 1 (W8): the log-statistic limit -/

/-- **Layer 1 (file 22 W8).**  From the quadratic second-chaos limit (the D3
hypotheses verbatim) to the EXPECTATION-centered log-statistic limit
`Ĝ_spec - E Ĝ_spec ⇒ Q`, where `Ĝ_spec` carries the `S^{ψ-1}`-normalized
spectral weights.  The fourth-order remainder inputs of
`featureGaussian_log_limit_of_quadratic_limit` (file 24, E2–E3) are
discharged internally from `hE2` (unweighted correlation energy), `hU`
(bounded chain weights) and `hlong` (`ψ < 1/2`). -/
theorem actualQ1_logStatistic_tendsto_secondChaos_of_quadratic
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lam : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lam)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (hPow : ∀ k : ℕ, 2 ≤ k → Even k → Tendsto
      (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hNegMass : Tendsto (fun n : ℕ =>
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (min ((actualQ1Hermitian f hf r n (δ n) t).eigenvalues i) 0) ^ 2)
      atTop (𝓝 0))
    (hlong : 3 / 4 < f t)
    (hW0 : Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) atTop (𝓝 0))
    (hE2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 ≤ C) :
    TendstoInDistribution
      (fun (n : ℕ) x => gaussianLogStatistic
          (actualQ1SpectralWeight f r n (δ n) t) (actualQ1Coeff n (δ n) t) x -
        (∫ y, gaussianLogStatistic
          (actualQ1SpectralWeight f r n (δ n) t) (actualQ1Coeff n (δ n) t) y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))))
      atTop Q (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
  obtain ⟨C₂, hC₂0, hC₂ev⟩ := hE2
  -- basic eventual facts (file 24, E2: merge finitely many eventual events)
  have hSpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * δ n := by
    filter_upwards [hδpos, hN.eventually_ge_atTop (1 : ℝ)] with n hδ hS
    have hn1 : 1 ≤ n := by
      rcases Nat.lt_or_ge n 1 with h0 | h0
      · exfalso
        rw [show n = 0 by omega] at hS
        exact absurd hS (by norm_num)
      · exact h0
    exact mul_pos (by exact_mod_cast hn1) hδ
  have hexpzero : 0 < 4 * f t - 3 := by linarith
  -- active-card upper bound from the ratio limit
  obtain ⟨_, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos hδ0 hN
  have hcardle : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * ((n : ℝ) * δ n) := by
    filter_upwards [hratio.eventually_lt_const (by norm_num : (2 : ℝ) < 3), hSpos] with n hlt hS
    exact le_of_lt ((div_lt_iff₀ hS).mp hlt)
  -- per-row fourth-power correlation bound from hE2 (file 24, E3)
  have hRow4 : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
          |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)| ^ 4 ≤ C₂ := by
    filter_upwards [hC₂ev] with n htot i
    have hrow : ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)) ^ 2 ≤ C₂ := by
      have hsingle := Finset.single_le_sum
        (f := fun k : Fin (localWeightActiveSet n 1 (δ n) t).card =>
          ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
              (actualQ1Coeff n (δ n) t k) (actualQ1Coeff n (δ n) t j)) ^ 2)
        (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
      linarith
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) hrow
    have h1 := featureCorrelation_abs_le_one
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j) (hane n i) (hane n j)
    obtain ⟨hc1, hc2⟩ := abs_le.mp h1
    have hx1 : |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)| ^ 2 = featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j) ^ 2 := sq_abs _
    have hx2 : featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j) ^ 2 ≤ 1 := by nlinarith [hc1, hc2]
    have hsplit : |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)| ^ 4 = |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)| ^ 2 * |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j)| ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
    rw [hsplit, hx1]
    nlinarith [hx2, sq_nonneg (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t j))]
  have hRem : Tendsto (fun n : ℕ => (1 : ℝ) ^ 2 * C₂ *
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2) atTop (𝓝 0) := by
    have h := hW0.const_mul ((1 : ℝ) ^ 2 * C₂)
    rwa [mul_zero] at h
  -- the quadratic-limit hypothesis of the log layer, at unit scale
  -- the quadratic-limit hypothesis of the log layer, at unit scale
  have hquad : TendstoInDistribution
      (fun (n : ℕ) x => (1 : ℝ) * gaussianLogQuadraticStatistic
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1SpectralWeight f r n (δ n) t)
        (actualQ1Coeff n (δ n) t) x) atTop Q
      (fun n => featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) P' := by
    refine TendstoInDistribution.congr
      (fun n => Eventually.of_forall fun x => by simp)
      (Eventually.of_forall fun _ => rfl)
      (actualQ1LongStatistic_tendsto_secondChaos_signed f hf r t δ hδpos hδ0 hN ht
        P' Q lam hQ hlam hm hPow hane hNegMass)
  -- assemble the log layer
  have hres := featureGaussian_log_limit_of_quadratic_limit P'
    (m := fun n => (localWeightActiveSet n 1 (δ n) t).card)
    (v := fun n => actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    (w := fun n => actualQ1SpectralWeight f r n (δ n) t)
    (a := fun n => actualQ1Coeff n (δ n) t)
    (c := fun _ => (1 : ℝ)) (R := fun _ => C₂) (Z := Q)
    (Eventually.of_forall fun n k => hane n k)
    hRow4 hRem hquad
  refine TendstoInDistribution.congr ?_ (Eventually.of_forall fun _ => rfl) hres
  intro n
  filter_upwards with x
  simp


/-! ## Layer 2 (W9 / E1–E4): transport contracts for the known-scale H estimator

The statistical input of file 22 W9 reduces to two L1 contracts; here they are
packaged as explicit-hypothesis transport theorems (file 24, E1–E2: the L1
transfer needs only eventual measurability and integrability; E4: center
change by a vanishing deterministic drift).  The L1 smallness itself is
file 22 (27): `2 S^ψ log n E|Π((cσ - Ĝ)/(2 log n)) - (cσ - Ĝ)/(2 log n)| ≤
S^ψ Var(Ĝ) / (2 d log n) → 0` given the `hE2`-reduced variance bound of
file 22 (26); its reduction is upstream work, so it is kept explicit here. -/

/-- **Layer 2 transport core (file 22 W9 / file 24 E1–E2).**  If the negated
centered log statistic tends to `-Q` and the scaled truncated estimator is
within `o(1)` in L1 of it, then the EXPECTATION-centered known-scale H limit
holds.  The `c n`-scaling is `c n = 2 S_n^ψ log n` in the actual chain. -/
theorem p5_transport_expectationCentered
    {Pn : ∀ n : ℕ, Measure (EuclideanSpace ℝ (Fin n))}
    [∀ n : ℕ, IsProbabilityMeasure (Pn n)]
    {Theta : Type*} [MeasurableSpace Theta]
    {P' : Measure Theta} [IsProbabilityMeasure P']
    {Q : Theta → ℝ}
    (specL : (n : ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (est : (n : ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : ℕ → ℝ)
    (hX : TendstoInDistribution
      (fun n x => -(specL n x - (∫ y, specL n y ∂Pn n))) atTop (fun ω => -Q ω) Pn P')
    (hYmeas : ∀ n : ℕ, AEMeasurable
      (fun x => c n * (est n x - (∫ y, est n y ∂Pn n))) (Pn n))
    (hDint : ∀ᶠ n : ℕ in atTop, Integrable
      (fun ω => c n * (est n ω - (∫ y, est n y ∂Pn n))
        - -(specL n ω - (∫ y, specL n y ∂Pn n))) (Pn n))
    (hL1 : Tendsto (fun n => ∫ ω, |c n * (est n ω - (∫ y, est n y ∂Pn n))
        - -(specL n ω - (∫ y, specL n y ∂Pn n))| ∂Pn n) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n x => c n * (est n x - (∫ y, est n y ∂Pn n))) atTop (fun ω => -Q ω) Pn P' :=
  triangular_L1_distribution_transfer Pn P' _ _ _ hX hYmeas hDint hL1

/-- **File 24 E4 (center change by a vanishing deterministic drift).**  If the
EXPECTATION-centered limit holds and the deterministic drift
`c n (E Ĥ_n - h)` tends to `0` (E5's bias condition `(1 - γ)ψ < γ s` with the
conservative `s = 1` is exactly what makes this drift vanish, upstream), then
the TRUTH-centered limit holds with the same reflection `-Q`. -/
theorem p5_transport_truthCentered_of_drift
    {Pn : ∀ n : ℕ, Measure (EuclideanSpace ℝ (Fin n))}
    [∀ n : ℕ, IsProbabilityMeasure (Pn n)]
    {Theta : Type*} [MeasurableSpace Theta]
    {P' : Measure Theta} [IsProbabilityMeasure P']
    {Q : Theta → ℝ}
    (est : (n : ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : ℕ → ℝ)
    (h : ℝ)
    (hE : TendstoInDistribution
      (fun n x => c n * (est n x - (∫ y, est n y ∂Pn n))) atTop (fun ω => -Q ω) Pn P')
    (hYmeas : ∀ n : ℕ, AEMeasurable (fun x => c n * (est n x - h)) (Pn n))
    (hDint : ∀ᶠ n : ℕ in atTop, Integrable
      (fun ω => c n * (est n ω - h) - c n * (est n ω - (∫ y, est n y ∂Pn n))) (Pn n))
    (hL1 : Tendsto (fun n => ∫ ω,
      |c n * (est n ω - h) - c n * (est n ω - (∫ y, est n y ∂Pn n))| ∂Pn n) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n x => c n * (est n x - h)) atTop (fun ω => -Q ω) Pn P' :=
  triangular_L1_distribution_transfer Pn P' _ _ _ hE hYmeas hDint hL1

end Hurst
