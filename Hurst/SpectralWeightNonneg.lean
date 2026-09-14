import Hurst.LocalLinearWeightsNonneg
import Hurst.CapstoneV2

/-!
# Sign of the actual q1 spectral weight in the balanced degree-one regime

This file discharges the capstone-v2 hypothesis `hwnn` (DEFECT 5):

```
hwnn : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
  0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i
```

in the **balanced degree-one local-linear regime** (`r = 1`), under the
`μ1 · x ≤ μ2` moment criterion of `Hurst.LocalLinearWeightsNonneg`.

## The verified sign structure (exact, checked here)

Unfolding `Hurst.ActualQuadratureConfluence.actualQ1SpectralWeight` and
`actualQ1ChainWeight` gives, for `S n := (n : ℝ) * δ n` and
`ψ := 2 - 2 * f t`:

```
actualQ1SpectralWeight f r n δ t i
  = S n ^ (ψ - 1) * (S n * localPolynomialWeights r n 1 δ t
      (localWeightActiveIndex n 1 δ t i))
```

so the ONLY sign-bearing factor is the local polynomial weight itself:

* `S n ^ (ψ - 1)` is positive for every real exponent `ψ - 1 = 1 - 2 * f t`
  (a positive base raised to any real power is positive — no condition on
  `f t`);
* `S n` is positive for `1 ≤ n`, `0 < δ n`;
* `localWeightActiveIndex n 1 δ t : Fin (activeSet.card) → Fin (n - 1)` is the
  increasing enumeration of the support (a pure reindexing, sign-preserving);
* `localPolynomialWeights r n 1 δ t j` is the degree-`r` local weight.  For
  `r = 1` it is nonnegative under the sharp criterion of
  `localLinearWeight_nonneg`: `μ1 * x j ≤ μ2`, where
  `μ1 = (localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)` and
  `μ2 = (localDesignGram 1 n 1 b t) (1 : Fin 2) (1 : Fin 2)`.

(The unconditional statement "every degree-one weight is nonnegative" is FALSE
on one-sided windows — the module docstring of `Hurst.LocalLinearWeightsNonneg`
carries an explicit counterexample — so the balance `μ1 · x ≤ μ2` is carried as
an explicit ordinary hypothesis, exactly matching the T5e criterion.)

## Contents

* `actualQ1SpectralWeight_eq` : the exact sign-structure identity (`rfl`);
* `actualQ1SpectralWeight_scale_pos`, `actualQ1SpectralWeight_nonneg` :
  positivity of the scalar prefactors and the pointwise transfer;
* `localLinearWeights_nonneg_of_abs_moment_balance` : the symmetric-window
  form `|μ1| ≤ μ2` suffices (off-window weights vanish, on-window `|x| ≤ 1`);
* `localLinearWeights_nonneg_of_zero_first_moment` : the exactly-balanced
  window `μ1 = 0` special case;
* `spectralWeight_nonneg_of_localLinearCriterion` : the main bridge — the
  `μ1 · x ≤ μ2` criterion at `b = n ^ (-γ)` gives the exact `hwnn` of
  `actualQ1LongStatistic_tendsto_secondChaos_v2` for `r = 1`;
* `actualQ1LongStatistic_tendsto_secondChaos_v2_degreeOne` : capstone v2
  specialized to `r = 1` with `hwnn` DISCHARGED (only `hcrit` remains, plus
  the other ordinary hypotheses).
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace Hurst

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ## The exact sign structure of `actualQ1SpectralWeight` -/

/-- **The sign-structure identity.**  The spectral weight is a positive scalar
power of `S n = n * δ`, times `S n`, times the raw local polynomial weight at
the (reindexed) active grid point.  No sign-changing factor (kernel values,
`-1`-multipliers) appears. -/
theorem actualQ1SpectralWeight_eq (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (i : Fin (localWeightActiveSet n 1 δ t).card) :
    actualQ1SpectralWeight f r n δ t i
      = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
          * ((n : ℝ) * δ * localPolynomialWeights r n 1 δ t
              (localWeightActiveIndex n 1 δ t i)) :=
  rfl

/-- Both scalar prefactors `S ^ (ψ - 1)` and `S` are strictly positive: `S > 0`
raised to any real exponent is positive, with no condition on `f t`. -/
theorem actualQ1SpectralWeight_scale_pos {n : ℕ} (hn : 0 < (n : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (f : ℝ → ℝ) :
    0 < ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * ((n : ℝ) * δ) :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos hn hδ) _) (mul_pos hn hδ)

/-- **Pointwise transfer.**  Nonnegativity of the raw degree-`r` weight at the
active index forces nonnegativity of the spectral weight (positive scalar
multiplication preserves sign). -/
theorem actualQ1SpectralWeight_nonneg (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (i : Fin (localWeightActiveSet n 1 δ t).card) (hn : 0 < (n : ℝ)) (hδ : 0 < δ)
    (h : 0 ≤ localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i)) :
    0 ≤ actualQ1SpectralWeight f r n δ t i := by
  rw [actualQ1SpectralWeight_eq]
  exact mul_nonneg (Real.rpow_pos_of_pos (mul_pos hn hδ) _).le
    (mul_nonneg (mul_pos hn hδ).le h)

/-! ## The symmetric-window sufficient conditions (r = 1) -/

/-- **Balanced-window criterion.**  If the truncated degree-one window is
balanced in the sense `|μ1| ≤ μ2` (first-order symmetry), then every
degree-one local weight is nonnegative: off the window (`|x| ≥ 1`) the weight
vanishes with the kernel, and on the window `|x| ≤ 1` gives
`μ1 * x ≤ |μ1| * |x| ≤ μ2`. -/
theorem localLinearWeights_nonneg_of_abs_moment_balance (n : ℕ) (b t : ℝ)
    (hn : 1 ≤ n) (hb : 0 < b)
    (hbal : |(localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)|
        ≤ (localDesignGram 1 n 1 b t) (1 : Fin 2) (1 : Fin 2)) :
    ∀ j : Fin (n - 1), 0 ≤ localPolynomialWeights 1 n 1 b t j := by
  intro j
  by_cases h1 : 1 ≤ |(grid n j.val - t) / b|
  · rw [localPolynomialWeights_zero 1 n 1 b t j h1]
  · have hx : |(grid n j.val - t) / b| ≤ 1 := (lt_of_not_ge h1).le
    have hstep : |(localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)|
          * |(grid n j.val - t) / b|
        ≤ (localDesignGram 1 n 1 b t) (1 : Fin 2) (1 : Fin 2) := by
      have hmul := mul_le_mul_of_nonneg_left hx
        (abs_nonneg ((localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)))
      rw [mul_one] at hmul
      exact le_trans hmul hbal
    have hcrit : (localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)
          * ((grid n j.val - t) / b)
        ≤ (localDesignGram 1 n 1 b t) (1 : Fin 2) (1 : Fin 2) := by
      calc (localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)
            * ((grid n j.val - t) / b)
          ≤ |(localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)
              * ((grid n j.val - t) / b)| := le_abs_self _
        _ = |(localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2)|
              * |(grid n j.val - t) / b| := abs_mul _ _
        _ ≤ (localDesignGram 1 n 1 b t) (1 : Fin 2) (1 : Fin 2) := hstep
    refine localLinearWeight_nonneg n 1 b t (by exact_mod_cast hn) hb j ?_
    have h2 := localDesignGram_one_moment_two_nonneg n 1 b t (by exact_mod_cast hn) hb
    linarith

/-- **Exactly-balanced window.**  The perfectly symmetric first-order balance
`μ1 = 0` (e.g. a truncated window symmetric about `t`) satisfies the
`|μ1| ≤ μ2` criterion. -/
theorem localLinearWeights_nonneg_of_zero_first_moment (n : ℕ) (b t : ℝ)
    (hn : 1 ≤ n) (hb : 0 < b)
    (hzero : (localDesignGram 1 n 1 b t) (0 : Fin 2) (1 : Fin 2) = 0) :
    ∀ j : Fin (n - 1), 0 ≤ localPolynomialWeights 1 n 1 b t j := by
  refine localLinearWeights_nonneg_of_abs_moment_balance n b t hn hb ?_
  rw [hzero, abs_zero]
  exact localDesignGram_one_moment_two_nonneg n 1 b t (by exact_mod_cast hn) hb

/-! ## The hwnn bridge for the capstone v2 -/

/-- **The `hwnn` bridge (DEFECT 5, degree-one regime).**  If the
`μ1 · x ≤ μ2` criterion of `localLinearWeight_nonneg` holds at the feasible
bandwidth `b = n ^ (-γ)` for every grid point, then the capstone-v2 hypothesis

```
∀ᶠ n : ℕ in atTop, ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
  0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i
```

holds at `r = 1`: the spectral weight is `S ^ (ψ - 1) * S *` (degree-one
weight), and both scalar factors are positive. -/
theorem spectralWeight_nonneg_of_localLinearCriterion (f : ℝ → ℝ) (t : ℝ) (γ : ℝ)
    (hcrit : ∀ n : ℕ, 1 ≤ n → ∀ j : Fin (n - 1),
      (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (0 : Fin 2) (1 : Fin 2)
          * ((grid n j.val - t) / ((n : ℝ) ^ (-γ)))
        ≤ (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (1 : Fin 2) (1 : Fin 2)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        0 ≤ actualQ1SpectralWeight f 1 n ((n : ℝ) ^ (-γ)) t i := by
  refine Filter.eventually_atTop.mpr ?_
  refine ⟨1, fun n hn => ?_⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 < (n : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hnR _
  have hw := localLinearWeights_nonneg n 1 ((n : ℝ) ^ (-γ)) t
    (by exact_mod_cast hn) hδ (hcrit n hn)
  exact fun i => actualQ1SpectralWeight_nonneg f 1 n ((n : ℝ) ^ (-γ)) t i hnR hδ (hw _)

/-- **Balanced form of the bridge.**  Same conclusion from the symmetric-window
moment balance `|μ1| ≤ μ2` at the feasible bandwidth. -/
theorem spectralWeight_nonneg_of_absMomentBalance (f : ℝ → ℝ) (t : ℝ) (γ : ℝ)
    (hbal : ∀ n : ℕ, 1 ≤ n →
      |(localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (0 : Fin 2) (1 : Fin 2)|
        ≤ (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (1 : Fin 2) (1 : Fin 2)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        0 ≤ actualQ1SpectralWeight f 1 n ((n : ℝ) ^ (-γ)) t i := by
  refine Filter.eventually_atTop.mpr ?_
  refine ⟨1, fun n hn => ?_⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 < (n : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hnR _
  exact fun i => actualQ1SpectralWeight_nonneg f 1 n ((n : ℝ) ^ (-γ)) t i hnR hδ
    (localLinearWeights_nonneg_of_abs_moment_balance n ((n : ℝ) ^ (-γ)) t hn hδ
      (hbal n hn) (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t i))

/-- **Capstone v2, degree-one instance with `hwnn` discharged.**  The full
`actualQ1LongStatistic_tendsto_secondChaos_v2` at `r = 1` (the capstone keeps
`r` as a free variable; the balanced degree-one regime instantiates `r := 1`)
with `hwnn` supplied by `spectralWeight_nonneg_of_localLinearCriterion` —
the moment criterion `μ1 · x ≤ μ2` is the only new hypothesis beyond the
ordinary interface. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v2_degreeOne
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (lam : ℕ → ℝ)
    (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j)
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hcrit : ∀ n : ℕ, 1 ≤ n → ∀ j : Fin (n - 1),
      (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (0 : Fin 2) (1 : Fin 2)
          * ((grid n j.val - t) / ((n : ℝ) ^ (-γ)))
        ≤ (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (1 : Fin 2) (1 : Fin 2)) :
    ∃ Q : (ℕ → ℝ) → ℝ, IsSecondChaosSeriesLaw gaussianSeqMeasure Q lam ∧
      TendstoInDistribution
        (fun (n : ℕ) x => gaussianLogQuadraticStatistic
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1SpectralWeight f 1 n ((n : ℝ) ^ (-γ)) t)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
        atTop Q (fun n => featureGaussian
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) gaussianSeqMeasure :=
  actualQ1LongStatistic_tendsto_secondChaos_v2 p a b M 1 hp ha hb hab hM f hf hF
    t ht hlong γ hγ0 hγ1 hgrid lam hlam hRiesz hane
    (spectralWeight_nonneg_of_localLinearCriterion f t γ hcrit)

end Hurst

