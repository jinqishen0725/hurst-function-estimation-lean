import Hurst.E5ChainInstantiation

/-!
# E5 rate link: the polynomial rate of the spectral correlation energy

This module closes the ENERGY-RATE gap documented in `Hurst.E5ChainInstantiation`
(its docstring, gap 1): the E5 fluctuation discharge
`e5_fluctuation_at_chain` consumes the spectral correlation energy in the RATE
form `∑∑ |w_j||w_k| corr_{jk}² ≤ E · n^{-2γ} (log n)²`, but only the
constant-form energy bounds were landed.  Here the rate is derived.

## What is provable honestly (and what is proved here)

The landed row-bound machinery (`firstStrideLongRowBound`,
`Hurst.P7RowBound`) bounds the correlation ROWS of the whole-grid
first-stride chain (`commonFirstStrideCoefficients`); the P5 chain of
`e5_fluctuation_at_chain` is the LOCAL active-window chain
(`actualQ1Coeff` at the active set of `localWeightActiveSet n 1 (δ n) t`),
whose per-row energies are NOT linked to `firstStrideLongRowBound` anywhere in
the repo (the spectral-energy-to-row-bound link is not landed).  What IS
landed, unconditionally, is the pointwise bound `|corr| ≤ 1` (the
inner-product form of `featureCorrelation`), which yields the ROW-ENERGY form

  `∑∑ |w_j||w_k| corr_{jk}² ≤ (∑ |w|)² ≤ card · ∑ w²`
  (`e5rl_energy_card`, Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq`),

and the weight-energy rate

  `∑ w² = S^{2(ψ-1)} ∑ u²` (spectral normalization `w = S^{ψ-1} u`),
  `card ≤ 3 S` (the landed active-set cardinality ratio limit),

so the energy is `≤ 3 U · S^{2ψ-1}` with `ψ = 2 - 2 f t` and `U` the
eventual bound on the chain-weight energy `∑ u²` (the `hU` shape of
`Hurst.P5LogHLayers`).

## The feasible bandwidth window (exponent bookkeeping)

Target: `3 U · S^{2ψ-1} ≤ E · n^{-2γ} (log n)²`.  In the long-memory band
`3/4 < f t` one has `ψ = 2 - 2 f t < 1/2`, i.e. `2ψ - 1 = -(4 f t - 3) < 0`,
so `S^{2ψ-1}` DECREASES in the mesh `S = (n:ℝ) * δ n`.  If the mesh grows at
least polynomially, `S ≥ n^c` (mesh exponent `c > 0`), then

  `S^{2ψ-1} ≤ n^{c(2ψ-1)} = n^{-c(4ft-3)} ≤ n^{-2γ} ≤ n^{-2γ} (log n)²`,

the middle inequality being exactly the WINDOW `2γ ≤ c (4 f t - 3)` and the
last one trivial (`(log n)² ≥ 0`).  So `E = 3 U` works.  The window is
feasible whenever `2γ < (mesh exponent) · (4 f t - 3)`, which is non-vacuous
exactly in the long-memory band.

## Main statements

* `correlationEnergy_rate` — the spectral correlation energy is eventually
  `≤ 3 U · n^{-2γ} (log n)²` under the ordinary bandwidth data, the
  long-memory band, the bounded chain-weight energy and the polynomial-mesh
  window; stated in EXACTLY the `hEnergy` shape of `e5_fluctuation_at_chain`.
* `e5_fluctuation_rate_of_window` — the composition: plugging
  `correlationEnergy_rate` into `e5_fluctuation_at_chain` yields the E5
  fluctuation at the polynomial rate `F · n^{-γ}`.

## Gaps (documented deviations)

The per-row refinement (each row `∑_k corr_{ik}²` bounded by
`firstStrideLongRowBound`, which would replace `corr² ≤ 1` by a genuinely
decaying row energy) remains the open spectral-energy-to-row-bound link: the
P7 row-bound machinery is proved for the whole-grid stride chain, not for the
local active-window chain of P5.  The rate landed here comes from the
row-energy bound alone (`corr² ≤ 1` + Cauchy–Schwarz) composed with the
weight-energy rate and the polynomial-mesh window.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Hurst

/-! ### Elementary helpers (clones of the E5ChainInstantiation privates) -/

/-- `(x ^ e) ^ 2 = x ^ (2 * e)` for `0 ≤ x`. -/
private theorem e5rl_rpow_sq (x : ℝ) (hx : 0 ≤ x) (e : ℝ) :
    (x ^ e) ^ 2 = x ^ (2 * e) := by
  rw [← Real.rpow_natCast (x := x ^ e) (n := 2), ← Real.rpow_mul hx]
  congr 1
  ring

/-- `x * x ^ e = x ^ (1 + e)` for `0 < x`. -/
private theorem e5rl_rpow_mul_one_add (x : ℝ) (hx : 0 < x) (e : ℝ) :
    x * x ^ e = x ^ (1 + e) := by
  rw [Real.rpow_add hx 1 e, Real.rpow_one]

/-- The double-sum weight energy is at most `card * ∑ w²`
(`(∑ |w|)² ≤ card * ∑ w²`, Cauchy–Schwarz/Jensen) — the row-energy form of
`e5c_energy_card_sq`. -/
private theorem e5rl_energy_card {κ : Type*} [Fintype κ] (w : κ → ℝ) :
    ∑ j : κ, ∑ k : κ, |w j| * |w k| ≤ (Fintype.card κ : ℝ) * ∑ i : κ, w i ^ 2 := by
  have habseq : ∑ i : κ, |w i| ^ 2 = ∑ i : κ, w i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs _
  calc ∑ j : κ, ∑ k : κ, |w j| * |w k| = (∑ j : κ, |w j|) * (∑ k : κ, |w k|) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ i : κ, |w i|) ^ 2 := by rw [pow_two]
    _ ≤ (Fintype.card κ : ℝ) * ∑ i : κ, |w i| ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (Fintype.card κ : ℝ) * ∑ i : κ, w i ^ 2 := by rw [habseq]

/-! ### The rate of the spectral correlation energy -/

/-- **MAIN: the energy-rate link.**  Under the ordinary bandwidth data
(`0 < δ n` eventually, `δ n → 0`, `n δ n → ∞`), the long-memory band
`3/4 < f t` (so `ψ = 2 - 2 f t < 1/2`), the bounded chain-weight energy
`hU` (the `hW0/hU` shape of `Hurst.P5LogHLayers`), and the polynomial-mesh
window `2 * γ ≤ c * (4 * f t - 3)` with `(n:ℝ)^c ≤ (n:ℝ) * δ n` eventually
(`c > 0`; feasible iff `2γ ≤ (mesh exponent)·(4 f t - 3)`, non-vacuous exactly
when `f t > 3/4`), the spectral correlation energy of the P5 chain satisfies
EVENTUALLY

`∑∑ |w_j||w_k| corr_{jk}² ≤ (3 * U) · n^{-2γ} (log n)²`,

in EXACTLY the `hEnergy` shape consumed by
`Hurst.E5ChainInstantiation.e5_fluctuation_at_chain`. -/
theorem correlationEnergy_rate (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hlong : 3 / 4 < f t)
    (hU : ∃ U : ℝ, 0 ≤ U ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1ChainWeight f r n (δ n) t i) ^ 2 ≤ U)
    (c γ : ℝ) (_hc : 0 < c) (hwin : 2 * γ ≤ c * (4 * f t - 3))
    (hmesh : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c ≤ (n : ℝ) * δ n) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        ∑ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
          |actualQ1SpectralWeight f r n (δ n) t i| *
            |actualQ1SpectralWeight f r n (δ n) t k| *
            (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
              (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)) ^ 2
        ≤ E * (n : ℝ) ^ (-2 * γ) * (Real.log n) ^ 2 := by
  obtain ⟨U, hU0, hUn⟩ := hU
  -- long-memory exponent bookkeeping: ψ = 2 - 2 f t < 1/2, 1 - 2ψ = 4 f t - 3 > 0
  have hψlt : (2 : ℝ) - 2 * f t < 1 / 2 := by linarith
  have hpos : (0 : ℝ) < 4 * f t - 3 := by linarith
  -- the eventual bandwidth facts
  have hSpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * δ n := by
    filter_upwards [hδpos, eventually_ge_atTop 1] with n hδ hn
    exact mul_pos (by exact_mod_cast hn) hδ
  obtain ⟨_, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos hδ0 hN
  have hcardle : ∀ᶠ n : ℕ in atTop,
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤ 3 * ((n : ℝ) * δ n) := by
    filter_upwards [hratio.eventually_lt_const (by norm_num : (2 : ℝ) < 3), hSpos]
      with n hlt hS
    exact le_of_lt ((div_lt_iff₀ hS).mp hlt)
  refine ⟨3 * U, by linarith, ?_⟩
  filter_upwards [hcardle, hUn, hSpos, hmesh, eventually_ge_atTop 3]
    with n hcard hUn' hS hm hn3
  have hn1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn3
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℕ) < n by omega)
  -- step 1: the spectral weight energy `∑ w² = S^{2(ψ-1)} · ∑ u² ≤ S^{2(ψ-1)} · U`
  have hexpw : ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2
      = ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t - 1)) *
        ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1ChainWeight f r n (δ n) t i) ^ 2 := by
    unfold actualQ1SpectralWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, e5rl_rpow_sq ((n : ℝ) * δ n) hS.le]
  have hsumw : ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2
      ≤ ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t - 1)) * U := by
    rw [hexpw]
    exact mul_le_mul_of_nonneg_left hUn' (Real.rpow_nonneg hS.le _)
  -- step 2: the pointwise correlation bound `corr² ≤ 1` (unconditional)
  have hcorr : ∀ i k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)) ^ 2 ≤ 1 := by
    intro i k
    have h1 : |featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)| ≤ 1 := by
      simpa only [featureCorrelation] using
        abs_real_inner_div_norm_mul_norm_le_one
          (∑ j, actualQ1Coeff n (δ n) t i j •
            actualQ1Obs f n (midpointSampleHurst f hf.1 n) j)
          (∑ j, actualQ1Coeff n (δ n) t k j •
            actualQ1Obs f n (midpointSampleHurst f hf.1 n) j)
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans (one_pow 2).le
  -- step 3: energy ≤ card · ∑ w² (row-energy form, corr² ≤ 1 + Cauchy–Schwarz)
  have hE1 : ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |actualQ1SpectralWeight f r n (δ n) t i| *
          |actualQ1SpectralWeight f r n (δ n) t k| *
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)) ^ 2
      ≤ (Fintype.card (Fin (localWeightActiveSet n 1 (δ n) t).card) : ℝ) *
        ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_).trans
      (e5rl_energy_card (actualQ1SpectralWeight f r n (δ n) t))
    calc |actualQ1SpectralWeight f r n (δ n) t i| *
          |actualQ1SpectralWeight f r n (δ n) t k| *
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)) ^ 2
        ≤ |actualQ1SpectralWeight f r n (δ n) t i| *
            |actualQ1SpectralWeight f r n (δ n) t k| * 1 :=
        mul_le_mul_of_nonneg_left (hcorr i k)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |actualQ1SpectralWeight f r n (δ n) t i| *
            |actualQ1SpectralWeight f r n (δ n) t k| := by rw [mul_one]
  -- step 4: energy ≤ 3 U · S^{2ψ-1}
  have hsum0 : 0 ≤ ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have henergy : ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      ∑ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |actualQ1SpectralWeight f r n (δ n) t i| *
          |actualQ1SpectralWeight f r n (δ n) t k| *
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)) ^ 2
      ≤ (3 * U) * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1) := by
    rw [Fintype.card_fin] at hE1
    calc ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
            |actualQ1SpectralWeight f r n (δ n) t i| *
              |actualQ1SpectralWeight f r n (δ n) t k| *
              (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
                (actualQ1Coeff n (δ n) t i) (actualQ1Coeff n (δ n) t k)) ^ 2
        ≤ ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 := hE1
      _ ≤ (3 * ((n : ℝ) * δ n)) * ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            (actualQ1SpectralWeight f r n (δ n) t i) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard hsum0
      _ ≤ (3 * ((n : ℝ) * δ n)) *
            (((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t - 1)) * U) :=
          mul_le_mul_of_nonneg_left hsumw (mul_nonneg (by norm_num) hS.le)
      _ = (3 * U) * ((n : ℝ) * δ n * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t - 1))) := by
          ring
      _ ≤ (3 * U) * ((n : ℝ) * δ n) ^ (1 + 2 * (2 - 2 * f t - 1)) := by
          rw [e5rl_rpow_mul_one_add _ hS _]
      _ = (3 * U) * ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1) := by
          congr 2
          ring
  -- step 5: the mesh window `S^{2ψ-1} ≤ n^{-2γ}` (2ψ-1 = -(4ft-3) < 0, S ≥ n^c)
  have hnegexp : (2 : ℝ) * (2 - 2 * f t) - 1 = -(4 * f t - 3) := by ring
  have hcneg : 0 < ((n : ℝ) ^ c) ^ (4 * f t - 3) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hnR c) _
  have hSge : ((n : ℝ) ^ c) ^ (4 * f t - 3) ≤ ((n : ℝ) * δ n) ^ (4 * f t - 3) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hnR.le c) hm hpos.le
  have hmeshpow : ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1)
      ≤ ((n : ℝ) ^ c) ^ (2 * (2 - 2 * f t) - 1) := by
    rw [hnegexp, Real.rpow_neg hS.le, Real.rpow_neg (Real.rpow_nonneg hnR.le c)]
    exact inv_anti₀ hcneg hSge
  have hmeshfinal : ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 1) ≤ (n : ℝ) ^ (-2 * γ) := by
    have hstep : (n : ℝ) ^ (c * (2 * (2 - 2 * f t) - 1))
        = ((n : ℝ) ^ c) ^ (2 * (2 - 2 * f t) - 1) :=
      Real.rpow_mul hnR.le c _
    refine le_trans hmeshpow ?_
    have hexp : c * -(4 * f t - 3) = -(c * (4 * f t - 3)) := by ring
    rw [← hstep, hnegexp, hexp]
    have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    refine Real.rpow_le_rpow_of_exponent_le hn1r ?_
    linarith
  -- step 6: the log headroom `n^{-2γ} ≤ n^{-2γ} (log n)²` (1 ≤ (log n)² for n ≥ 3)
  have h3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hexpn : Real.exp (Real.log (n : ℝ)) = (n : ℝ) := Real.exp_log hnR
  have hkey : Real.exp 1 < Real.exp (Real.log (n : ℝ)) := by
    rw [hexpn]
    exact lt_of_lt_of_le Real.exp_one_lt_three h3r
  have hlog1 : (1 : ℝ) < Real.log (n : ℝ) := Real.exp_lt_exp.mp hkey
  refine le_trans
    (henergy.trans
      (mul_le_mul_of_nonneg_left hmeshfinal (mul_nonneg (by norm_num) hU0))) ?_
  refine le_mul_of_one_le_right ?_ ?_
  · exact mul_nonneg (mul_nonneg (by norm_num) hU0) (Real.rpow_nonneg hnR.le _)
  · have hpow2 : Real.log (n : ℝ) ^ 2 = Real.log (n : ℝ) * Real.log (n : ℝ) := pow_two _
    have hm1 : (0 : ℝ) ≤ Real.log (n : ℝ) - 1 := by linarith
    have hprod : (0 : ℝ) ≤ Real.log (n : ℝ) * (Real.log (n : ℝ) - 1) :=
      mul_nonneg (by linarith) hm1
    rw [hpow2]
    linarith

/-! ### The E5 fluctuation at the polynomial rate (the composition) -/

/-- **The composed E5 rate.**  Under the hypotheses of
`correlationEnergy_rate` (ordinary model, long-memory band, bounded
chain-weight energy, polynomial-mesh window) plus the chain nondegeneracy
`hane`, the calibrated known-scale statistic `X_n = (cσ - Ĝ_n)/(2 log n)` of
the P5 chain satisfies, for some explicit `F ≥ 0`,

`E|X_n - E X_n| ≤ F · n^{-γ}` eventually.

This discharges the energy-rate input of
`Hurst.E5ChainInstantiation.e5_fluctuation_at_chain` under the window:
`F = √(4 gaussianLogSquareVariance E)` with `E ≤ 3 U`. -/
theorem e5_fluctuation_rate_of_window (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (δ : ℕ → ℝ) (cσ γ c : ℝ)
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 (δ n) t).card),
      ∑ i, actualQ1Coeff n (δ n) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hlong : 3 / 4 < f t)
    (hU : ∃ U : ℝ, 0 ≤ U ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1ChainWeight f r n (δ n) t i) ^ 2 ≤ U)
    (hc : 0 < c) (hwin : 2 * γ ≤ c * (4 * f t - 3))
    (hmesh : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c ≤ (n : ℝ) * δ n) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop,
      ∫ x, |chainCalibratedStatistic f r n (δ n) t cσ x -
          ∫ y, chainCalibratedStatistic f r n (δ n) t cσ y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        ≤ F * (n : ℝ) ^ (-γ) :=
  e5_fluctuation_at_chain f hf r t δ cσ γ hane
    (correlationEnergy_rate f hf r t ht δ hδpos hδ0 hN hlong hU c γ hc hwin hmesh)
