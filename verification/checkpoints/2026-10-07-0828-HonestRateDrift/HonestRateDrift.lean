import Hurst.UnitVarianceRate
import Hurst.E5BiasExpansion
import Hurst.TruncationTransfer
import Hurst.CenterBandDischarge
import Hurst.HBiasSecondOrder

/-!
# The honest-rate drift lemma (takeover10, task 2)

The truth-centered endpoint needs, at the feasible bandwidth `δ n = n^(-(f t))`,
the honest-rate DRIFT

`seamScaleC f t δ n · |E Ĥ_n - f t| = 2 S^ψ log n · |E Ĥ_n - f t| → 0`,
`S = n^(1 - f t)`, `ψ = 2 - 2 f t`,

NOT an `n^(-(f t))`-rate hBias (which is unsatisfiable at `γ = f t` under the
long-memory band; see `Hurst.HBiasSecondOrder`).  The assembly decomposes

`E Ĥ_n - f t = [E H̃_n - f t] + [E Ĥ_n - E H̃_n]`

along the EXACT expectation identity:

* **Deterministic side** — `p5KnownScaleHtilde_drift_bound`
  (`Hurst.E5BiasExpansion`) at the pinned center `cσ = gaussianLogSquareMean`
  (which kills the constant offset), the k=0 Hölder-Lipschitz weight
  contraction `|∑ ŵ_j H_j - f t| ≤ Cw·D·(1+M)·δ` (rate `δ¹ = n^(-f t)`;
  the moment-conditions route `δ^p` is NOT needed since
  `2(1-f t)² - f t·p < 0` already at `p = 1`), and the second-order per-row
  log bound at rate `n^(-(2-2b))` (`gridStrideFirstActual_logNormSq_secondOrder`).
  Scaled drift ≤ `2·Dc·log n/n^(f t - 2(1-f t)²) + Cw·Clog₂/n^((2-2b) - 2(1-f t)²)`
  — the first exponent positive since `f t > 3/4 > 1/8 ≥ 2(1-f t)²`, the second
  EXACTLY the b-band `(1-f t)² < 1-b`.

* **Random side** — the TAIL-BASED truncation transfer `truncationCorrection_le`
  (`Hurst.TruncationTransfer`; the crude sd route is the twice-registered
  landmine and is NOT used): with `m = E H̃_n ∈ [d', 1-d']` (the center band
  `d' = (1-f t)/2` from `centerBand_hband_discharged`), second central moment
  `V = (4·gLSV·U²·C)·S^(-2ψ)/(2 log n)²` (task 1:
  `hurstHolder_q1_unitVariance_eventually_bounded` + the exact `2 log n`
  scaling) and Chebyshev tail `μ{d' ≤ |H̃-m|} ≤ V/d'²`, the clipping moves
  the mean by at most `V(1 + 1/d'²)`.  Scaled drift ≤
  `(1+1/d'²)·2·gLSV·U²·C/((n^((1-f t)ψ))·log n) → 0` UNCONDITIONALLY
  (`S^ψ → ∞` swamps `S^(-ψ)`).

## Honest premise registration (deviations from the task book)

* `ha : 1/2 < a` replaces the model window's `0 < a`: the second-order
  increment algebra (the mixed-power Lipschitz of `IncrementLogSecondOrder`)
  needs `2a > 1`.  Satisfiable jointly with the b-band (e.g. `f t = 0.8`,
  `a = 0.9`, `b = 0.95`).
* The k=0 contraction replaces the task book's `δ^p` bookkeeping (`p ≥ 1`
  makes the two routes converge at the same exponent; the k=0 route needs no
  `⌊p⌋ ≤ r` moment-window premise).
-/

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology ENNReal

namespace Hurst

/-- **The honest-rate drift lemma.**  Under the model window (with the
second-order band `1/2 < a`), the b-band datum `(1-f t)² < 1-b` and the
polynomial order `r`, the seam-scaled deviation of the clipped known-scale H
estimator from `f t` (at the pinned center `cσ = gaussianLogSquareMean`) has
vanishing honest-rate drift. -/
theorem honestRate_drift_tendsto_zero
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 1 / 2 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (hbband : (1 - f t) ^ 2 < 1 - b)
    (r : ℕ) :
    Tendsto (fun n : ℕ => |seamScaleC f t (fun m => ((m : ℝ) ^ (-(f t)))) n *
        ((∫ y, p5KnownScaleEstimator f r n ((n : ℝ) ^ (-(f t))) t gaussianLogSquareMean y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t)|)
      atTop (𝓝 0) := by
  have hft : f t ∈ Ioo (0 : ℝ) 1 := hf.1 ht
  -- the Lipschitz data of the Hölder class (k = 0)
  obtain ⟨D, hD0, hD⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  have hk0 : (0 : ℕ) < Nat.floor p := Nat.floor_pos.mpr hp
  have hlip : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      |f y - f x| ≤ D * (1 + M) * |y - x| := by
    intro x hx y hy
    have hh := hD M hM f hf 0 hk0 x hx y hy
    simpa only [iteratedDeriv_zero] using hh
  -- the weight stability package (order r, q = 1)
  obtain ⟨N₀, hN₀, Cw, hCw, hstab⟩ := localPolynomialWeights_uniform_stability r 1
  -- the second-order per-row log bound
  obtain ⟨Clog₂, hClog₂, hlog₂⟩ := gridStrideFirstActual_logNormSq_secondOrder
    p a b M hp ha hb hab hM
  -- the unit variance rate (task 1) at the endpoint rate γ = f t
  have hgrid : (1 - f t) * (2 - 2 * f t) < 2 - 2 * b := by
    have h2 : (1 - f t) * (2 - 2 * f t) = 2 * ((1 - f t) * (1 - f t)) := by ring
    have hbd : (1 - f t) * (1 - f t) < 1 - b := by simpa only [pow_two] using hbband
    rw [h2]; linarith
  obtain ⟨U, hU0, C₂, hC₂0, hVar⟩ := hurstHolder_q1_unitVariance_eventually_bounded
    p a b M hp (by linarith : 0 < a) hb hab hM f hf hF t ht hlong (f t) hft.1 hft.2 hgrid r
  -- the center band at the explicit band d' = (1 - f t)/2 (every fixed cσ)
  have hband := centerBand_hband_discharged p a b M hp (by linarith : 0 < a) hb hab hM
    f hf hF r t ht (f t) gaussianLogSquareMean hft.1 hft.2 hlong
  -- the bandwidth windows
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) ^ (-(f t))) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hδ0 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-(f t)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hft.1).comp tendsto_natCast_atTop_atTop
  have hδ12 : ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ (-(f t))) < 1 / 2 :=
    hδ0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hNtop : Tendsto (fun n : ℕ => ((n : ℝ) * ((n : ℝ) ^ (-(f t))))) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 - f t))) atTop atTop :=
      (tendsto_rpow_atTop (by linarith [hft.2])).comp tendsto_natCast_atTop_atTop
    refine Tendsto.congr' ?_ h1
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show ((1 : ℝ) - f t) = ((1 : ℝ) + (-(f t))) by ring,
      Real.rpow_add hnR (1 : ℝ) (-(f t)), Real.rpow_one]
  have hNS : ∀ᶠ n : ℕ in atTop, N₀ ≤ (n : ℝ) * ((n : ℝ) ^ (-(f t))) :=
    hNtop.eventually_ge_atTop N₀
  -- the second-order log smallness window
  have hδ2b0 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-(2 - 2 * b)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hsmall₀ : Tendsto (fun n : ℕ => Clog₂ * ((n : ℝ) ^ (-(2 - 2 * b)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hδ2b0.const_mul Clog₂
  have hsmall₂ : ∀ᶠ n : ℕ in atTop,
      Clog₂ * ((n : ℝ) ^ (-(2 - 2 * b))) < 1 / 2 :=
    hsmall₀.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  -- the two honest exponents and the three vanishing tails
  have h1ft : 0 < 1 - f t := by linarith [hft.2]
  have hψ0 : 0 < (1 - f t) * (2 - 2 * f t) := mul_pos h1ft (by linarith [hft.2])
  have hp2 : (1 - f t) * (2 - 2 * f t) = 2 * (1 - f t) ^ 2 := by ring
  have hftsq : (1 - f t) ^ 2 ≤ 1 / 8 := by nlinarith [hft.2, h1ft]
  set ca : ℝ := f t - 2 * (1 - f t) ^ 2 with hcadef
  have hca0 : 0 < ca := by rw [hcadef]; linarith [hft.2, hftsq]
  set cb : ℝ := (2 - 2 * b) - 2 * (1 - f t) ^ 2 with hcbdef
  have hcb0 : 0 < cb := by rw [hcbdef]; linarith
  have hlogden : Tendsto (fun n : ℕ =>
      (((n : ℝ) ^ ((1 - f t) * (2 - 2 * f t))) * Real.log (n : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ ((1 - f t) * (2 - 2 * f t)))) atTop atTop :=
      (tendsto_rpow_atTop hψ0).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact h1.atTop_mul_atTop₀ h2
  have ha0 : Tendsto (fun n : ℕ =>
      (2 * (Cw * (D * (1 + M)))) * (Real.log (n : ℝ) / ((n : ℝ) ^ ca))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (Real.log (n : ℝ) / ((n : ℝ) ^ ca))) atTop (𝓝 0) := by
      simpa only [pow_one] using nat_log_power_div_rpow_tendsto ca hca0 1
    simpa only [mul_zero] using h1.const_mul (2 * (Cw * (D * (1 + M))))
  have hb0 : Tendsto (fun n : ℕ => (Cw * Clog₂) / ((n : ℝ) ^ cb)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => ((n : ℝ) ^ cb)) atTop atTop :=
      (tendsto_rpow_atTop hcb0).comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (Cw * Clog₂) * (((n : ℝ) ^ cb)⁻¹)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply] using
        (tendsto_inv_atTop_zero.comp hden).const_mul (Cw * Clog₂)
    exact hinv.congr' (Eventually.of_forall fun n => by ring)
  have hc0 : Tendsto (fun n : ℕ =>
      (1 + 4 / (1 - f t) ^ 2) * ((2 * gaussianLogSquareVariance * U ^ 2 * C₂)
        / (((n : ℝ) ^ ((1 - f t) * (2 - 2 * f t))) * Real.log (n : ℝ)))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (2 * gaussianLogSquareVariance * U ^ 2 * C₂) *
        ((((n : ℝ) ^ ((1 - f t) * (2 - 2 * f t))) * Real.log (n : ℝ))⁻¹)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply] using
        (tendsto_inv_atTop_zero.comp hlogden).const_mul
        (2 * gaussianLogSquareVariance * U ^ 2 * C₂)
    have hmid : Tendsto (fun n : ℕ => (2 * gaussianLogSquareVariance * U ^ 2 * C₂)
        / (((n : ℝ) ^ ((1 - f t) * (2 - 2 * f t))) * Real.log (n : ℝ))) atTop (𝓝 0) := by
      refine hinv.congr' (Eventually.of_forall fun n => ?_)
      ring
    have h2 : Tendsto (fun n : ℕ => (1 + 4 / (1 - f t) ^ 2) *
        ((2 * gaussianLogSquareVariance * U ^ 2 * C₂)
          / (((n : ℝ) ^ ((1 - f t) * (2 - 2 * f t))) * Real.log (n : ℝ)))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hmid.const_mul (1 + 4 / (1 - f t) ^ 2)
    exact h2
  have hsum : Tendsto (fun n : ℕ =>
      (2 * (Cw * (D * (1 + M)))) * (Real.log (n : ℝ) / ((n : ℝ) ^ ca))
        + (Cw * Clog₂) / ((n : ℝ) ^ cb)
        + (1 + 4 / (1 - f t) ^ 2) * ((2 * gaussianLogSquareVariance * U ^ 2 * C₂)
            / (((n : ℝ) ^ ((1 - f t) * (2 - 2 * f t))) * Real.log (n : ℝ)))) atTop (𝓝 0) := by
    simpa only [zero_add, add_zero] using (ha0.add hb0).add hc0
  refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hsum
  filter_upwards [hδpos, hδ12, hNS, hsmall₂, hVar, hband,
    eventually_ge_atTop (2 : ℕ)] with n hnδ hn12 hNSn hl₂ hVarN hbandN hn2
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  set δn : ℝ := (n : ℝ) ^ (-(f t)) with hδndef
  have hδn : 0 < δn := hnδ
  have hδhalf : δn ≤ 1 / 2 := hn12.le
  set S : ℝ := (n : ℝ) * δn with hSdef
  have hSn : 0 < S := by rw [hSdef]; exact mul_pos (by exact_mod_cast hn0) hδn
  set δ₂n : ℝ := (n : ℝ) ^ (-(2 - 2 * b)) with hδ2def
  set pn : ℝ := (n : ℝ) ^ ((1 - f t) * (2 - 2 * f t)) with hpndef
  -- the S-power identities
  have hnR0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0.le
  have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hSform : S = (n : ℝ) ^ (1 - f t) := by
    have e0 : (n : ℝ) * ((n : ℝ) ^ (-(f t))) = ((n : ℝ) ^ (1 : ℝ)) * ((n : ℝ) ^ (-(f t))) := by
      rw [Real.rpow_one]
    rw [hSdef, hδndef, e0, ← Real.rpow_add hnRpos]
    ring_nf
  have hSψ : S ^ (2 - 2 * f t) = pn := by
    rw [hSform, ← Real.rpow_mul hnR0]
  have hpn2 : pn * pn = S ^ (2 * (2 - 2 * f t)) := by
    rw [← hSψ, ← Real.rpow_add hSn]
    congr 1
    ring
  have hS2ψinv : S ^ (-(2 * (2 - 2 * f t))) = (S ^ (2 * (2 - 2 * f t)))⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hSn.le]
    congr 1
    ring
  -- the S·δ products at the two honest exponents
  have hpnδ : pn * δn = (n : ℝ) ^ (-(ca)) := by
    have ha : pn * δn = (n : ℝ) ^ ((1 - f t) * (2 - 2 * f t) - f t) := by
      rw [hpndef, hδndef, ← Real.rpow_add hnRpos]
      ring_nf
    rw [ha]
    congr 2
    linarith [hcadef, hp2]
  have hpnδ2 : pn * δ₂n = (n : ℝ) ^ (-(cb)) := by
    have ha : pn * δ₂n = (n : ℝ) ^ ((1 - f t) * (2 - 2 * f t) - (2 - 2 * b)) := by
      rw [hpndef, hδ2def, ← Real.rpow_add hnRpos]
      ring_nf
    rw [ha]
    congr 2
    linarith [hcbdef, hp2]
  have hconvca : (n : ℝ) ^ (-(ca)) = ((n : ℝ) ^ ca)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hnR0]
    congr 1
    ring
  have hconvcb : (n : ℝ) ^ (-(cb)) = ((n : ℝ) ^ cb)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hnR0]
    congr 1
    ring
  -- the observation measure and the two statistics
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) with hμdef
  set Gfn : EuclideanSpace ℝ (Fin n) → ℝ :=
    p5KnownScaleLogStatistic f r n δn t with hGfndef
  set Hfn : EuclideanSpace ℝ (Fin n) → ℝ :=
    p5KnownScaleHtilde f r n δn t gaussianLogSquareMean with hHfndef
  have haneAll := actualQ1_hane_all f hf δn t n
  have hGmemLp : MemLp Gfn 2 μ :=
    gaussianLogStatistic_memLp_two (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (fun i => ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t i)
      (actualQ1Coeff n δn t) haneAll
  have hGint : Integrable Gfn μ := hGmemLp.integrable one_le_two
  -- the stability package at this n (unit sum, absolute sum)
  have hδIcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  obtain ⟨_, _, hwabsum, hmoments⟩ := hstab n hn0 (by omega) δn t hδn hδhalf hδIcc hNSn
  have hw1 : ∑ j : Fin (localWeightActiveSet n 1 δn t).card,
      ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j = 1 := by
    have hunit : ∀ j : Fin (localWeightActiveSet n 1 δn t).card,
        ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
          = localPolynomialWeights r n 1 δn t (localWeightActiveIndex n 1 δn t j) :=
      fun j => unitStatWeight_eq_localPolynomialWeight f r n δn t hSn j
    have hsum : (∑ j : Fin (localWeightActiveSet n 1 δn t).card,
        ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j)
        = (∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          localPolynomialWeights r n 1 δn t (localWeightActiveIndex n 1 δn t j)) :=
      Finset.sum_congr rfl fun j _ => hunit j
    rw [hsum]
    have hbr := localPolynomialWeights_sum_active r n 1 δn t (fun _ => (1 : ℝ))
    simp only [mul_one] at hbr
    rw [← hbr]
    have hmom := hmoments ⟨0, by omega⟩
    simpa using hmom
  have hWabs : ∑ j : Fin (localWeightActiveSet n 1 δn t).card,
      |((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j| ≤ Cw := by
    have hunit : ∀ j : Fin (localWeightActiveSet n 1 δn t).card,
        |((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j|
          = |localPolynomialWeights r n 1 δn t (localWeightActiveIndex n 1 δn t j)| :=
      fun j => by rw [unitStatWeight_eq_localPolynomialWeight f r n δn t hSn j]
    have hsum : (∑ j : Fin (localWeightActiveSet n 1 δn t).card,
        |((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j|)
        = (∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          |localPolynomialWeights r n 1 δn t (localWeightActiveIndex n 1 δn t j)|) :=
      Finset.sum_congr rfl fun j _ => hunit j
    rw [hsum, ← localPolynomialWeights_abs_sum_active r n 1 δn t]
    exact hwabsum
  -- the rowwise closeness of the sampled Hurst values to f t
  have hclose : ∀ j : Fin (localWeightActiveSet n 1 δn t).card,
      |((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
          (localWeightActiveIndex n 1 δn t j)) : ℝ)) - f t| ≤ D * (1 + M) * δn := by
    intro j
    have hmem0 : |(grid n (localWeightActiveIndex n 1 δn t j).val - t) / δn| < 1 := by
      simpa only [localWeightActiveSet, Finset.mem_filter, Finset.mem_univ, true_and]
        using localWeightActiveIndex_mem n 1 δn t j
    rw [abs_div, abs_of_pos hδn] at hmem0
    have hglt : |(grid n (localWeightActiveIndex n 1 δn t j).val - t)| < δn :=
      (div_lt_one hδn).mp hmem0
    have hgridmem : (grid n (localWeightActiveIndex n 1 δn t j).val)
        ∈ Ioo (0 : ℝ) 1 :=
      grid_mem n _ hn0 (lt_of_lt_of_le
        (localWeightActiveIndex n 1 δn t j).isLt (by omega))
    have hfL := hlip t ht (grid n (localWeightActiveIndex n 1 δn t j).val) hgridmem
    show |f (grid n (localWeightActiveIndex n 1 δn t j).val) - f t| ≤ _
    calc |f (grid n (localWeightActiveIndex n 1 δn t j).val) - f t|
        ≤ D * (1 + M) * |(grid n (localWeightActiveIndex n 1 δn t j).val) - t| := hfL
      _ ≤ D * (1 + M) * δn := mul_le_mul_of_nonneg_left hglt.le (by positivity)
  -- the k=0 weight contraction
  have hcontr : |∑ j : Fin (localWeightActiveSet n 1 δn t).card,
      ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
        * ((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
            (localWeightActiveIndex n 1 δn t j)) : ℝ)) - f t|
      ≤ Cw * (D * (1 + M)) * δn := by
    have hsplit : (∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
            * ((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
                (localWeightActiveIndex n 1 δn t j)) : ℝ))) - f t
        = ∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
            * (((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
                (localWeightActiveIndex n 1 δn t j)) : ℝ)) - f t) := by
      have hbody : ∀ j : Fin (localWeightActiveSet n 1 δn t).card,
          ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
            * (((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
                (localWeightActiveIndex n 1 δn t j)) : ℝ)) - f t)
          = ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
              * ((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
                  (localWeightActiveIndex n 1 δn t j)) : ℝ))
            - ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j * f t :=
        fun j => mul_sub _ _ _
      rw [Finset.sum_congr rfl (fun j _ => hbody j), Finset.sum_sub_distrib,
        ← Finset.sum_mul, hw1, one_mul]
    rw [hsplit]
    calc |∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
            * (((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
                (localWeightActiveIndex n 1 δn t j)) : ℝ)) - f t)|
        ≤ ∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          |((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j
            * (((midpointSampleHurst f hf.1 n (strideFirstLeft n 1
                (localWeightActiveIndex n 1 δn t j)) : ℝ)) - f t)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          |((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j|
            * (D * (1 + M) * δn) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hclose j) (abs_nonneg _)
      _ = (∑ j : Fin (localWeightActiveSet n 1 δn t).card,
            |((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j|)
            * (D * (1 + M) * δn) := by
          rw [← Finset.sum_mul]
      _ ≤ Cw * (D * (1 + M)) * δn := by
          have h := mul_le_mul_of_nonneg_right hWabs
            (by positivity : (0 : ℝ) ≤ D * (1 + M) * δn)
          have hXY : Cw * (D * (1 + M) * δn) = Cw * (D * (1 + M)) * δn := by ring
          linarith
  -- the second-order log bound
  have hlog : ∀ j : Fin (localWeightActiveSet n 1 δn t).card,
      |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 δn t j)‖ ^ 2)| ≤ Clog₂ * δ₂n :=
    fun j => hlog₂ n hn1 f hf hF (localWeightActiveIndex n 1 δn t j) hl₂.le
  -- the deterministic drift bound at the pinned center
  have hE0 : 0 ≤ Clog₂ * δ₂n := mul_nonneg hClog₂
    (Real.rpow_nonneg (by exact_mod_cast hn0.le) _)
  have hid := p5KnownScaleHtilde_drift_bound f r n hn1 δn t hδn gaussianLogSquareMean
    (midpointSampleHurst f hf.1 n) Cw (Cw * (D * (1 + M)) * δn) (Clog₂ * δ₂n) hE0
    haneAll hw1 hWabs hcontr hlog
  simp only [sub_self, abs_zero, zero_add] at hid
  -- the expectation of the untruncated transform
  have hint : (∫ x, Hfn x ∂μ)
      = (gaussianLogSquareMean - (∫ y, Gfn y ∂μ)) / (2 * Real.log n) := by
    have hHform : Hfn = fun x => (gaussianLogSquareMean - Gfn x) / (2 * Real.log n) := rfl
    have hform : (fun x => (gaussianLogSquareMean - Gfn x) / (2 * Real.log n))
        = fun x => (2 * Real.log n)⁻¹ * (gaussianLogSquareMean - Gfn x) := by
      funext x; ring
    rw [hHform, hform, integral_const_mul,
      integral_sub (integrable_const gaussianLogSquareMean) hGint]
    have hc : ∫ _x : EuclideanSpace ℝ (Fin n), (gaussianLogSquareMean : ℝ) ∂μ
        = gaussianLogSquareMean := by
      rw [integral_const]; simp
    rw [hc]
    ring
  set m : ℝ := ∫ x, Hfn x ∂μ with hmdef
  -- the second central moment of the untruncated transform
  have hGsqInt : Integrable (fun x => (Gfn x - (∫ y, Gfn y ∂μ)) ^ 2) μ := by
    have hGG : MemLp (fun x => Gfn x * Gfn x) 1 μ := hGmemLp.mul hGmemLp
    have hGGi := hGG.integrable (by norm_num)
    have hexpand : (fun x => (Gfn x - (∫ y, Gfn y ∂μ)) ^ 2)
        = fun x => Gfn x * Gfn x - (2 * (∫ y, Gfn y ∂μ)) * Gfn x
          + (∫ y, Gfn y ∂μ) ^ 2 := by
      funext x; ring
    rw [hexpand]
    have h1 : Integrable (fun x => (2 * (∫ y, Gfn y ∂μ)) * Gfn x) μ :=
      hGint.const_mul _
    exact (hGGi.sub h1).add (integrable_const _)
  -- the pointwise 2 log n-scaling of the centered square
  have hpt : (fun x => (Hfn x - m) ^ 2)
      = fun x => ((Gfn x - (∫ y, Gfn y ∂μ)) ^ 2) / (2 * Real.log n) ^ 2 := by
    funext x
    have hxc : Hfn x - m = -((Gfn x - (∫ y, Gfn y ∂μ)) / (2 * Real.log n)) := by
      have hHx : Hfn x = (gaussianLogSquareMean - Gfn x) / (2 * Real.log n) := rfl
      rw [hHx, hint]
      ring
    rw [hxc]
    ring
  have hVarScale : ∫ x, (Hfn x - m) ^ 2 ∂μ
      ≤ (4 * gaussianLogSquareVariance * U ^ 2 * C₂)
          * S ^ (-(2 * (2 - 2 * f t))) / (2 * Real.log n) ^ 2 := by
    rw [hpt]
    have hc2 : (2 : ℝ) * Real.log n ≠ 0 := by
      have := Real.log_pos (by exact_mod_cast hn1 : (1 : ℝ) < (n : ℝ)); linarith
    have hscal : ∫ x, ((Gfn x - (∫ y, Gfn y ∂μ)) ^ 2) / (2 * Real.log n) ^ 2 ∂μ
        = (∫ x, (Gfn x - (∫ y, Gfn y ∂μ)) ^ 2 ∂μ) / (2 * Real.log n) ^ 2 := by
      have hform : (fun x => ((Gfn x - (∫ y, Gfn y ∂μ)) ^ 2) / (2 * Real.log n) ^ 2)
          = fun x => ((2 * Real.log n) ^ 2)⁻¹ * (Gfn x - (∫ y, Gfn y ∂μ)) ^ 2 := by
        funext x; field_simp
      rw [hform, integral_const_mul, div_eq_mul_inv]
      ring
    rw [hscal]
    exact div_le_div_of_nonneg_right hVarN (by positivity)
  have hHsqInt : Integrable (fun x => (Hfn x - m) ^ 2) μ := by
    rw [hpt]
    exact hGsqInt.div_const _
  -- the measurability of the statistics (strongly-measurable route)
  have hGmeas : Measurable Gfn := by
    have hsmand : ∀ j : Fin (localWeightActiveSet n 1 δn t).card, StronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin n) => ((n : ℝ) * δn)⁻¹ *
          actualQ1ChainWeight f r n δn t j *
            Real.log (⟪actualQ1Coeff n δn t j, x⟫ ^ 2)) :=
      fun j => stronglyMeasurable_iff_measurable.mpr (by fun_prop)
    have hsum : StronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ j : Fin (localWeightActiveSet n 1 δn t).card,
          ((n : ℝ) * δn)⁻¹ * actualQ1ChainWeight f r n δn t j *
            Real.log (⟪actualQ1Coeff n δn t j, x⟫ ^ 2)) :=
      Finset.stronglyMeasurable_fun_sum _ fun j _ => hsmand j
    exact stronglyMeasurable_iff_measurable.mp hsum
  have hHmeas : Measurable Hfn := by
    have hHform : Hfn = fun x => (gaussianLogSquareMean - Gfn x) / (2 * Real.log n) := rfl
    rw [hHform]
    exact Measurable.div_const (Measurable.sub measurable_const hGmeas) _
  -- the center band for m = E H̃
  have hmband : (1 - f t) / 2 ≤ m ∧ m ≤ 1 - (1 - f t) / 2 := by
    rw [hint]
    exact hbandN
  have hmc : m ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hmband.1, h1ft], by linarith [hmband.2]⟩
  -- the tail set, its cover property and its Chebyshev bound
  set d' : ℝ := (1 - f t) / 2 with hd'def
  have hd'0 : 0 < d' := div_pos h1ft (by norm_num)
  have hcover : ∀ ω, Hfn ω ∉ Icc (0 : ℝ) 1 → d' ≤ |Hfn ω - m| := by
    intro ω hout
    rcases lt_trichotomy (Hfn ω) 0 with hx | hx | hx
    · have h1 : Hfn ω - m < 0 := by linarith [hmband.1, hx]
      rw [abs_of_neg h1]
      linarith [hmband.1, hx]
    · have hmem : Hfn ω ∈ Icc (0 : ℝ) 1 := by rw [hx]; exact ⟨le_rfl, zero_le_one⟩
      exact absurd hmem hout
    · rcases lt_trichotomy (Hfn ω) 1 with h1 | h1 | h1
      · exact absurd (show Hfn ω ∈ Icc (0 : ℝ) 1 from ⟨le_of_lt hx, le_of_lt h1⟩) hout
      · have hmem : Hfn ω ∈ Icc (0 : ℝ) 1 := by rw [h1]; exact ⟨zero_le_one, le_rfl⟩
        exact absurd hmem hout
      · have h2 : 0 ≤ Hfn ω - m := by linarith [hmband.2, h1]
        rw [abs_of_nonneg h2]
        linarith [hmband.2, h1]
  have hZmeas : Measurable (fun ω => |Hfn ω - m|) := (hHmeas.sub measurable_const).abs
  have hAm : MeasurableSet {ω | d' ≤ |Hfn ω - m|} :=
    measurableSet_le measurable_const hZmeas
  set Vq : ℝ := (4 * gaussianLogSquareVariance * U ^ 2 * C₂)
    * S ^ (-(2 * (2 - 2 * f t))) / (2 * Real.log n) ^ 2 with hVqdef
  have hVq0 : 0 ≤ Vq := by
    have hA : (0 : ℝ) ≤ 4 * gaussianLogSquareVariance * U ^ 2 * C₂ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
        (sq_nonneg U)) hC₂0
    have hB : (0 : ℝ) ≤ S ^ (-(2 * (2 - 2 * f t))) := Real.rpow_nonneg hSn.le _
    exact div_nonneg (mul_nonneg hA hB) (by positivity)
  have htail : (μ {ω | d' ≤ |Hfn ω - m|}).toReal ≤ Vq / d' ^ 2 := by
    have hZ2 : Measurable (fun ω => (|Hfn ω - m|) ^ 2) := by fun_prop
    have hFmeas : AEStronglyMeasurable (fun ω => ENNReal.ofReal ((|Hfn ω - m|) ^ 2)) μ :=
      (hZ2.ennreal_ofReal).aestronglyMeasurable
    have hz2 : ∀ ω, |Hfn ω - m| ^ 2 = (Hfn ω - m) ^ 2 := fun ω => by
      rw [← abs_pow (Hfn ω - m) 2]; exact abs_sq (Hfn ω - m)
    have hinteq : ∫ ω, (|Hfn ω - m|) ^ 2 ∂μ = ∫ ω, (Hfn ω - m) ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall hz2)
    have hintle : ∫ ω, (|Hfn ω - m|) ^ 2 ∂μ ≤ Vq := by
      rw [hinteq]
      exact hVarScale
    have hZ2int : Integrable (fun ω => (|Hfn ω - m|) ^ 2) μ :=
      hHsqInt.congr (Eventually.of_forall fun ω => (hz2 ω).symm)
    have hlint : ∫⁻ ω, ENNReal.ofReal ((|Hfn ω - m|) ^ 2) ∂μ ≤ ENNReal.ofReal Vq := by
      rw [← ofReal_integral_eq_lintegral_ofReal hZ2int
        (Eventually.of_forall fun ω => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hintle
    have hmono : {ω | d' ≤ |Hfn ω - m|}
        ⊆ {ω | ENNReal.ofReal (d' ^ 2) ≤ ENNReal.ofReal ((|Hfn ω - m|) ^ 2)} := by
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      have h1 : d' * d' ≤ |Hfn ω - m| * d' := mul_le_mul_of_nonneg_right hω hd'0.le
      have h2 : |Hfn ω - m| * d' ≤ |Hfn ω - m| * |Hfn ω - m| :=
        mul_le_mul_of_nonneg_left hω (abs_nonneg _)
      calc d' ^ 2 = d' * d' := by ring
        _ ≤ |Hfn ω - m| * d' := h1
        _ ≤ |Hfn ω - m| * |Hfn ω - m| := h2
        _ = (|Hfn ω - m|) ^ 2 := by ring
    have hmarkov := meas_ge_le_of_lintegral_pow (k := 2) (Z := fun ω => Hfn ω - m)
      hFmeas.aemeasurable hlint (t := ENNReal.ofReal (d' ^ 2))
    have hle : ENNReal.ofReal (d' ^ 2) * μ {ω | d' ≤ |Hfn ω - m|} ≤ ENNReal.ofReal Vq :=
      le_trans (mul_le_mul_left' (measure_mono hmono) _) hmarkov
    have hd'2pos : (0 : ℝ) < d' ^ 2 := sq_pos_of_pos hd'0
    have htoReal : (μ {ω | d' ≤ |Hfn ω - m|}).toReal * d' ^ 2 ≤ Vq := by
      have hμ1 : μ {ω | d' ≤ |Hfn ω - m|} ≤ 1 :=
        le_trans (measure_mono (subset_univ _))
          (le_of_eq (measure_univ : (μ Set.univ) = 1))
      have hμStop : μ {ω | d' ≤ |Hfn ω - m|} ≠ ∞ := by
        have h5 : μ {ω | d' ≤ |Hfn ω - m|} < ∞ :=
          lt_of_le_of_lt hμ1 (by norm_num)
        exact h5.ne
      have h1 : ((ENNReal.ofReal (d' ^ 2) * μ {ω | d' ≤ |Hfn ω - m|}).toReal)
          ≤ (ENNReal.ofReal Vq).toReal := by
        refine (ENNReal.toReal_le_toReal ?_ ENNReal.ofReal_ne_top).mpr hle
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμStop
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hd'2pos),
        ENNReal.toReal_ofReal hVq0] at h1
      calc (μ {ω | d' ≤ |Hfn ω - m|}).toReal * d' ^ 2
          = d' ^ 2 * (μ {ω | d' ≤ |Hfn ω - m|}).toReal := by ring
        _ ≤ Vq := h1

    exact (le_div_iff₀ hd'2pos).mpr htoReal
  -- the truncation transfer
  have hEstInt : (∫ y, p5KnownScaleEstimator f r n δn t gaussianLogSquareMean y ∂μ)
      = ∫ x, p5Trunc01 (Hfn x) ∂μ := by rfl
  have hXint : Integrable Hfn μ := by
    have hHform : Hfn = fun x => (gaussianLogSquareMean - Gfn x) / (2 * Real.log n) := rfl
    rw [hHform]
    exact ((integrable_const gaussianLogSquareMean).sub hGint).div_const _
  have htt := truncationCorrection_le (X := Hfn) (μ := μ)
    hHmeas.aestronglyMeasurable hXint rfl hmc hHsqInt hVq0 hVarScale
    (by positivity : (0 : ℝ) ≤ Vq / d' ^ 2) hcover hAm htail
  rw [← hmdef] at htt
  -- the seam identity and the vanishing-tail identities
  have hseam : seamScaleC f t (fun mm => ((mm : ℝ) ^ (-(f t)))) n
      = 2 * S ^ (2 - 2 * f t) * Real.log n := by
    rw [hSdef, hδndef]
    rfl
  have hpnpos : (0 : ℝ) < pn := Real.rpow_pos_of_pos (by exact_mod_cast hn0) _
  have hseam0 : 0 < seamScaleC f t (fun mm => ((mm : ℝ) ^ (-(f t)))) n := by
    rw [hseam, hSψ]
    exact mul_pos (mul_pos (by norm_num) hpnpos)
      (Real.log_pos (by exact_mod_cast hn1 : (1 : ℝ) < (n : ℝ)))
  have hkey : pn * pn * (S ^ (2 * (2 - 2 * f t)))⁻¹ = 1 := by
    rw [hpn2]
    field_simp [(Real.rpow_pos_of_pos hSn _).ne']
  -- e1: the scaled contraction term
  have e1 : 2 * S ^ (2 - 2 * f t) * Real.log n * (Cw * (D * (1 + M)) * δn)
      = (2 * (Cw * (D * (1 + M)))) * (Real.log n / (n : ℝ) ^ ca) := by
    have hmain : pn * δn = ((n : ℝ) ^ ca)⁻¹ := by rw [hpnδ, hconvca]
    calc 2 * S ^ (2 - 2 * f t) * Real.log n * (Cw * (D * (1 + M)) * δn)
        = 2 * (Cw * (D * (1 + M))) * (pn * δn) * Real.log n := by rw [hSψ]; ring
      _ = 2 * (Cw * (D * (1 + M))) * (((n : ℝ) ^ ca)⁻¹) * Real.log n := by rw [hmain]
      _ = (2 * (Cw * (D * (1 + M)))) * (Real.log n / (n : ℝ) ^ ca) := by
          rw [inv_eq_one_div]; ring
  -- e2: the scaled second-order log term
  have hc2' : (2 : ℝ) * Real.log n ≠ 0 := by
    have := Real.log_pos (by exact_mod_cast hn1 : (1 : ℝ) < (n : ℝ)); linarith
  have e2 : 2 * S ^ (2 - 2 * f t) * Real.log n
        * (Cw * (Clog₂ * δ₂n) / (2 * Real.log n))
      = (Cw * Clog₂) / (n : ℝ) ^ cb := by
    have hmain2 : pn * δ₂n = ((n : ℝ) ^ cb)⁻¹ := by rw [hpnδ2, hconvcb]
    have hstep2 : 2 * pn * Real.log n * (Cw * (Clog₂ * δ₂n) / (2 * Real.log n))
        = Cw * Clog₂ * (pn * δ₂n) := by
      have hlogne : Real.log n ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hn1 : (1 : ℝ) < (n : ℝ))).ne'
      field_simp [hc2', hlogne]
    calc 2 * S ^ (2 - 2 * f t) * Real.log n * (Cw * (Clog₂ * δ₂n) / (2 * Real.log n))
        = Cw * Clog₂ * (pn * δ₂n) := by rw [hSψ]; exact hstep2
      _ = Cw * Clog₂ * (((n : ℝ) ^ cb)⁻¹) := by rw [hmain2]
      _ = (Cw * Clog₂) / (n : ℝ) ^ cb := by rw [inv_eq_one_div]; ring
  -- e3: the scaled variance term
  have e3 : 2 * S ^ (2 - 2 * f t) * Real.log n * Vq
      = (2 * gaussianLogSquareVariance * U ^ 2 * C₂) / (pn * Real.log n) := by
    rw [hVqdef, hS2ψinv, hSψ]
    have hY : (S ^ (2 * (2 - 2 * f t)))⁻¹ = (pn * pn)⁻¹ :=
      eq_inv_of_mul_eq_one_right hkey
    rw [hY]
    field_simp [hc2', hpnpos.ne']
    ring
  -- 1/d'² = 4/(1-f t)²
  have hinvd' : 1 / d' ^ 2 = 4 / (1 - f t) ^ 2 := by
    rw [hd'def]
    field_simp
    ring
  have hsplit3 : (2 * S ^ (2 - 2 * f t) * Real.log n) *
      (Vq + Vq / d' ^ 2 + (Cw * (D * (1 + M)) * δn
        + Cw * (Clog₂ * δ₂n) / (2 * Real.log n)))
    = 2 * S ^ (2 - 2 * f t) * Real.log n * (Cw * (D * (1 + M)) * δn)
      + (2 * S ^ (2 - 2 * f t) * Real.log n
          * (Cw * (Clog₂ * δ₂n) / (2 * Real.log n)))
      + (2 * S ^ (2 - 2 * f t) * Real.log n * Vq) * (1 + 1 / d' ^ 2) := by
    ring
  -- the final squeeze
  have hE4 : ((∫ y, p5KnownScaleEstimator f r n δn t gaussianLogSquareMean y ∂μ) - f t)
      = ((∫ x, p5Trunc01 (Hfn x) ∂μ) - m) + (m - f t) := by
    rw [hEstInt]
    ring
  have hsplit2 : |((∫ y, p5KnownScaleEstimator f r n δn t gaussianLogSquareMean y ∂μ) - f t)|
      ≤ |((∫ x, p5Trunc01 (Hfn x) ∂μ) - m)| + |m - f t| := by
    rw [hE4]
    exact abs_add_le _ _
  have hstep : |((∫ x, p5Trunc01 (Hfn x) ∂μ) - m)| + |m - f t|
      ≤ Vq + Vq / d' ^ 2
        + (Cw * (D * (1 + M)) * δn + Cw * (Clog₂ * δ₂n) / (2 * Real.log n)) := by
    have h1 := htt
    have h2 := hid
    linarith
  calc |seamScaleC f t (fun mm => ((mm : ℝ) ^ (-(f t)))) n *
        ((∫ y, p5KnownScaleEstimator f r n δn t gaussianLogSquareMean y ∂μ) - f t)|
      = seamScaleC f t (fun mm => ((mm : ℝ) ^ (-(f t)))) n *
          |(∫ y, p5KnownScaleEstimator f r n δn t gaussianLogSquareMean y ∂μ) - f t| := by
        rw [abs_mul, abs_of_pos hseam0]
    _ ≤ seamScaleC f t (fun mm => ((mm : ℝ) ^ (-(f t)))) n *
          (Vq + Vq / d' ^ 2 + (Cw * (D * (1 + M)) * δn
            + Cw * (Clog₂ * δ₂n) / (2 * Real.log n))) := by
        refine mul_le_mul_of_nonneg_left (le_trans hsplit2 hstep) (le_of_lt hseam0)
    _ = (2 * (Cw * (D * (1 + M)))) * (Real.log n / (n : ℝ) ^ ca)
          + (Cw * Clog₂) / (n : ℝ) ^ cb
          + (1 + 4 / (1 - f t) ^ 2) * ((2 * gaussianLogSquareVariance * U ^ 2 * C₂)
              / (pn * Real.log n)) := by
        rw [hseam, hsplit3, e1, e2, e3, hinvd']
        ring

end Hurst
