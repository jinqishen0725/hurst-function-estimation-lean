import Hurst.P5LogHLayers
import Hurst.NormalizedLogVariance
import Hurst.NormalizedActualEnergy
import Hurst.NormalizedActualRemainder
import Hurst.FirstStrideActualRows
import Hurst.FeasibleRates
import Hurst.FeatureRowNondegenerate

/-!
# Unit variance rate of the actual known-scale log statistic (takeover10, task 1)

The honest-rate drift assembly (takeover10 task 2) consumes the SECOND
central moment of the untruncated known-scale transform, which by the exact
`2 log n`-scaling splits into the second central moment of the unit-weight
log statistic `Ĝ_n` over `(2 log n)²`.  This file supplies that variance rate
at the honest scale:

`∫ (Ĝ_n − E Ĝ_n)²  ≤  (4 · gaussianLogSquareVariance · U² · C) · S^(-2ψ)`,
`S = n · δ n = n^(1-γ)`, `ψ = 2 - 2 f t`,

with `U` the scaled-weight bound of `localPolynomialWeights_scaled_eventually_bounded`
and `C` the normalized correlation-energy bound of
`hurstHolder_q1_actual_normalized_energy_eventually_bounded` (its scalar rates
`hR`/`hcut`/`hEnv` are discharged internally at `R n = ⌊n^β⌋₊` with the window
midpoint `β = (1 - f t)(4 f t - 3)/2`, whose positivity needs only
`3/4 < f t`; the `hEnv` window at general `γ` is exactly
`(1 - γ)(2 - 2 f t) < 2 - 2 b`, i.e. AT `γ = f t` precisely the b-band datum
`(1 - f t)² < 1 - b`).

## Honest premise registration (deviation from the task book)

The task book stated task 1 under "model window + hlong" only.  The tail
envelope rate `hEnv` required by the normalized-energy theorem carries the
window `(1 - γ)(2 - 2 f t) < 2 - 2 b`, which at the endpoint rate `γ = f t`
IS the b-band datum — it cannot be discharged from the model window alone.
The theorem therefore takes the general-`γ` window `hgrid` as an explicit
premise; at `γ = f t` the consumer feeds `hgrid` from `hbband`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology

namespace Hurst

/-- **The unit variance rate.**  Under the model window and the grid window
`(1 - γ)(2 - 2 f t) < 2 - 2 b` (at the endpoint rate `γ = f t` this is the
b-band datum), the second central moment of the unit-weight known-scale log
statistic at the feasible bandwidth `δ n = n^(-γ)` is eventually bounded by
`(4 · gaussianLogSquareVariance · U² · C) · S^(-2ψ)` with `S = n^(1-γ)` and
`ψ = 2 - 2 f t`.  The constants `U` and `C` are the existential witnesses of
the scaled-weight and normalized-energy theorems. -/
theorem hurstHolder_q1_unitVariance_eventually_bounded
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (r : ℕ) :
    ∃ U ≥ 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∫ x, (p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t x -
          ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) ^ 2 ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      ≤ (4 * gaussianLogSquareVariance * U ^ 2 * C)
        * ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (-(2 * (2 - 2 * f t))) := by
  -- the bandwidth window facts (replicated from FullChainGeneralSigned)
  have hδpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) ^ (-γ)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hδ0 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-γ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hγ0).comp tendsto_natCast_atTop_atTop
  have hN : Tendsto (fun n : ℕ => ((n : ℝ) * ((n : ℝ) ^ (-γ)))) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (1 - γ))) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    refine Tendsto.congr' ?_ h1
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show ((1 : ℝ) - γ) = ((1 : ℝ) + (-γ)) by ring,
      Real.rpow_add hnR (1 : ℝ) (-γ), Real.rpow_one]
  -- the two existential constants
  obtain ⟨U, hU, hUw⟩ := localPolynomialWeights_scaled_eventually_bounded
    r 1 t ht (fun n => ((n : ℝ) ^ (-γ))) hδpos hδ0 hN
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hEnergy⟩ :=
    hurstHolder_q1_actual_normalized_energy_eventually_bounded
      p a b M hp ha hb hab hM f hf hF t ht hlong
  -- the internal scalar-rate instantiation at the window midpoint β
  have hft : f t ∈ Ioo (0 : ℝ) 1 := hf.1 ht
  have hψpos : 0 < 2 - 2 * f t := by linarith [hft.2]
  have hψhalf : 2 - 2 * f t < 1 / 2 := by linarith [hft.2]
  set β : ℝ := (1 - γ) * (4 * f t - 3) / 2 with hβdef
  have h4 : (0 : ℝ) < 4 * f t - 3 := by linarith
  have hβ0 : 0 < β := div_pos (mul_pos (sub_pos.mpr hγ1) h4) (by norm_num)
  have hβ' : β < (1 - γ) * (1 - 2 * (2 - 2 * f t)) := by
    have hw : (1 - γ) * (4 * f t - 3) = (1 - γ) * (1 - 2 * (2 - 2 * f t)) := by ring
    rw [hβdef, hw]
    nlinarith [mul_pos (sub_pos.mpr hγ1) h4]
  have hRn : ∀ᶠ n : ℕ in atTop, 1 ≤ (⌊(n : ℝ) ^ β⌋₊ : ℕ) :=
    (feasibleR_nat_tendsto β hβ0).eventually_ge_atTop 1
  have hcut := feasibleR_cut_tendsto f t γ β hγ1 hβ0 hβ'
  have hEnv := feasibleR_env_tendsto b Ccov Ctail L M (f t) γ β hγ0 hψpos hψhalf
    hgrid hβ0
  obtain ⟨C₂, hC₂, hEnergy'⟩ := hEnergy
  have hEv := hEnergy' (fun n => ((n : ℝ) ^ (-γ)))
    (fun n => (⌊(n : ℝ) ^ β⌋₊ : ℕ)) hδpos hδ0 hN hRn hcut hEnv
  refine ⟨U, hU, C₂, hC₂, ?_⟩
  filter_upwards [hEv, hUw, eventually_gt_atTop (0 : ℕ), hδpos] with n hEn hUwn hn0 hδn
  have haneAll := actualQ1_hane_all f hf ((n : ℝ) ^ (-γ)) t n
  have hS : 0 < (n : ℝ) * ((n : ℝ) ^ (-γ)) :=
    mul_pos (by exact_mod_cast hn0) (Real.rpow_pos_of_pos (by exact_mod_cast hn0) _)
  -- the normalized energy bound in the featureCorrelation form consumed by
  -- the variance lemma (the correlation identity on each pair of rows)
  have hcorr : ∀ i j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t i)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t j)
        = vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t i))
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)) :=
    fun i j => gridStrideFirst_correlation_identity n 1 hn0 (by norm_num)
      (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t i)
      (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j)
  have hE : ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (2 * (2 - 2 * f t) - 2) *
      (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
        ∑ k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t j)
            (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k)) ^ 2) ≤ C₂ := by
    have hsum : (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
            (featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
              (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t j)
              (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k)) ^ 2)
        = (∑ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
          ∑ k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
            (vectorCorrelation
              (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t j))
              (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                (localWeightActiveIndex n 1 ((n : ℝ) ^ (-γ)) t k))) ^ 2) :=
      Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => congrArg (fun z => z ^ 2) (hcorr j k)
    rw [hsum]
    exact hEn
  -- the scaled weights are eventually uniformly bounded
  have hu : ∀ j : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      |actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t j| ≤ U := fun j => hUwn _
  -- the variance rate at the unit weights
  have hvar := gaussianLogStatistic_variance_of_normalizedEnergy
    (v := actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    (u := actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t)
    (a := actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
    (ha := haneAll)
    (S := (n : ℝ) * ((n : ℝ) ^ (-γ))) (ψ := 2 - 2 * f t) (U := U) (C := C₂)
    (hS := hS) (hU := hU) (hu := hu) hE
  -- the MSE bridge to the second central moment of the known-scale statistic
  have hunfold : p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t
      = gaussianLogStatistic
          (fun i => ((n : ℝ) * ((n : ℝ) ^ (-γ)))⁻¹ *
            actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t i)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) := rfl
  have hcenter : (∫ x, gaussianLogStatistic
        (fun i => ((n : ℝ) * ((n : ℝ) ^ (-γ)))⁻¹ *
          actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t i)
        (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
      = ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) := by
    rw [hunfold]
  have hmse := gaussianLogStatistic_mse
    (v := actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    (w := fun i => ((n : ℝ) * ((n : ℝ) ^ (-γ)))⁻¹ *
      actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t i)
    (a := actualQ1Coeff n ((n : ℝ) ^ (-γ)) t)
    (∫ y, gaussianLogStatistic
      (fun i => ((n : ℝ) * ((n : ℝ) ^ (-γ)))⁻¹ *
        actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t i)
      (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) y ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
    haneAll
  have hstep : ∫ x, (p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t x -
        ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) ^ 2 ∂
      featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      = Var[gaussianLogStatistic
          (fun i => ((n : ℝ) * ((n : ℝ) ^ (-γ)))⁻¹ *
            actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t i)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t);
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))] := by
    rw [hunfold, hmse, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  calc ∫ x, (p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t x -
          ∫ y, p5KnownScaleLogStatistic f r n ((n : ℝ) ^ (-γ)) t y ∂
            featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) ^ 2 ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      = Var[gaussianLogStatistic
          (fun i => ((n : ℝ) * ((n : ℝ) ^ (-γ)))⁻¹ *
            actualQ1ChainWeight f r n ((n : ℝ) ^ (-γ)) t i)
          (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t);
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))] := hstep
    _ ≤ (4 * gaussianLogSquareVariance * U ^ 2 * C₂)
          * ((n : ℝ) * ((n : ℝ) ^ (-γ))) ^ (-(2 * (2 - 2 * f t))) := hvar

end Hurst
