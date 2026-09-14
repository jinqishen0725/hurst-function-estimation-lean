import Hurst.FrozenHsmallMirror
import Hurst.ActualQuadratureFinal
import Hurst.ActualFirstLongWeightedKernel
import Hurst.MeshFactorizationLimit
import Hurst.BandPowerSum
import Hurst.RieszQuadratureInstance
import Hurst.ActualFirstLongOffDiagonal

/-!
# The frozen-side quadrature: the `hFquad` assembly of the corrected route

This file is the LAST assembly of the corrected route: it lands the frozen-side
quadrature input `hFquad` of `Hurst.frozenHsmallMirror`,

`Tendsto (fun n => tr(F_n ^ k)) atTop
  (𝓝 (weightedRieszCycleIntegral k psi c (equivalentKernel r)))`,

with `F_n = actualQ1NormalizedFrozenMatrix f hf r n (δ n) t`, `psi = 2 - 2 * f t`,
`c = f t * (2 * f t - 1)`, in the shape consumed to close
`Hurst.actualQ1_trace_pow_tendsto_of_frozenPert`.

## What is landed here

1. **(A) The row-profile bridge** `frozenQuadRowProfile_tendsto`: the frozen row
   weight `u_i = actualQ1ChainWeight = S * localPolynomialWeights` converges
   UNIFORMLY over `i` to the continuum profile value
   `omega(g_i) = equivalentKernel r (rieszCycleGridPoint m i)` with
   `g_i = 2 * (i+1) / m - 1` — exactly the coordinate of `rieszCycleGridPoint`,
   so the bridge matches the Riesz quadrature row profile EXACTLY (no constant
   adaptation needed).  This is the specialization of
   `localPolynomialWeights_active_rank_uniform_tendsto` at `q = 1`.
2. **(B1) The far-band `16/x` class envelope** `frozenQuadClassSixteen_le`: at
   the SELF pair `h = k = h0 = f t` (so the log-hypothesis is vacuous at
   `M = 0`), `firstIncrementCrossLagCorrelation_scaled_error_le_explicit`
   collapses to the pure power-law envelope
   `|d^psi * firstIncrementLagCorrelation (f t) d - c| <= 16 / d` for `d >= 2`
   (every concentration term carries a zero factor).
3. **(B2) The far-band entry envelope** `frozenQuadFarBandEntry_le`: on the far
   band `dist >= 2`, the frozen-vs-Riesz ENTRY difference obeys
   `|F_n i j - T_n i j| <= S^{psi-1} * (eps * B + B_omega * (eps + 16 * d^{-psi} / d))`,
   combining (A) at precision `eps`, the per-class convergence (precision
   `eps`), the uniform per-lag box bound `B`, and (B1).  This is the per-entry
   `16/x`-relative machinery feeding the word assembly.
4. The **unconditional Riesz-side limit** `frozenQuad_riesz_trace_pow`:
   `tr(T_n ^ k) -> weightedRieszCycleIntegral k psi c (equivalentKernel r)`
   along the active grid, extracted as a standalone theorem (the `hriesz`
   derivation inside `frozenQ1_trace_pow_tendsto_of_farBand`, made directly
   available).
5. **(C) The conditional `hFquad` assembly** `frozenQuad_hFquad_of_farWord`:
   given the far-band word input (the `hsmall` shape), `hFquad` follows by
   transport through `frozenQ1_trace_pow_tendsto_of_farBand`.

## Honest gap note (the one remaining step)

The word-level assembly reducing `hFarWord` to (A) + (B2) is NOT proved here:
words with at least one far-frozen edge must be bounded by the rotation engine
(`trace_matWord_bound` / `sum_abs_trace_matWord_le_true` of
`Hurst.BandRemovalSharp`) with the far-band factors stratified by (B2)'s
`16/x` envelope and the `2 * psi < 1` band power sums
(`Hurst.BandPowerSum`), and the near-band part is closed by
`frozenHsmall_class_eps` / `frozenQ1_kernel_nearBand_bounded`
(`Hurst.FrozenHsmallMirror` / `Hurst.FrozenQuadratureRun`).  The direct
Frobenius route is void (`‖T_n‖_F ~ S^psi -> infinity` before normalization of
the word sum), which is precisely why the sharp word machinery is required.
Everything short of that single assembly — the near band (closed), the Riesz
side (unconditional), and the far-band per-entry envelope (B2) with the EXACT
profile constants — is proved here.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ### (A) The row-profile bridge -/

/-- **(A) The row-profile bridge.**  The frozen row weight
`u_i = actualQ1ChainWeight f r n δ t i = S * localPolynomialWeights …`
converges uniformly over the active indices to the continuum profile value
`equivalentKernel r (rieszCycleGridPoint m i)`, `g_i = 2 * (i+1)/m - 1`.
The coordinate matches `rieszCycleGridPoint` EXACTLY, so the bridge feeds the
Riesz quadrature row profile with no constant adaptation. -/
theorem frozenQuadRowProfile_tendsto
    (r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (f : ℝ → ℝ) :
    ∀ eps > 0, ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        |actualQ1ChainWeight f r n (δ n) t i -
          equivalentKernel r (rieszCycleGridPoint
            (localWeightActiveSet n 1 (δ n) t).card i)| ≤ eps := by
  intro eps heps
  simpa only [actualQ1ChainWeight, rieszCycleGridPoint] using
    localPolynomialWeights_active_rank_uniform_tendsto r 1 t ht δ hδpos hδ0 hN
      eps heps

/-! ### The uniform per-lag box bound -/

/-- The fixed-lag cross correlation is uniformly bounded on the compact box
`Icc a b ×ˢ Icc a b` of admissible Hurst parameters (compactness of the
continuously-extended absolute value; no concentration needed). -/
theorem frozenQuad_boxLagBound (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (d : ℕ) :
    ∃ B ≥ 0, ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b →
      |firstIncrementCrossLagCorrelation x y (d : ℝ)| ≤ B := by
  have hcont : ContinuousOn (fun z : ℝ × ℝ =>
      firstIncrementCrossLagCorrelation z.1 z.2 (d : ℝ))
      (Icc a b ×ˢ (Icc a b)) := fun z hz =>
    (firstIncrementCrossLagCorrelation_continuousAt z.1 z.2 (d : ℝ)
      (lt_of_lt_of_le ha hz.1.1) (lt_of_le_of_lt hz.1.2 hb)
      (lt_of_lt_of_le ha hz.2.1) (lt_of_le_of_lt hz.2.2 hb)).continuousWithinAt
  have haI : a ∈ Icc a b := ⟨le_refl a, hab⟩
  have hmem : (a, a) ∈ Icc a b ×ˢ (Icc a b) := Set.mem_prod.mpr ⟨haI, haI⟩
  obtain ⟨x, hx, hmax⟩ := (IsCompact.prod isCompact_Icc isCompact_Icc).exists_isMaxOn
    ⟨(a, a), hmem⟩ (hcont.abs)
  refine ⟨|firstIncrementCrossLagCorrelation x.1 x.2 (d : ℝ)|, abs_nonneg _, ?_⟩
  intro y z hy hz
  rw [isMaxOn_iff] at hmax
  exact hmax (y, z) (Set.mem_prod.mpr ⟨hy, hz⟩)

/-! ### (B1) The far-band `16/x` class envelope -/

/-- **(B1) The far-band `16/x` class envelope.**  At the self pair
`h = k = h0 = f t` the scaled error machinery
`firstIncrementCrossLagCorrelation_scaled_error_le_explicit` collapses (all
concentration terms carry a zero factor; the log hypothesis holds at `M = 0`)
to the pure power-law envelope: for every rank distance `d ≥ 2`,
`|d ^ psi * firstIncrementLagCorrelation (f t) d - c| ≤ 16 / d` with
`psi = 2 - 2 * f t`, `c = f t * (2 * f t - 1)`. -/
theorem frozenQuadClassSixteen_le (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (h0 : ℝ) (hh0 : h0 ∈ Icc a b) (d : ℕ) (hd : 2 ≤ d) :
    |((d : ℝ) ^ (2 - 2 * h0)) * firstIncrementCrossLagCorrelation h0 h0 (d : ℝ)
        - h0 * (2 * h0 - 1)|
      ≤ 16 * ((d : ℝ)⁻¹) := by
  obtain ⟨C, hC, hraw⟩ :=
    firstIncrementCrossLagCorrelation_scaled_error_le_explicit a b ha hb hab
  have hlog : |(h0 + h0 - 2 * h0) * Real.log ((d : ℝ))| ≤ (0 : ℝ) := by
    rw [show (h0 + h0 - 2 * h0 : ℝ) = 0 from by ring, zero_mul, abs_zero]
  have hraw' := hraw h0 h0 h0 (d : ℝ) (2 - 2 * h0) 0 hh0 hh0 hh0
    (by exact_mod_cast hd) (by norm_num) rfl hlog
  rw [show (h0 + h0 - 2 * h0 : ℝ) = 0 from by ring] at hraw'
  simp only [sub_self, abs_zero, Real.exp_zero, zero_mul, mul_zero, add_zero,
    zero_add, one_mul, mul_one] at hraw'
  linarith

/-! ### (B2) The far-band entry envelope -/

/-- **(B2) The far-band entry envelope.**  On the far band `dist(i,j) = d ≥ 2`,
the normalized frozen-vs-Riesz entry difference obeys
`|F_n i j - T_n i j| ≤ S^{ψ-1} * (eps * B + B_omega * (eps + 16 * d^{-ψ} / d))`
where `eps` is the simultaneous precision of (i) the row-profile bridge (A)
(`|u_i - omega(g_i)| ≤ eps`) and (ii) the per-class convergence
(`|corr(x, y, d) - lagcorr(f t) d| ≤ eps`), `B` is the uniform per-lag box
bound (`frozenQuad_boxLagBound`), and the `16 / d` term is (B1).  This is the
per-entry `16/x`-relative agreement of the frozen kernel with the pure power
law `c * d^{-ψ}` row-scaled by `omega(g_i)` — the input of the far-band word
assembly. -/
theorem frozenQuadFarBandEntry_le
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r n : ℕ) (hn : 0 < n) (δ t : ℝ) (hS : 0 < (n : ℝ) * δ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card)
    (d : ℕ) (hdij : Nat.dist (localWeightActiveIndex n 1 δ t i).val
        (localWeightActiveIndex n 1 δ t j).val = d)
    (hdrank : Nat.dist i.val j.val = d)
    (hd2 : 2 ≤ d)
    (x y : ℝ)
    (hx : (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ) = x)
    (hy : (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ) = y)
    (eps B B_omega : ℝ)
    (hprof : |actualQ1ChainWeight f r n δ t i -
        equivalentKernel r (rieszCycleGridPoint
          (localWeightActiveSet n 1 δ t).card i)| ≤ eps)
    (hcorrB : |firstIncrementCrossLagCorrelation x y (d : ℝ)| ≤ B)
    (hclass : |firstIncrementCrossLagCorrelation x y (d : ℝ)
        - firstIncrementLagCorrelation (f t) (d : ℝ)| ≤ eps)
    (homega : ∀ z : ℝ, |equivalentKernel r z| ≤ B_omega)
    (h16 : |((d : ℝ) ^ (2 - 2 * f t)) *
          firstIncrementLagCorrelation (f t) (d : ℝ)
        - f t * (2 * f t - 1)| ≤ 16 * ((d : ℝ)⁻¹)) :
    |actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
        actualQ1RieszMatrix f r n δ t i j|
      ≤ ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
        * (eps * B + B_omega
            * (eps + 16 * ((d : ℝ) ^ (-(2 - 2 * f t))) * ((d : ℝ)⁻¹))) := by
  classical
  have hpos : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have hd1 : 0 < d := by omega
    exact_mod_cast hd1
  have hdne : Nat.dist i.val j.val ≠ 0 := by
    rw [hdrank]; omega
  -- the frozen entry: S^{-1} * u_i * S^ψ * corr
  have hFk := frozenQ1_kernel_eq_crossLagCorrelation f hf n hn δ t
    ((n : ℝ) * δ) i j
  rw [hx, hy] at hFk
  have hFn : actualQ1NormalizedFrozenMatrix f hf r n δ t i j
      = ((n : ℝ) * δ)⁻¹ * (actualQ1ChainWeight f r n δ t i *
          actualQ1FrozenApproxKernel f hf n δ t ((n : ℝ) * δ) i j) := rfl
  -- the Riesz entry: S^{-1} * omega(g_i) * c * S^ψ * d^{-ψ}
  have hTn : actualQ1RieszMatrix f r n δ t i j
      = ((n : ℝ) * δ)⁻¹ * (equivalentKernel r (rieszCycleGridPoint
            (localWeightActiveSet n 1 δ t).card i)
          * ((f t * (2 * f t - 1)) * ((n : ℝ) * δ) ^ (2 - 2 * f t)
            * ((d : ℝ) ^ (-(2 - 2 * f t))))) := by
    show ((n : ℝ) * δ)⁻¹ * equivalentKernel r
        (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i) *
        rankRieszKernel ((n : ℝ) * δ) (2 - 2 * f t)
        (f t * (2 * f t - 1)) i j = _
    unfold rankRieszKernel rankRieszUnitKernel
    rw [if_neg hdne, hdrank]
    ring
  -- the common scale
  have hscale : ((n : ℝ) * δ)⁻¹ * ((n : ℝ) * δ) ^ (2 - 2 * f t)
      = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) := by
    rw [Real.rpow_sub hS (2 - 2 * f t) 1, Real.rpow_one]; ring
  have hkey : actualQ1NormalizedFrozenMatrix f hf r n δ t i j -
        actualQ1RieszMatrix f r n δ t i j
      = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
        * (actualQ1ChainWeight f r n δ t i *
            firstIncrementCrossLagCorrelation x y (d : ℝ)
          - equivalentKernel r (rieszCycleGridPoint
              (localWeightActiveSet n 1 δ t).card i)
            * ((f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))))) := by
    rw [hFn, hFk, hdij, hTn, ← mul_sub, ← hscale]
    ring
  -- the absolute-value bookkeeping
  have hωB : |equivalentKernel r (rieszCycleGridPoint
      (localWeightActiveSet n 1 δ t).card i)| ≤ B_omega := homega _
  have hω0 : (0 : ℝ) ≤ B_omega := le_trans (abs_nonneg _) (homega 0)
  have hdψ0 : (0 : ℝ) ≤ (d : ℝ) ^ (-(2 - 2 * f t)) :=
    Real.rpow_nonneg hpos _
  have hunity : ((d : ℝ) ^ (-(2 - 2 * f t)))
      * ((d : ℝ) ^ (2 - 2 * f t)) = 1 := by
    rw [mul_comm, ← Real.rpow_add hdpos (2 - 2 * f t) (-(2 - 2 * f t)),
      show ((2 - 2 * f t : ℝ) + -(2 - 2 * f t)) = 0 from by ring,
      Real.rpow_zero]
  have hrep : ((d : ℝ) ^ (-(2 - 2 * f t))) *
        (((d : ℝ) ^ (2 - 2 * f t)) * firstIncrementLagCorrelation (f t) (d : ℝ)
          - f t * (2 * f t - 1))
      = firstIncrementLagCorrelation (f t) (d : ℝ)
        - (f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))) := by
    rw [mul_sub, ← mul_assoc, hunity, one_mul]
    ring
  -- the inner decomposition
  have heps0 : (0 : ℝ) ≤ eps := le_trans (abs_nonneg _) hprof
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) hcorrB
  -- the inner decomposition
  have hinner : |actualQ1ChainWeight f r n δ t i *
          firstIncrementCrossLagCorrelation x y (d : ℝ)
        - equivalentKernel r (rieszCycleGridPoint
            (localWeightActiveSet n 1 δ t).card i)
          * ((f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))))|
      ≤ eps * B + B_omega
        * (eps + 16 * ((d : ℝ) ^ (-(2 - 2 * f t))) * ((d : ℝ)⁻¹)) := by
    have hsplit : actualQ1ChainWeight f r n δ t i *
          firstIncrementCrossLagCorrelation x y (d : ℝ)
        - equivalentKernel r (rieszCycleGridPoint
            (localWeightActiveSet n 1 δ t).card i)
          * ((f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))))
        = (actualQ1ChainWeight f r n δ t i - equivalentKernel r
            (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i))
          * firstIncrementCrossLagCorrelation x y (d : ℝ)
        + equivalentKernel r (rieszCycleGridPoint
            (localWeightActiveSet n 1 δ t).card i)
          * ((firstIncrementCrossLagCorrelation x y (d : ℝ)
              - firstIncrementLagCorrelation (f t) (d : ℝ))
            + (firstIncrementLagCorrelation (f t) (d : ℝ)
              - (f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))))) := by
      ring
    have hp1 : |(actualQ1ChainWeight f r n δ t i - equivalentKernel r
          (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i))
        * firstIncrementCrossLagCorrelation x y (d : ℝ)|
        ≤ eps * B := by
      rw [abs_mul]
      exact mul_le_mul hprof hcorrB (abs_nonneg _) heps0
    have hp2 : |equivalentKernel r (rieszCycleGridPoint
          (localWeightActiveSet n 1 δ t).card i)
        * (firstIncrementCrossLagCorrelation x y (d : ℝ)
          - firstIncrementLagCorrelation (f t) (d : ℝ))|
        ≤ B_omega * eps := by
      rw [abs_mul]
      exact mul_le_mul hωB hclass (abs_nonneg _) hω0
    have hp3 : |equivalentKernel r (rieszCycleGridPoint
          (localWeightActiveSet n 1 δ t).card i)
        * (firstIncrementLagCorrelation (f t) (d : ℝ)
          - (f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))))|
        ≤ B_omega * (16 * ((d : ℝ) ^ (-(2 - 2 * f t))) * ((d : ℝ)⁻¹)) := by
      rw [abs_mul, ← hrep, abs_mul, abs_of_nonneg hdψ0]
      have hcore : ((d : ℝ) ^ (-(2 - 2 * f t)))
          * |((d : ℝ) ^ (2 - 2 * f t))
            * firstIncrementLagCorrelation (f t) (d : ℝ)
            - f t * (2 * f t - 1)|
          ≤ ((d : ℝ) ^ (-(2 - 2 * f t))) * (16 * ((d : ℝ)⁻¹)) := by
        nlinarith [h16, hdψ0]
      have hcore' : (0 : ℝ) ≤ B_omega *
          (((d : ℝ) ^ (-(2 - 2 * f t))) * (16 * ((d : ℝ)⁻¹))
            - ((d : ℝ) ^ (-(2 - 2 * f t)))
              * |((d : ℝ) ^ (2 - 2 * f t))
                * firstIncrementLagCorrelation (f t) (d : ℝ)
                - f t * (2 * f t - 1)|) := by
        linear_combination B_omega * hcore
      have h2' : (0 : ℝ) ≤ (B_omega - |equivalentKernel r
            (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i)|)
          * (((d : ℝ) ^ (-(2 - 2 * f t)))
            * |((d : ℝ) ^ (2 - 2 * f t))
              * firstIncrementLagCorrelation (f t) (d : ℝ)
              - f t * (2 * f t - 1)|) := by
        have hzc : (0 : ℝ) ≤ ((d : ℝ) ^ (-(2 - 2 * f t)))
            * |((d : ℝ) ^ (2 - 2 * f t))
              * firstIncrementLagCorrelation (f t) (d : ℝ)
              - f t * (2 * f t - 1)| :=
          mul_nonneg hdψ0 (abs_nonneg _)
        nlinarith [hωB, hzc]
      nlinarith [hcore', h2']
    rw [hsplit]
    have htri2 : |equivalentKernel r (rieszCycleGridPoint
          (localWeightActiveSet n 1 δ t).card i)
        * ((firstIncrementCrossLagCorrelation x y (d : ℝ)
            - firstIncrementLagCorrelation (f t) (d : ℝ))
          + (firstIncrementLagCorrelation (f t) (d : ℝ)
            - (f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t)))))|
        ≤ |equivalentKernel r (rieszCycleGridPoint
            (localWeightActiveSet n 1 δ t).card i)
          * (firstIncrementCrossLagCorrelation x y (d : ℝ)
            - firstIncrementLagCorrelation (f t) (d : ℝ))|
        + |equivalentKernel r (rieszCycleGridPoint
            (localWeightActiveSet n 1 δ t).card i)
          * (firstIncrementLagCorrelation (f t) (d : ℝ)
            - (f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))))| := by
      rw [abs_mul, abs_mul, abs_mul]
      have hab2 : |firstIncrementCrossLagCorrelation x y (d : ℝ)
            - firstIncrementLagCorrelation (f t) (d : ℝ)
          + (firstIncrementLagCorrelation (f t) (d : ℝ)
            - (f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t))))|
          ≤ |firstIncrementCrossLagCorrelation x y (d : ℝ)
              - firstIncrementLagCorrelation (f t) (d : ℝ)|
            + |firstIncrementLagCorrelation (f t) (d : ℝ)
              - (f t * (2 * f t - 1)) * ((d : ℝ) ^ (-(2 - 2 * f t)))| :=
        abs_add_le _ _
      nlinarith [hab2, abs_nonneg (equivalentKernel r
        (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i))]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add (le_refl _) htri2) ?_
    linarith [hp1, hp2, hp3]
  rw [hkey, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hS.le (2 - 2 * f t - 1 : ℝ))]
  exact mul_le_mul_of_nonneg_left hinner
    (Real.rpow_nonneg hS.le (2 - 2 * f t - 1 : ℝ))

/-! ### The unconditional Riesz-side limit -/

/-- **The Riesz-side trace-power limit along the active grid
(unconditional).**  `tr(T_n ^ k)` converges to the weighted Riesz cycle
integral — the landed quadrature instance, extracted as a standalone theorem
(the `hriesz` derivation of `frozenQ1_trace_pow_tendsto_of_farBand`). -/
theorem frozenQuad_riesz_trace_pow
    (p a b M : ℝ) (r : ℕ) (_hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (_hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) := by
  set psi : ℝ := 2 - 2 * f t with hpsi
  set c : ℝ := f t * (2 * f t - 1) with hc
  have hft := hF ht
  obtain ⟨hm0, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ
    hδpos hδ0 hN
  have hcardpos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 1 (δ n) t).card := hm0
  have hmtop : Tendsto (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro N
    have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) <
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) / ((n : ℝ) * δ n) ∧
        (N : ℝ) ≤ (n : ℝ) * δ n ∧ (1 : ℝ) ≤ (n : ℝ) * δ n := by
      filter_upwards [hratio.eventually_const_lt one_lt_two,
        hN.eventually_ge_atTop (N : ℝ), hN.eventually_ge_atTop 1] with n h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨i, hi⟩ := Filter.eventually_atTop.mp hall
    refine ⟨i, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi a ha
    have hS0 : (0 : ℝ) < (a : ℝ) * δ a := by linarith
    have hle : ((a : ℝ) * δ a) ≤ (localWeightActiveSet a 1 (δ a) t).card := by
      have hfac : ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          = ((localWeightActiveSet a 1 (δ a) t).card : ℝ) / ((a : ℝ) * δ a) *
            ((a : ℝ) * δ a) :=
        (div_mul_cancel₀ ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          (ne_of_gt hS0)).symm
      rw [hfac]
      exact le_trans (by rw [one_mul])
        (le_of_lt (mul_lt_mul_of_pos_right h1 hS0))
    exact_mod_cast (h2.trans hle)
  obtain ⟨B, hB0, hB⟩ := equivalentKernel_bounded r
  have hquad := hasWeightedRieszCycleQuadrature_instance
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n : ℕ => (n : ℝ) * δ n) psi c B (equivalentKernel r) hmtop hratio
    (by filter_upwards [hN.eventually_ge_atTop 1, hcardpos] with n h hcard
        exact ⟨by linarith, hcard⟩)
    (by rw [hpsi]; linarith [hft.1, hft.2, hb])
    (by rw [hpsi]; linarith [hlong])
    (equivalentKernel_continuous r) fun z hz => hB z
  simpa only [actualQ1RieszMatrix] using
    weightedRieszDiscrete_trace_pow_tendsto
      (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      (fun n : ℕ => (n : ℝ) * δ n) psi c (equivalentKernel r) hquad k hk

/-! ### (C) The `hFquad` assembly (conditional on the far-band word input) -/

/-- **(C) The frozen quadrature `hFquad` (the last assembly of the corrected
route).**  Given the far-band word input — eventual smallness of the
trace-power difference against the Riesz quadrature matrix, the shape whose
derivation from (A) + (B2) via the word/rotation engine is the one documented
remaining step — every fixed trace power of the normalized frozen matrix
converges to the weighted Riesz cycle integral.  This is EXACTLY `hFquad` as
consumed by `Hurst.frozenHsmallMirror`, and via
`Hurst.frozenQ1_trace_pow_tendsto_of_farBand` the hypothesis `hFrozenQuad` of
`Hurst.actualQ1_trace_pow_tendsto_of_frozenPert`, closing the corrected route. -/
theorem frozenQuad_hFquad_of_farWord
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k)
    (hFarWord : ∀ eps > 0, ∀ᶠ n in atTop,
      |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| < eps) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) :=
  frozenQ1_trace_pow_tendsto_of_farBand p a b M r hp ha hb hab hM f hf hF t ht
    hlong δ hδpos hδ0 hN k hk hFarWord

end Hurst
