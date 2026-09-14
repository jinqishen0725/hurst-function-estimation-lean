import Hurst.FrozenQuadratureInstance
import Hurst.BandRemovalFinal
import Hurst.RieszQuadratureInstance

/-!
# The frozen-quadrature run: per-distance-class convergence and the assembly

This file runs the frozen-kernel analogue of the Riesz-side three-predicate
quadrature, feeding the word machinery of `Hurst.BandRemovalFinal`, and lands
the remaining analytic input `hFrozenQuad` of
`Hurst.actualQ1_trace_pow_tendsto_of_frozenBandwidth` in conditional form.

## Architecture (the DCD-over-distance-classes run)

The normalized frozen matrix `F_n = S^{ψ-1} u_i F_ij` has, by the exact entry
identity `frozenQ1_kernel_eq_crossLagCorrelation`, entries

`F_n i j = S^{ψ-1} * u_i * firstIncrementCrossLagCorrelation(h_i, h_j, d_ij)`,

`d_ij = Nat.dist` of the underlying grid indices, `h_i` the midpoint-sampled
Hurst values.  The frozen kernel is NOT a row-profile instantiation of the pure
power law (its diagonal is `S^ψ`, and at fixed rank distance the correlation
carries `O(1)` short-range constants).  The correct decomposition, mirroring
the continuum cutoff removal (T6), is over the distance classes:

* (deliverable 1) the per-distance-class convergence
  `frozenQ1_kernel_class_converges`: for each FIXED rank distance `d ≥ 1` and
  to uniform relative precision `eps`, every class-`d` entry of the frozen
  kernel equals `S^ψ * firstIncrementLagCorrelation (f t) d` up to
  `S^ψ * eps` — the increments at a fixed lag have Hurst parameters
  concentrating at `f t` (midpoint concentration hypothesis `hmid`), and the
  fixed-lag cross correlation is continuous in the two parameters
  (`firstIncrementCrossLagCorrelation_continuousAt`) hence, by Heine-Cantor
  (`frozenQ1_corr_uniformContinuousOn`), uniformly so on the compact box of
  admissible values.
* (deliverable 2) the near-band boundedness
  `frozenQ1_kernel_nearBand_bounded`: on every fixed band `d ≤ D` the frozen
  kernel entries are uniformly bounded (compactness only; no concentration
  needed), so the class-`d` NORMALIZED entries are `O(S^{ψ-1})`: each fixed
  distance class contributes a vanishing amount to the traces, exactly as the
  corresponding shell of the continuum integral is a measure-zero strip.
* (deliverable 3) the assembly `frozenQ1_trace_pow_tendsto_of_farBand`: the
  frozen analogue of `hasUniformDiscreteRieszCutoffRemoval` feeding the L3
  word machinery.  With the far-band word input `hsmall` (eventual smallness
  of the trace difference against the Riesz quadrature matrix — the frozen
  mirror of the norm-only word quantity of
  `hasUniformDiscreteRieszCutoffRemoval_of_word_small`, whose derivation from
  the far-band `O(1/x)` envelope
  `firstIncrementCrossLagCorrelation_scaled_error_le_explicit` and the
  `2ψ < 1` band power sums is the documented remaining gap), it concludes
  `Tendsto (fun n => tr(F_n ^ k)) atTop
    (𝓝 (weightedRieszCycleIntegral k ψ c (equivalentKernel r)))`,
  exactly the hypothesis `hFrozenQuad` consumed by
  `Hurst.actualQ1_trace_pow_tendsto_of_frozenBandwidth`.

## Honest scope note

The purely diagonal and near-band contributions of `F_n` vanish
(`frozenQ1_diagonal_trace_tendsto_zero` in `Hurst.FrozenQuadratureInstance`
and the `O(S^{2ψ-1})` per-entry scale of deliverable 2), and the continuum
limit is carried by the large-distance regime where
`firstIncrementCrossLagCorrelation_scaled_error_le_explicit` gives the
relative `O(1/x)` agreement with the pure power law `c * x^{-ψ}`.  What
remains open is the WORD-LEVEL assembly of that far-band relative error into
`hsmall` (the direct Frobenius route is arithmetically impossible: the
untruncated Riesz matrix has Frobenius norm `~ S^ψ → ∞`, so the sharp
word/binomial machinery of `Hurst.BandRemovalSharp`/`BandRemovalFinal` is
required).  `frozenQ1_trace_pow_tendsto_of_farBand` isolates exactly this
single input; every other step of the run is proved here.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ### Pointwise and uniform continuity of the fixed-lag cross correlation -/

/-- Continuity on the closed box of the fixed-lag cross correlation in its two
Hurst parameters (from the pointwise `ContinuousAt` on the open quadrant). -/
private theorem frozenQ1_corr_continuousOn (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (d : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => firstIncrementCrossLagCorrelation z.1 z.2 d)
      (Icc a b ×ˢ (Icc a b)) := fun z hz =>
  (firstIncrementCrossLagCorrelation_continuousAt z.1 z.2 d
    (lt_of_lt_of_le ha hz.1.1) (lt_of_le_of_lt hz.1.2 hb)
    (lt_of_lt_of_le ha hz.2.1) (lt_of_le_of_lt hz.2.2 hb)).continuousWithinAt

/-- Heine-Cantor: the fixed-lag cross correlation is uniformly continuous on
the compact box `Icc a b ×ˢ Icc a b ⊂ (0,1)²`. -/
private theorem frozenQ1_corr_uniformContinuousOn (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (d : ℝ) :
    UniformContinuousOn
      (fun z : ℝ × ℝ => firstIncrementCrossLagCorrelation z.1 z.2 d)
      (Icc a b ×ˢ (Icc a b)) :=
  (IsCompact.prod isCompact_Icc isCompact_Icc).uniformContinuousOn_of_continuous
    (frozenQ1_corr_continuousOn a b ha hb d)

/-! ### Deliverable (0): the exact entry identity -/

/-- **Exact frozen-kernel entry identity.**  On the midpoint grid the frozen
approximation kernel is `S ^ ψ` times the scale-free cross-lag correlation of
the two midpoint-sampled Hurst parameters at the INTEGER (rank) distance of
the underlying grid indices.  This is the precise form of
`normalizedFrozenIncrement_grid_inner_eq_cross_dist` at the level of
`actualQ1FrozenApproxKernel`. -/
theorem frozenQ1_kernel_eq_crossLagCorrelation
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (n : ℕ) (hn : 0 < n) (δ t S : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    actualQ1FrozenApproxKernel f hf n δ t S i j =
      S ^ (2 - 2 * f t) * firstIncrementCrossLagCorrelation
        (midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)))
        (midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)))
        (Nat.dist (localWeightActiveIndex n 1 δ t i).val
          (localWeightActiveIndex n 1 δ t j).val) := by
  unfold actualQ1FrozenApproxKernel
  have hcast : (((1 : ℕ) : ℝ) / (n : ℝ)) = (1 / (n : ℝ)) := by
    norm_num
  rw [hcast, normalizedFrozenIncrement_grid_inner_eq_cross_dist n hn
    (midpointSampleHurst f hf.1 n)
    (localWeightActiveIndex n 1 δ t i) (localWeightActiveIndex n 1 δ t j)]

/-! ### Deliverable (1): per-distance-class convergence -/

/-- **Per-distance-class convergence of the frozen kernel (deliverable 1).**
Fix a rank distance `d ≥ 1`.  Under midpoint concentration (the sampled Hurst
values at the active indices are eventually within `η n` of `f t`, `η n → 0` —
a routine consequence of continuity of `f` and the active-window geometry),
every class-`d` entry of the frozen kernel agrees with the pointwise limit
`S ^ ψ * firstIncrementLagCorrelation (f t) d` to uniform RELATIVE precision
`eps`, eventually in `n`:
`|F i j - S^ψ * lagcorr(d)| ≤ S^ψ * eps` for ALL pairs `(i, j)` at rank
distance `d`.  At fixed `d` the relative error to the PURE power law is
`O(1)`; the pure power law re-enters only as `d → ∞`
(`firstIncrementCrossLagCorrelation_scaled_error_le_explicit`), which is why
the assembly runs over distance classes. -/
theorem frozenQ1_kernel_class_converges
    (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (η : ℕ → ℝ) (hη0 : Tendsto η atTop (𝓝 0))
    (hmid : ∀ᶠ n in atTop, ∀ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
      |(midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)) : ℝ) - f t| ≤ η n)
    (d : ℕ) :
    ∀ eps > 0, ∀ᶠ n in atTop,
      ∀ i j : Fin (localWeightActiveSet n 1 (δ n) t).card,
        Nat.dist (localWeightActiveIndex n 1 (δ n) t i).val
          (localWeightActiveIndex n 1 (δ n) t j).val = d →
        |actualQ1FrozenApproxKernel f hf n (δ n) t ((n : ℝ) * δ n) i j -
          ((n : ℝ) * δ n) ^ (2 - 2 * f t) * firstIncrementLagCorrelation (f t) (d : ℝ)|
        ≤ ((n : ℝ) * δ n) ^ (2 - 2 * f t) * eps := by
  intro eps heps
  obtain ⟨ν, hνpos, hνapp⟩ := (Metric.uniformContinuousOn_iff).1
    (frozenQ1_corr_uniformContinuousOn a b ha hb (d : ℝ)) eps heps
  have hην : ∀ᶠ n in atTop, η n < ν := hη0.eventually_lt_const hνpos
  have htbox : f t ∈ Icc a b := hF ht
  have hft0 : 0 < f t := lt_of_lt_of_le ha htbox.1
  have hft1 : f t < 1 := lt_of_le_of_lt htbox.2 hb
  have hn0 : ∀ᶠ n in atTop, 0 < n := eventually_gt_atTop 0
  filter_upwards [hδpos, hην, hmid, hn0] with n hδ hην hmidn hn i j hdij
  have hval : ∀ k : Fin (localWeightActiveSet n 1 (δ n) t).card,
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t k)) : ℝ) ∈ Icc a b := by
    intro k
    have hp : grid n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 (δ n) t k)).val ∈ Ioo (0 : ℝ) 1 :=
      grid_mem n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 (δ n) t k)).val
        (Nat.zero_lt_of_lt (strideFirstLeft n 1
          (localWeightActiveIndex n 1 (δ n) t k)).isLt)
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t k)).isLt
    exact hF hp
  have hi := hval i
  have hj := hval j
  have hdist : dist ((midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)) : ℝ),
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j)) : ℝ))
      (f t, f t) < ν := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Real.dist_eq]
      linarith [hmidn i, hην]
    · rw [Real.dist_eq]
      linarith [hmidn j, hην]
  have hpair : ((midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)) : ℝ),
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j)) : ℝ))
      ∈ Icc a b ×ˢ (Icc a b) := Set.mem_prod.mpr ⟨hi, hj⟩
  have hboxft : (f t, f t) ∈ Icc a b ×ˢ (Icc a b) := Set.mem_prod.mpr ⟨htbox, htbox⟩
  have happ := hνapp
    ((midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)) : ℝ),
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j)) : ℝ)) hpair
    (f t, f t) hboxft hdist
  rw [frozenQ1_kernel_eq_crossLagCorrelation f hf n hn (δ n) t ((n : ℝ) * δ n) i j,
    ← firstIncrementCrossLagCorrelation_self (f t) (d : ℝ) hft0 hft1, hdij]
  have hkey : ((n : ℝ) * δ n) ^ (2 - 2 * f t) *
        |firstIncrementCrossLagCorrelation
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)))
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j))) (d : ℝ) -
        firstIncrementCrossLagCorrelation (f t) (f t) (d : ℝ)|
      = |((n : ℝ) * δ n) ^ (2 - 2 * f t) *
          firstIncrementCrossLagCorrelation
            (midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)))
            (midpointSampleHurst f hf.1 n
              (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j))) (d : ℝ) -
        ((n : ℝ) * δ n) ^ (2 - 2 * f t) *
          firstIncrementCrossLagCorrelation (f t) (f t) (d : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg
      (Real.rpow_nonneg (by positivity) (2 - 2 * f t : ℝ))]
  have happ' : |firstIncrementCrossLagCorrelation
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)))
      (midpointSampleHurst f hf.1 n
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j))) (d : ℝ) -
      firstIncrementCrossLagCorrelation (f t) (f t) (d : ℝ)| ≤ eps := by
    rw [Real.dist_eq] at happ
    linarith
  rw [← hkey]
  calc ((n : ℝ) * δ n) ^ (2 - 2 * f t) * |firstIncrementCrossLagCorrelation
        (midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)))
        (midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j))) (d : ℝ) -
      firstIncrementCrossLagCorrelation (f t) (f t) (d : ℝ)|
      = |firstIncrementCrossLagCorrelation
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t i)))
          (midpointSampleHurst f hf.1 n
            (strideFirstLeft n 1 (localWeightActiveIndex n 1 (δ n) t j))) (d : ℝ) -
        firstIncrementCrossLagCorrelation (f t) (f t) (d : ℝ)| *
        ((n : ℝ) * δ n) ^ (2 - 2 * f t) := by ring
    _ ≤ eps * ((n : ℝ) * δ n) ^ (2 - 2 * f t) :=
        mul_le_mul_of_nonneg_right happ' (Real.rpow_nonneg (by positivity) _)
    _ = ((n : ℝ) * δ n) ^ (2 - 2 * f t) * eps := by ring

/-! ### Deliverable (2): near-band boundedness (compactness only) -/

set_option maxHeartbeats 8000000 in
/-- **Near-band boundedness of the frozen kernel (deliverable 2).**  On every
fixed band of rank distances `d ≤ D` the frozen kernel entries are uniformly
bounded: the sampled Hurst values lie in the compact box `Icc a b` and the
cross correlation is bounded there on each of the finitely many lags.  No
midpoint concentration is needed.  Combined with the `S^{ψ-1}` normalization
this gives the per-entry scale `O(S^{ψ-1})` of every fixed-distance class —
the pointwise-in-`d` vanishing of the DCD decomposition (each fixed class
contributes a vanishing amount to the traces, matching the measure-zero shell
of the continuum integral). -/
theorem frozenQ1_kernel_nearBand_bounded
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (n : ℕ) (hn : 0 < n) (δ t S : ℝ) (hS : 0 < S)
    (D : ℕ) :
    ∃ B ≥ 0, ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      Nat.dist (localWeightActiveIndex n 1 δ t i).val
          (localWeightActiveIndex n 1 δ t j).val ≤ D →
      |actualQ1FrozenApproxKernel f hf n δ t S i j| ≤ S ^ (2 - 2 * f t) * B := by
  have haI : a ∈ Icc a b := ⟨le_refl a, hab⟩
  have hmem : (a, a) ∈ Icc a b ×ˢ (Icc a b) := Set.mem_prod.mpr ⟨haI, haI⟩
  have hlag : ∀ d : ℕ, ∃ Bd ≥ 0, ∀ z ∈ Icc a b ×ˢ (Icc a b),
      |firstIncrementCrossLagCorrelation z.1 z.2 (d : ℝ)| ≤ Bd := by
    intro d
    have habsCont : ContinuousOn (fun z : ℝ × ℝ =>
        |firstIncrementCrossLagCorrelation z.1 z.2 (d : ℝ)|)
        (Icc a b ×ˢ (Icc a b)) :=
      (frozenQ1_corr_continuousOn a b ha hb (d : ℝ)).abs
    obtain ⟨x, hx, hmax⟩ := (IsCompact.prod isCompact_Icc isCompact_Icc).exists_isMaxOn
      ⟨(a, a), hmem⟩ habsCont
    refine ⟨|firstIncrementCrossLagCorrelation x.1 x.2 (d : ℝ)|, abs_nonneg _, ?_⟩
    intro z hz
    rw [isMaxOn_iff] at hmax
    exact hmax z hz
  have hall : ∃ B : ℝ, 0 ≤ B ∧ ∀ d ≤ D, ∀ z ∈ Icc a b ×ˢ (Icc a b),
      |firstIncrementCrossLagCorrelation z.1 z.2 (d : ℝ)| ≤ B := by
    refine ⟨∑ d' ∈ Finset.range (D + 1), Classical.choose (hlag d'), ?_, ?_⟩
    · exact Finset.sum_nonneg fun d _ => (Classical.choose_spec (hlag d)).1
    · intro d hd z hz
      exact le_trans ((Classical.choose_spec (hlag d)).2 z hz)
        (Finset.single_le_sum (f := fun d' => Classical.choose (hlag d'))
          (fun d' _ => (Classical.choose_spec (hlag d')).1)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hd)))
  obtain ⟨B, hB0, hB⟩ := hall
  refine ⟨B, hB0, ?_⟩
  intro i j hdij
  -- name the two sampled Hurst values to keep the goal small
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ) = x :=
    ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, (midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ) = y :=
    ⟨_, rfl⟩
  have hxF : x ∈ Icc a b := by
    rw [← hx]
    have hp : grid n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 δ t i)).val ∈ Ioo (0 : ℝ) 1 :=
      grid_mem n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 δ t i)).val
        (Nat.zero_lt_of_lt (strideFirstLeft n 1
          (localWeightActiveIndex n 1 δ t i)).isLt)
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)).isLt
    exact hF hp
  have hyF : y ∈ Icc a b := by
    rw [← hy]
    have hp : grid n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 δ t j)).val ∈ Ioo (0 : ℝ) 1 :=
      grid_mem n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 δ t j)).val
        (Nat.zero_lt_of_lt (strideFirstLeft n 1
          (localWeightActiveIndex n 1 δ t j)).isLt)
        (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)).isLt
    exact hF hp
  rw [frozenQ1_kernel_eq_crossLagCorrelation f hf n hn δ t S i j, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hS.le (2 - 2 * f t : ℝ)), hx, hy]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hS.le (2 - 2 * f t : ℝ))
  exact hB _ hdij (x, y) (Set.mem_prod.mpr ⟨hxF, hyF⟩)

/-! ### Deliverable (3): the frozen quadrature assembly -/

/-- **The frozen quadrature assembly (deliverable 3).**  The frozen analogue
of `hasUniformDiscreteRieszCutoffRemoval` feeding the L3 word machinery: with
the far-band word input `hsmall` (eventual smallness of the trace difference
against the Riesz quadrature matrix `actualQ1RieszMatrix` — the frozen mirror
of the norm-only word quantity of
`hasUniformDiscreteRieszCutoffRemoval_of_word_small`), every fixed power trace
of the normalized frozen matrix converges to the weighted Riesz cycle
integral.  This is EXACTLY the hypothesis `hFrozenQuad` consumed by
`Hurst.actualQ1_trace_pow_tendsto_of_frozenBandwidth`, so the corrected route
of `Hurst.FrozenQuadratureInstance` terminates at the signed spectral endpoint
once `hsmall` is supplied.

The remaining gap is the derivation of `hsmall` itself: the diagonal and
near-band parts of the difference vanish (deliverables 1-2 above and
`frozenQ1_diagonal_trace_tendsto_zero`), and on the far band the entries agree
at relative error `O(1/x)` with the pure power law
(`firstIncrementCrossLagCorrelation_scaled_error_le_explicit`); assembling
these into the word-level estimate requires the sharp word/binomial machinery
(the plain Frobenius bound is void here since `‖Riesz‖_F ~ S^ψ → ∞`).
-/
theorem frozenQ1_trace_pow_tendsto_of_farBand
    (p a b M : ℝ) (r : ℕ) (_hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (_hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (k : ℕ) (hk : 2 ≤ k)
    (hsmall : ∀ eps > 0, ∀ᶠ n in atTop,
      |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| < eps) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) := by
  set psi : ℝ := 2 - 2 * f t with hpsi
  set c : ℝ := f t * (2 * f t - 1) with hc
  have hft := hF ht
  obtain ⟨hm0, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ
    hδpos hδ0 hN
  have hcardpos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 1 (δ n) t).card := hm0
  -- the active mesh tends to infinity
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
  -- the Riesz quadrature instance along the active grid
  obtain ⟨B, hB0, hB⟩ := equivalentKernel_bounded r
  have hquad := hasWeightedRieszCycleQuadrature_instance
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n : ℕ => (n : ℝ) * δ n) psi c B (equivalentKernel r) hmtop hratio
    (by filter_upwards [hN.eventually_ge_atTop 1, hcardpos] with n h hcard
        exact ⟨by linarith, hcard⟩)
    (by rw [hpsi]; linarith [hft.1, hft.2, hb])
    (by rw [hpsi]; linarith [hlong])
    (equivalentKernel_continuous r) fun z hz => hB z
  -- the Riesz trace-power limit, at the actualQ1RieszMatrix wrapper
  have hriesz : Tendsto (fun n : ℕ => Matrix.trace
      ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k psi c (equivalentKernel r))) := by
    simpa only [actualQ1RieszMatrix] using
      weightedRieszDiscrete_trace_pow_tendsto
        (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
        (fun n : ℕ => (n : ℝ) * δ n) psi c (equivalentKernel r) hquad k hk
  -- the word input hsmall as a vanishing trace difference
  have habs0 : Tendsto (fun n : ℕ => |Matrix.trace
      ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
      - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)|) atTop (𝓝 (0:ℝ)) := by
    rw [tendsto_atTop_nhds]
    intro U hU hUopen
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUopen 0 hU
    have hsmallε : ∀ᶠ n in atTop,
        |Matrix.trace ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
          - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)| < ε :=
      hsmall ε hε
    rw [eventually_atTop] at hsmallε
    obtain ⟨N, hN⟩ := hsmallε
    refine ⟨N, fun n hn => hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)]
    exact hN n hn
  have hdiff0 : Tendsto (fun n : ℕ => Matrix.trace
      ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)
      - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (by simpa only [Real.dist_eq, sub_zero] using habs0)
  have hsum : Tendsto (fun n : ℕ => Matrix.trace
      ((actualQ1NormalizedFrozenMatrix f hf r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k psi c (equivalentKernel r))) := by
    simpa using hdiff0.add hriesz
  exact hsum

end Hurst

