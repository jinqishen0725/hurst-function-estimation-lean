import Hurst.P5L1Joining
import Hurst.VaryingIncrement
import Hurst.FirstStrideGrid
import Hurst.HolderTaylor
import Hurst.ActiveSetReindex
import Hurst.E5ChainInstantiation

/-!
# E5 bias expansion, block 1 (hBias milestone, second-agent parallel work)

This file is the first formal block of the E5 drift-side (bias) expansion for the
known-scale H estimator `p5KnownScaleEstimator = p5Trunc01 ∘ p5KnownScaleHtilde`
of the q1 chain.  It contains four independently stated pieces that the
assembly blueprint of the hBias milestone consumes:

* `truncExpectation_le_fluctuation` — the abstract truncation-expectation
  lemma `|E p5Trunc01(X) - E X| ≤ E|X - E X|` (valid whenever `E X ∈ [0, 1]`),
  via the 1-Lipschitz property of `p5Trunc01` and the clip geometry.
* `varyingIncrement_norm_sq_error` / `varyingIncrement_logNormSq_error` /
  `gridStrideFirstActual_logNormSq_error` — the increment-norm log expansion:
  `‖varying increment‖² = 1 + ε` with the parameter-Lipschitz rate
  `|ε| ≤ 3·C·K·ℓ^(1-b)`, and the per-row log deviation
  `|log ‖gridStrideFirstActual n 1 H i‖²| ≤ C'·n^{-(1-b)}` under the
  Hölder-Lipschitz control of the sampled Hurst profile.
* `holderWeightContraction` / `exists_holderWeightContraction_localPolynomialWeights`
  — the Hölder weight contraction `|∑ w_j f(x_j) - f t| ≤ M'·δ^p` under the
  explicit unit-sum premise `hsum`, the moment-annihilation premises and the
  active-window geometry; the second theorem discharges the premises for the
  actual local-polynomial weights via `localPolynomialWeights_uniform_stability`.
* The drift-side identity `p5KnownScaleHtilde_expectation_eq` and the per-point
  bias envelope `knownScaleEstimator_bias_envelope`, assembled from the three
  pieces above (truncation + per-row log deviation + weight contraction).

## Honest rate registration (deviation from the sketched blueprint)

The sketched blueprint predicted the per-row log deviation at rate
`C·n^{-(2-b)}`.  That arithmetic is NOT correct for the landed machinery:
`normalizedVaryingIncrement_uniform_remainder` (VaryingIncrement.lean:29) has
the premise `|k - h| ≤ B * ℓ`, so a Hölder-Lipschitz profile difference
`|k - h| = O(ℓ)` forces `B = O(1)`, and the conclusion is
`C·B·ℓ^(1-b) = O(ℓ^{1-b}) = O(n^{-(1-b)})`, not `O(n^{-(2-b)})`.  The theorems
below therefore carry the honest rate `n^{-(1-b)}`.

Consequence for the endpoint: with the honest rate, the drift-side ε-term
contributes `W·C'·n^{-(1-b)}/(2·log n)`, which fits the endpoint budget
`C·n^{-γ}` exactly when `γ ≤ 1 - b` — and `γ = f t` with the long-memory band
`f t > 3/4` violates `γ ≤ 1 - b` whenever `b > f t` (both hold in the feasible
endpoint, where `b` is the UPPER Hurst-band end and `f t ∈ (a, b)`).  The
conditional envelope `knownScaleEstimator_bias_envelope_grid` is therefore
stated under the honest window `γ ≤ 1 - b` with the center calibration forced
to `cσ = gaussianLogSquareMean` (any constant offset `cσ - c₀ ≠ 0` decays only
like `1/log n`, slower than every polynomial rate).  This is a REAL rate gap,
not a missing mechanical step; it is registered in the handover report and
must not be papered over by weakening the endpoint's `hBias` definition.

## Boundaries

Second-agent parallel file: every `∑ w = 1`-style fact that the mainline agent
is producing is kept as an explicit premise (`hw1`, `hwt`, `hwc`) in the
modular statements; only the final grid corollary discharges them internally
from already-landed repo lemmas (`localPolynomialWeights_uniform_stability`).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology

namespace Hurst

/-! ## Part 0: an elementary log sublemma (hand-proved, no simp abuse) -/

/-- `|log(1+x)| ≤ 2|x|` on `|x| ≤ 1/2`: the log-amplification sublemma of the
increment-norm expansion. -/
theorem abs_log_one_add_le_two_mul {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x)| ≤ 2 * |x| := by
  rcases le_total 0 x with h0 | h0
  · have h1 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
    have h2 : Real.log (1 + x) ≤ x := by
      have h3 := Real.log_le_sub_one_of_pos (x := 1 + x) (by linarith)
      linarith
    rw [abs_of_nonneg h1, abs_of_nonneg h0]
    linarith
  · have hx2 : -(1 / 2) ≤ x := by
      have := (abs_le.mp hx).1
      linarith
    have hpos : 0 < 1 + x := by linarith
    have hneg : Real.log (1 + x) ≤ 0 := (Real.log_nonpos_iff (by linarith)).mpr (by linarith)
    have hinv : 0 < 1 / (1 + x) := by positivity
    have hupper := Real.log_le_sub_one_of_pos hinv
    have hloginv : Real.log (1 / (1 + x)) = -Real.log (1 + x) := by
      rw [one_div, Real.log_inv]
    rw [hloginv] at hupper
    have hstep : 1 / (1 + x) - 1 ≤ -2 * x := by
      have hrewrite : 1 / (1 + x) - 1 = -x / (1 + x) := by field_simp; ring
      have hdiv : -x / (1 + x) ≤ -2 * x := by
        rw [div_le_iff₀ hpos]
        have h2 : 0 ≤ 1 + 2 * x := by linarith
        have h3 : 0 ≤ -x := by linarith
        have h4 := mul_nonneg h3 h2
        nlinarith
      rw [hrewrite]
      exact hdiv
    rw [abs_of_nonpos hneg]
    calc -Real.log (1 + x) ≤ 1 / (1 + x) - 1 := by linarith
      _ ≤ -2 * x := hstep
      _ = 2 * |x| := by rw [abs_of_nonpos h0]; ring

/-! ## Part A: the truncation-expectation lemma (fully abstract) -/

/-- **The truncation-expectation lemma.**  For a real integrable `X` on a
probability space with `E X ∈ [0, 1]`, clipping through `p5Trunc01` moves the
mean by at most the mean absolute fluctuation:

`|E p5Trunc01(X) - E X| ≤ E|X - E X|`.

Pointwise: `|p5Trunc01 x - x|` is the distance of `x` to the clip value, which
is at most the distance of `x` to any point `c` of the clip range `[0, 1]`
(here `c = E X`); equivalently it follows from the 1-Lipschitz property of
`p5Trunc01` applied to the pair `(x, c)` together with `p5Trunc01_eq_self c`,
plus the clip geometry outside `[0, 1]`. -/
theorem truncExpectation_le_fluctuation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable X μ) (hX : Integrable X μ)
    (hc : (∫ x, X x ∂μ) ∈ Icc 0 1) :
    |∫ ω, p5Trunc01 (X ω) ∂μ - ∫ ω, X ω ∂μ| ≤ ∫ ω, |X ω - ∫ y, X y ∂μ| ∂μ := by
  set c : ℝ := ∫ y, X y ∂μ with hcdef
  have hbound : ∀ ω, |p5Trunc01 (X ω) - X ω| ≤ |X ω - c| := by
    intro ω
    rcases lt_trichotomy (X ω) 0 with hx | hx | hx
    · rw [p5Trunc01_eq_zero (le_of_lt hx),
        abs_of_pos (show (0 : ℝ) < 0 - X ω by linarith),
        abs_of_neg (show X ω - c < 0 by linarith [hc.1])]
      linarith [hc.1]
    · rw [hx, p5Trunc01_eq_zero (le_refl 0), sub_self, abs_zero]
      exact abs_nonneg _
    · rcases lt_trichotomy (X ω) 1 with h1 | h1 | h1
      · rw [p5Trunc01_eq_self ⟨le_of_lt hx, le_of_lt h1⟩, sub_self, abs_zero]
        exact abs_nonneg _
      · rw [h1, p5Trunc01_eq_one (le_refl 1), sub_self, abs_zero]
        exact abs_nonneg _
      · rw [p5Trunc01_eq_one (le_of_lt h1),
          abs_of_neg (show (1 : ℝ) - X ω < 0 by linarith),
          abs_of_pos (show (0 : ℝ) < X ω - c by linarith [hc.2])]
        linarith [hc.2]
  have hdmeas : AEStronglyMeasurable (fun ω => p5Trunc01 (X ω)) μ :=
    Continuous.comp_aestronglyMeasurable p5Trunc01_continuous hXm
  have hb1 : ∀ ω, |p5Trunc01 (X ω)| ≤ 1 := by
    intro ω
    have hmem := p5Trunc01_mem_Icc (X ω)
    exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
  have htrunc : Integrable (fun ω => p5Trunc01 (X ω)) μ :=
    ((MemLp.of_bound (p := 2) hdmeas 1
      (Filter.Eventually.of_forall fun ω => hb1 ω))).integrable one_le_two
  have hdiff : Integrable (fun ω => p5Trunc01 (X ω) - X ω) μ := htrunc.sub hX
  have hXc : Integrable (fun ω => X ω - c) μ := hX.sub (integrable_const c)
  have hdom : Integrable (fun ω => |X ω - c|) μ := hXc.abs
  calc |∫ ω, p5Trunc01 (X ω) ∂μ - ∫ ω, X ω ∂μ|
      = |∫ ω, (p5Trunc01 (X ω) - X ω) ∂μ| := by
        rw [← integral_sub htrunc hX]
      _ ≤ ∫ ω, |p5Trunc01 (X ω) - X ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |X ω - c| ∂μ :=
          integral_mono hdiff.abs hdom (fun ω => hbound ω)

/-! ## Part B: the increment-norm log expansion (Harmonizable side) -/

/-- **First-order increment-norm expansion.**  If the varying parameter stays
within one stride of the frozen one, `|k - h| ≤ K·ℓ`, then the squared norm of
the normalized varying increment differs from `1` (the frozen value) by at
most `3·C·K·ℓ^(1-b)`, where `C` is the uniform parameter-Lipschitz constant of
the harmonizable features on the band `[a, b]`. -/
theorem varyingIncrement_norm_sq_error (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s ℓ K : ℝ, |s + ℓ| ≤ 1 → 0 < ℓ → ℓ ≤ 1 → 0 ≤ K → |(k : ℝ) - h| ≤ K * ℓ →
        C * K * ℓ ^ (1 - b) ≤ 1 →
        |‖normalizedVaryingIncrement h k s ℓ‖ ^ 2 - 1| ≤ 3 * C * K * ℓ ^ (1 - b) := by
  obtain ⟨C, hC, hrem⟩ := normalizedVaryingIncrement_uniform_remainder a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k hh hk s ℓ K hs hℓ hℓ1 hK hkK hsmall
  have hε0 : 0 ≤ C * K * ℓ ^ (1 - b) := by
    refine mul_nonneg (mul_nonneg hC hK) ?_
    exact Real.rpow_nonneg hℓ.le _
  have hε : ‖normalizedVaryingIncrement h k s ℓ - normalizedFrozenIncrement h s ℓ‖
      ≤ C * K * ℓ ^ (1 - b) :=
    hrem h k hh hk s ℓ K hs hℓ hℓ1 hK hkK
  have h1 : ‖normalizedFrozenIncrement h s ℓ‖ = 1 :=
    normalizedFrozenIncrement_norm h s ℓ hℓ
  have herr := norm_square_error_from_unit
    (normalizedFrozenIncrement h s ℓ) (normalizedVaryingIncrement h k s ℓ)
    (C * K * ℓ ^ (1 - b)) hε0 h1 hε
  have h3 : (C * K * ℓ ^ (1 - b)) * (2 + C * K * ℓ ^ (1 - b))
      ≤ 3 * C * K * ℓ ^ (1 - b) := by
    have hε1 : (C * K * ℓ ^ (1 - b)) * (C * K * ℓ ^ (1 - b))
        ≤ C * K * ℓ ^ (1 - b) := by
      have hmul := mul_le_mul_of_nonneg_left hsmall hε0
      rwa [mul_one] at hmul
    nlinarith
  linarith

/-- **Log version of the increment-norm expansion.**  Under the same premises
with the stronger smallness `C·K·ℓ^(1-b) ≤ 1/2`, the log of the squared norm
of the varying increment is `O(C·K·ℓ^(1-b))`. -/
theorem varyingIncrement_logNormSq_error (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s ℓ K : ℝ, |s + ℓ| ≤ 1 → 0 < ℓ → ℓ ≤ 1 → 0 ≤ K → |(k : ℝ) - h| ≤ K * ℓ →
        C * K * ℓ ^ (1 - b) ≤ 1 / 2 →
        |Real.log (‖normalizedVaryingIncrement h k s ℓ‖ ^ 2)| ≤ 10 * C * K * ℓ ^ (1 - b) := by
  obtain ⟨C, hC, hrem⟩ := normalizedVaryingIncrement_uniform_remainder a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k hh hk s ℓ K hs hℓ hℓ1 hK hkK hsmall
  have hε0 : 0 ≤ C * K * ℓ ^ (1 - b) := by
    refine mul_nonneg (mul_nonneg hC hK) ?_
    exact Real.rpow_nonneg hℓ.le _
  have hε : ‖normalizedVaryingIncrement h k s ℓ - normalizedFrozenIncrement h s ℓ‖
      ≤ C * K * ℓ ^ (1 - b) :=
    hrem h k hh hk s ℓ K hs hℓ hℓ1 hK hkK
  have h1 : ‖normalizedFrozenIncrement h s ℓ‖ = 1 :=
    normalizedFrozenIncrement_norm h s ℓ hℓ
  simpa only [mul_assoc] using log_norm_square_error_from_unit
    (normalizedFrozenIncrement h s ℓ) (normalizedVaryingIncrement h k s ℓ)
    (C * K * ℓ ^ (1 - b)) hε0 h1 hε hsmall

/-- **The per-row log deviation of the actual first-stride statistic.**  For a
Hölder Hurst profile sampled at the midpoints (`midpointSampleHurst`), the
log of the squared norm of every first-stride varying increment deviates from
`0` (the frozen value) by at most `C'·n^{-(1-b)}` once `C'·n^{-(1-b)} ≤ 1/2`.
The constant is `10·D·(1+M)` with `D` the universal Hölder-Lipschitz constant
(`hurstHolder_uniform_lower_derivative_lipschitz`) and `M` the Hölder constant
of the profile.

Honest-rate note: this is the `n^{-(1-b)}` shape forced by the premise
`|k - h| ≤ B·ℓ` of `normalizedVaryingIncrement_uniform_remainder`; the
sketched `n^{-(2-b)}` would require `|k - h| = O(ℓ²)`, which the Hölder
class does not provide. -/
theorem gridStrideFirstActual_logNormSq_error (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C' ≥ 0, ∀ n : ℕ, 0 < n → ∀ (f : ℝ → ℝ) (hfM : f ∈ hurstHolderClass p M),
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ i : Fin (n - 1),
      C' * (n : ℝ) ^ (-(1 - b)) ≤ 1 / 2 →
      |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hfM.1 n) i‖ ^ 2)|
        ≤ C' * (n : ℝ) ^ (-(1 - b)) := by
  obtain ⟨C, hC, hlogerr⟩ := varyingIncrement_logNormSq_error a b ha hb hab
  obtain ⟨D, hD, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  refine ⟨10 * C * (D * (1 + M)), by positivity, ?_⟩
  intro n hn f hfclass hF i hsmall
  have hstride : gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i
      = normalizedVaryingIncrement
          (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i))
          (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i))
          (grid n i.val) (1 / n) := by
    simp only [gridStrideFirstActual, Nat.cast_one]
  -- the parameter difference is at most D·(1+M) per stride
  have hmemL : grid n (strideFirstLeft n 1 i).val ∈ Ioo (0 : ℝ) 1 :=
    grid_mem n (strideFirstLeft n 1 i).val hn (strideFirstLeft n 1 i).isLt
  have hmemR : grid n (strideFirstRight n 1 i).val ∈ Ioo (0 : ℝ) 1 :=
    grid_mem n (strideFirstRight n 1 i).val hn (strideFirstRight n 1 i).isLt
  have hstep : grid n (strideFirstRight n 1 i).val
      = grid n i.val + (1 : ℝ) / n := by
    rw [grid_stride_first_step n 1 i, Nat.cast_one]
  have hL : grid n (strideFirstLeft n 1 i).val = grid n i.val := rfl
  have hℓpos : (0 : ℝ) < 1 / n := by positivity
  have hfloorpos : (0 : ℕ) < Nat.floor p := by
    have hmono := Nat.floor_mono (a := (1 : ℝ)) hp
    have h1le : (1 : ℕ) ≤ Nat.floor p := by simpa using hmono
    omega
  have hdiffParam : |(midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i) : ℝ)
        - (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i) : ℝ)|
      ≤ (D * (1 + M)) * (1 / n) := by
    have hlip := hLip M hM f hfclass 0 hfloorpos
      (grid n (strideFirstLeft n 1 i).val) hmemL
      (grid n (strideFirstRight n 1 i).val) hmemR
    have hdist : |grid n (strideFirstRight n 1 i).val
        - grid n (strideFirstLeft n 1 i).val| = (1 : ℝ) / n := by
      rw [hstep, hL, add_sub_cancel_left, abs_of_pos hℓpos]
    rw [hdist] at hlip
    have hrw : (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i) : ℝ)
        - (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i) : ℝ)
        = f (grid n (strideFirstRight n 1 i).val)
          - f (grid n (strideFirstLeft n 1 i).val) := rfl
    rw [hrw]
    simpa only [iteratedDeriv_zero] using hlip
  -- all the uniform_remainder side conditions at ℓ = 1/n, K = D·(1+M)
  have hℓ1 : (1 : ℝ) / n ≤ 1 := by
    have hR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_one hR).mpr (by exact_mod_cast hn)
  have hs : |grid n i.val + 1 / n| ≤ 1 := by
    rw [← hstep, abs_of_pos hmemR.1]
    exact le_of_lt hmemR.2
  have hK0 : 0 ≤ D * (1 + M) := by positivity
  have hbandL : (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i) : ℝ) ∈ Icc a b :=
    hF hmemL
  have hbandR : (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i) : ℝ) ∈ Icc a b :=
    hF hmemR
  have hrpow : (1 / n : ℝ) ^ (1 - b) = (n : ℝ) ^ (-(1 - b)) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul
      (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)]
    congr 1
    ring
  have hsmall' : C * (D * (1 + M)) * (1 / n) ^ (1 - b) ≤ 1 / 2 := by
    rw [hrpow]
    calc C * (D * (1 + M)) * (n : ℝ) ^ (-(1 - b))
        = (10 * C * (D * (1 + M)) * (n : ℝ) ^ (-(1 - b))) / 10 := by ring
      _ ≤ (1 / 2 : ℝ) / 10 := by
          exact div_le_div_of_nonneg_right hsmall (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have herr := hlogerr
    (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i))
    (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i))
    hbandL hbandR (grid n i.val) (1 / n) (D * (1 + M)) hs hℓpos hℓ1 hK0 hdiffParam hsmall'
  rw [hrpow] at herr
  rw [hstride]
  exact herr

/-! ## Part C: the Hölder weight contraction (weight side) -/

/-- **The Hölder weight contraction (abstract form).**  If the weights sum to
one, annihilate the monomials `(x_j - t)^k` for `1 ≤ k ≤ ⌊p⌋` (the order-`r ≥
⌊p⌋` local-polynomial moment conditions), have bounded total variation
`∑ |w_j| ≤ W`, and every sample point `x_j` sits within `δ` of `t`, then for
`f` in the Hölder class `hurstHolderClass p M`:

`|∑ w_j f(x_j) - f t| ≤ (W · M / ⌊p⌋!) · δ^p`.

The premises `hsum`/`hmom` are kept EXPLICIT (mainline-owned middleware);
`holderWeightContraction_localPolynomialWeights_of_stable` discharges them for
the actual local-polynomial weights. -/
theorem holderWeightContraction (p M W δ t : ℝ) (hp : 1 ≤ p) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (x : κ → ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hx : ∀ j, x j ∈ Ioo (0 : ℝ) 1)
    (hsum : ∑ j, w j = 1)
    (hmom : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.floor p → ∑ j, w j * (x j - t) ^ k = 0)
    (hW : ∑ j, |w j| ≤ W)
    (hgeo : ∀ j, |x j - t| ≤ δ) (hδ : 0 ≤ δ) :
    |∑ j, w j * f (x j) - f t| ≤ (W * M / ((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p := by
  classical
  have hm1 : (1 : ℕ) ≤ Nat.floor p := by
    have hmono := Nat.floor_mono (a := (1 : ℝ)) hp
    simpa using hmono
  have hpowE : ((Nat.floor p : ℕ) : ℝ) + (p - ((Nat.floor p : ℕ) : ℝ)) = p := by
    ring
  -- Taylor remainder with the Hölder-class data at every sample point
  have hR : ∀ j : κ, |f (x j) - taylorJet (Nat.floor p) f t (x j)|
      ≤ M / (((Nat.floor p).factorial : ℕ) : ℝ) * |x j - t| ^ p := by
    intro j
    have hfdiff : ∀ k ≤ Nat.floor p - 1, ∀ z ∈ Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (iteratedDeriv k f) z := by
      intro k hk z hz
      exact hf.2.1 k (by omega) z hz
    have hmp : ((Nat.floor p : ℕ) : ℝ) ≤ p := Nat.floor_le (by linarith)
    have hβ : 0 ≤ p - ((Nat.floor p : ℕ) : ℝ) := by linarith
    have hholder : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
        |iteratedDeriv (Nat.floor p - 1 + 1) f x - iteratedDeriv (Nat.floor p - 1 + 1) f y|
          ≤ M * |x - y| ^ (p - ((Nat.floor p : ℕ) : ℝ)) := by
      intro x hx y hy
      simpa only [Nat.sub_add_cancel hm1] using hf.2.2 x hx y hy
    have hT := holder_taylor_remainder f (Nat.floor p - 1) M (p - ((Nat.floor p : ℕ) : ℝ))
      hM hβ hfdiff hholder t (x j) ht (hx j)
    rw [show (Nat.floor p - 1 + 1 : ℕ) = Nat.floor p from Nat.sub_add_cancel hm1] at hT
    rwa [hpowE] at hT
  -- the Taylor polynomial part annihilates against the weights
  have hTay : ∑ j, w j * taylorJet (Nat.floor p) f t (x j) = f t := by
    have hstep1 : ∀ j : κ, w j * taylorJet (Nat.floor p) f t (x j)
        = ∑ k : Fin (Nat.floor p + 1), w j *
            (iteratedDeriv k.val f t * (x j - t) ^ k.val / ((k.val.factorial : ℕ) : ℝ)) := by
      intro j
      simp only [taylorJet]
      exact Finset.mul_sum _ _ _
    calc ∑ j, w j * taylorJet (Nat.floor p) f t (x j)
        = ∑ k : Fin (Nat.floor p + 1),
            (iteratedDeriv k.val f t / ((k.val.factorial : ℕ) : ℝ))
              * ∑ j, w j * (x j - t) ^ k.val := by
          rw [Finset.sum_congr rfl (fun j _ => hstep1 j), Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hr : ∀ j : κ,
              w j * (iteratedDeriv k.val f t * (x j - t) ^ k.val / ((k.val.factorial : ℕ) : ℝ))
              = (iteratedDeriv k.val f t / ((k.val.factorial : ℕ) : ℝ))
                  * (w j * (x j - t) ^ k.val) := fun j => by ring
          rw [Finset.sum_congr rfl (fun j _ => hr j), ← Finset.mul_sum]
      _ = (iteratedDeriv (0 : Fin (Nat.floor p + 1)).val f t
              / (((0 : Fin (Nat.floor p + 1)).val.factorial : ℕ) : ℝ))
            * ∑ j, w j * (x j - t) ^ (0 : Fin (Nat.floor p + 1)).val
          + ∑ k : Fin (Nat.floor p),
              (iteratedDeriv (Fin.succ k).val f t / (((Fin.succ k).val.factorial : ℕ) : ℝ))
                * ∑ j, w j * (x j - t) ^ (Fin.succ k).val := by
          simp only [Fin.sum_univ_succ]
      _ = f t := by
          have hS : ∀ k : Fin (Nat.floor p),
              ∑ j, w j * (x j - t) ^ (Fin.succ k).val = 0 := by
            intro k
            rw [Fin.val_succ]
            exact hmom (k.val + 1) (by omega) (by have := k.isLt; omega)
          have hz : ∑ k : Fin (Nat.floor p),
              (iteratedDeriv (Fin.succ k).val f t / (((Fin.succ k).val.factorial : ℕ) : ℝ))
                * ∑ j, w j * (x j - t) ^ (Fin.succ k).val = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [hS k, mul_zero]
          rw [hz, add_zero]
          simp [hsum, iteratedDeriv_zero, Nat.factorial_zero]
  -- assemble: the weighted average minus f t is the weighted remainder
  calc |∑ j, w j * f (x j) - f t|
      = |∑ j, w j * (f (x j) - taylorJet (Nat.floor p) f t (x j))| := by
        have hsplit : ∑ j, w j * f (x j)
            = ∑ j, w j * (f (x j) - taylorJet (Nat.floor p) f t (x j))
              + ∑ j, w j * taylorJet (Nat.floor p) f t (x j) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hsplit, hTay, add_sub_cancel_right]
      _ ≤ ∑ j, |w j * (f (x j) - taylorJet (Nat.floor p) f t (x j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |w j| * (M / (((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p) := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc |w j * (f (x j) - taylorJet (Nat.floor p) f t (x j))|
              = |w j| * |f (x j) - taylorJet (Nat.floor p) f t (x j)| := abs_mul _ _
            _ ≤ |w j| * (M / (((Nat.floor p).factorial : ℕ) : ℝ) * |x j - t| ^ p) :=
                mul_le_mul_of_nonneg_left (hR j) (abs_nonneg _)
            _ ≤ |w j| * (M / (((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact Real.rpow_le_rpow (abs_nonneg _) (hgeo j) (by linarith)
      _ = (∑ j, |w j|) * (M / (((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p) := by
          rw [← Finset.sum_mul]
      _ ≤ (W * M / ((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p := by
          have hA : 0 ≤ (M / (((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p) := by positivity
          calc (∑ j, |w j|) * (M / (((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p)
              ≤ W * (M / (((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p) :=
                mul_le_mul_of_nonneg_right hW hA
            _ = (W * M / ((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p := by ring

/-- The total variation of the actual local-polynomial weights equals the
total variation of their increasing active-window reindexing. -/
theorem localPolynomialWeights_abs_sum_active (r n q : ℕ) (δ t : ℝ) :
    (∑ i, |localPolynomialWeights r n q δ t i|)
      = ∑ j, |localPolynomialWeights r n q δ t (localWeightActiveIndex n q δ t j)| := by
  classical
  calc ∑ i, |localPolynomialWeights r n q δ t i|
      = ∑ i ∈ localWeightActiveSet n q δ t, |localPolynomialWeights r n q δ t i| := by
        apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro i _ hi
        rw [localPolynomialWeights_zero_outside_activeSet r n q δ t i hi, abs_zero]
    _ = ∑ x : {i // i ∈ localWeightActiveSet n q δ t},
          |localPolynomialWeights r n q δ t x.val| :=
        (Finset.sum_attach (localWeightActiveSet n q δ t)
          (fun i => |localPolynomialWeights r n q δ t i|)).symm
    _ = ∑ j, |localPolynomialWeights r n q δ t (localWeightActiveIndex n q δ t j)| := by
        simpa only [localWeightActiveIndex] using
          ((localWeightActiveEquiv n q δ t).sum_comp
            (fun x : {i // i ∈ localWeightActiveSet n q δ t} =>
              |localPolynomialWeights r n q δ t x.val|)).symm

/-- **The Hölder weight contraction for the actual local-polynomial weights**
(stability-input form).  Given the total-variation bound and the moment
conditions produced by `localPolynomialWeights_uniform_stability` (order `r ≥
⌊p⌋`), the weighted grid average of `f` over the active window at bandwidth
`δ` concentrates on `f t` at the rate `δ^p`:

`|∑_j w(idx j) · f(grid(idx j)) - f t| ≤ (C · M / ⌊p⌋!) · δ^p`. -/
theorem holderWeightContraction_localPolynomialWeights_of_stable
    (p M : ℝ) (hp : 1 ≤ p) (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r n : ℕ) (hrp : Nat.floor p ≤ r) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (Cstab : ℝ)
    (hsumabs : (∑ i, |localPolynomialWeights r n 1 δ t i|) ≤ Cstab)
    (hmoments : ∀ k : Fin (r + 1),
      (∑ i, localPolynomialWeights r n 1 δ t i * ((grid n i.val - t) / δ) ^ k.val)
        = if k = 0 then 1 else 0) :
    |∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)
          * f (grid n (localWeightActiveIndex n 1 δ t j).val) - f t|
      ≤ (Cstab * M / ((Nat.floor p).factorial : ℕ) : ℝ) * δ ^ p := by
  classical
  -- hsum : the active reindexing of the weights sums to one
  have h1 : ∑ i, localPolynomialWeights r n 1 δ t i = 1 := by
    have h0 := hmoments (0 : Fin (r + 1))
    simpa using h0
  have hsum' : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j) = 1 := by
    have h2 := localPolynomialWeights_sum_active r n 1 δ t (fun _ => (1 : ℝ))
    simp only [mul_one] at h2
    rw [← h2]
    exact h1
  -- the moment conditions transfer to the active reindexing, rescaled by δ^k
  have hmomk : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.floor p →
      ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)
          * (grid n (localWeightActiveIndex n 1 δ t j).val - t) ^ k = 0 := by
    intro k hk1 hkP
    have hne : ¬ (⟨k, by omega⟩ : Fin (r + 1)) = 0 := by
      intro hz
      have hv : k = 0 := Fin.ext_iff.mp hz
      omega
    have h2 := localPolynomialWeights_sum_active r n 1 δ t
      (fun i => ((grid n i.val - t) / δ) ^ k)
    have h3 : ∑ i, localPolynomialWeights r n 1 δ t i * ((grid n i.val - t) / δ) ^ k = 0 := by
      have hm' : ∑ i, localPolynomialWeights r n 1 δ t i * ((grid n i.val - t) / δ) ^ k
          = if (⟨k, by omega⟩ : Fin (r + 1)) = 0 then 1 else 0 := hmoments ⟨k, by omega⟩
      rw [if_neg hne] at hm'
      exact hm'
    have h4 : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)
          * ((grid n (localWeightActiveIndex n 1 δ t j).val - t) / δ) ^ k = 0 :=
      h2.symm.trans h3
    have h6 : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
        localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)
          * ((grid n (localWeightActiveIndex n 1 δ t j).val - t) / δ) ^ k
        = (δ ^ k)⁻¹ * (localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)
            * (grid n (localWeightActiveIndex n 1 δ t j).val - t) ^ k) := by
      intro j
      rw [div_pow]
      ring
    rw [Finset.sum_congr rfl (fun j _ => h6 j), ← Finset.mul_sum, mul_eq_zero] at h4
    rcases h4 with hz | hz
    · exact absurd (inv_eq_zero.mp hz) (pow_ne_zero k (ne_of_gt hδ))
    · exact hz
  -- active-window geometry: |grid(idx j) - t| ≤ δ
  have hgeo : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      |grid n (localWeightActiveIndex n 1 δ t j).val - t| ≤ δ := by
    intro j
    have hmem := localWeightActiveIndex_mem n 1 δ t j
    have hfilter := (Finset.mem_filter.mp hmem).2
    have h1 : |grid n (localWeightActiveIndex n 1 δ t j).val - t| / δ < 1 := by
      rwa [abs_div, abs_of_pos hδ] at hfilter
    have h2 : |grid n (localWeightActiveIndex n 1 δ t j).val - t| < δ := by
      rwa [div_lt_iff₀ hδ, one_mul] at h1
    exact le_of_lt h2
  have hxoo : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      grid n (localWeightActiveIndex n 1 δ t j).val ∈ Ioo (0 : ℝ) 1 := fun j =>
    grid_mem n _ hn (by have := (localWeightActiveIndex n 1 δ t j).isLt; omega)
  have hW : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      |localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)| ≤ Cstab := by
    rw [← localPolynomialWeights_abs_sum_active r n 1 δ t]
    exact hsumabs
  exact holderWeightContraction p M Cstab δ t hp hM f hf _ _ ht hxoo hsum' hmomk hW hgeo hδ.le

/-- **The Hölder weight contraction, packaged over the actual local-polynomial
weights.**  Under the uniform-stability window (`N₀ ≤ n·δ`, `δ ≤ 1/2`) with
`⌊p⌋ ≤ r`, there is an explicit `M' = C·M/⌊p⌋!` (with `C` the
uniform-stability constant) with
`|∑_j w(idx j) · f(grid(idx j)) - f t| ≤ M'·δ^p`. -/
theorem exists_holderWeightContraction_localPolynomialWeights (p M : ℝ) (hp : 1 ≤ p)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (hrp : Nat.floor p ≤ r) :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∃ Cstab : ℝ, 0 < Cstab ∧ ∀ n : ℕ, 0 < n → ∀ δ t : ℝ, 0 < δ →
      δ ≤ 1 / 2 → t ∈ Ioo (0 : ℝ) 1 → N₀ ≤ (n : ℝ) * δ →
      ∃ M' : ℝ, 0 ≤ M' ∧
        |∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)
              * f (grid n (localWeightActiveIndex n 1 δ t j).val) - f t|
          ≤ M' * δ ^ p := by
  obtain ⟨N₀, hN₀, Cstab, hCstab, hstab⟩ := localPolynomialWeights_uniform_stability r 1
  refine ⟨N₀, hN₀, Cstab, hCstab, ?_⟩
  intro n hn δ t hδ hδhalf ht hN
  obtain ⟨hdet, hptw, hsumabs, hmoments⟩ :=
    hstab n hn (by omega) δ t hδ hδhalf (Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩) hN
  refine ⟨Cstab * M / ((Nat.floor p).factorial : ℕ), by positivity, ?_⟩
  exact holderWeightContraction_localPolynomialWeights_of_stable p M hp hM f hf r n hrp hn δ t hδ ht
    Cstab hsumabs hmoments

/-! ## Part D: the drift-side assembly (E5 bias envelope) -/

/-- The known-scale statistic weight is exactly the active reindexing of the
local-polynomial weight (the `S⁻¹ u = w` normalization of file 22 §1). -/
theorem unitStatWeight_eq_localPolynomialWeight (f : ℝ → ℝ) (r n : ℕ) (δ t : ℝ)
    (hnd : 0 < (n : ℝ) * δ) (j : Fin (localWeightActiveSet n 1 δ t).card) :
    ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
      = localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j) := by
  unfold actualQ1ChainWeight
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnd), one_mul]

/-- **The E5ChainInstantiation ↔ P5LogHLayers interface identity.**  The
spectral chain log statistic `Ĝ_spec` is the unit-weight known-scale log
statistic rescaled by `S^{2-2 f t}` with `S = n·δ`: the combo vectors agree
verbatim and the two weight families are proportional by that constant. -/
theorem chainLogStatistic_eq_rpow_smul (f : ℝ → ℝ) (r n : ℕ) (δ t : ℝ)
    (hnd : 0 < (n : ℝ) * δ) (x : EuclideanSpace ℝ (Fin n)) :
    chainLogStatistic f r n δ t x
      = ((n : ℝ) * δ) ^ (2 - 2 * f t) * p5KnownScaleLogStatistic f r n δ t x := by
  unfold chainLogStatistic p5KnownScaleLogStatistic actualQ1SpectralWeight
  simp only [gaussianLogStatistic]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcoef : ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
      = ((n : ℝ) * δ) ^ (2 - 2 * f t) * ((n : ℝ) * δ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hnd (2 - 2 * f t) (-1 : ℝ)]
    congr 1
  rw [hcoef]
  ring

/-- **The calibrated chain statistic is the scaled known-scale H transform**
with the rescaled center `cσ / S^{2-2 f t}`: the two calibrations of the E5
fluctuation side and the drift side coincide up to the `S^{2-2 f t}` scaling. -/
theorem chainCalibratedStatistic_eq (f : ℝ → ℝ) (r n : ℕ) (δ t : ℝ)
    (hnd : 0 < (n : ℝ) * δ) (cσ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    chainCalibratedStatistic f r n δ t cσ x
      = ((n : ℝ) * δ) ^ (2 - 2 * f t)
          * p5KnownScaleHtilde f r n δ t (cσ / ((n : ℝ) * δ) ^ (2 - 2 * f t)) x := by
  unfold chainCalibratedStatistic p5KnownScaleHtilde
  rw [chainLogStatistic_eq_rpow_smul f r n δ t hnd x]
  have hS : ((n : ℝ) * δ) ^ (2 - 2 * f t) ≠ 0 := (Real.rpow_pos_of_pos hnd _).ne'
  have hform : (cσ - ((n : ℝ) * δ) ^ (2 - 2 * f t) * p5KnownScaleLogStatistic f r n δ t x)
        / (2 * Real.log n)
      = ((n : ℝ) * δ) ^ (2 - 2 * f t)
          * ((cσ / ((n : ℝ) * δ) ^ (2 - 2 * f t) - p5KnownScaleLogStatistic f r n δ t x)
            / (2 * Real.log n)) := by
    field_simp
  rw [hform]

/-- **The drift-side expectation identity** (the heart of the E5 bias
expansion).  Under the row-nondegeneracy `hane` and the unit-sum premise
`hw1` (mainline-owned middleware), the expectation of the known-scale H
transform decomposes EXACTLY as

`E Ĥtilde = ∑ ŵ_j · H_j + (cσ - gaussianLogSquareMean - ∑ ŵ_j · L_j) / (2 log n)`,

with `H_j` the sampled Hurst value at the active row and `L_j := log
‖gridStrideFirstActual n 1 H (idx j)‖²` the per-row log deviation.  Taking
`cσ := gaussianLogSquareMean` kills the constant term. -/
theorem p5KnownScaleHtilde_expectation_eq (f : ℝ → ℝ) (r n : ℕ) (hn : 1 < n) (δ t : ℝ)
    (_hδ : 0 < δ) (cσ : ℝ) (H : Fin n → Ioo (0 : ℝ) 1)
    (hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i • actualQ1Obs f n H i ≠ 0)
    (hw1 : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j = 1) :
    (∫ x, p5KnownScaleHtilde f r n δ t cσ x ∂featureGaussian (actualQ1Obs f n H))
      = ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
            * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ))
        + ((cσ - gaussianLogSquareMean
            - ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
                ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
                  * Real.log (‖gridStrideFirstActual n 1 H
                      (localWeightActiveIndex n 1 δ t j)‖ ^ 2))
          / (2 * Real.log n)) := by
  classical
  have hn1 : (0 : ℝ) < 2 * Real.log n := by
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    positivity
  have hGmemLp : MemLp (p5KnownScaleLogStatistic f r n δ t) 2
      (featureGaussian (actualQ1Obs f n H)) :=
    gaussianLogStatistic_memLp_two (actualQ1Obs f n H)
      (fun i => ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t i) (actualQ1Coeff n δ t) hane
  have hGint : Integrable (p5KnownScaleLogStatistic f r n δ t)
      (featureGaussian (actualQ1Obs f n H)) := hGmemLp.integrable one_le_two
  have hsplit : ∫ x, p5KnownScaleHtilde f r n δ t cσ x ∂featureGaussian (actualQ1Obs f n H)
      = (cσ - ∫ x, p5KnownScaleLogStatistic f r n δ t x ∂featureGaussian (actualQ1Obs f n H))
        / (2 * Real.log n) := by
    unfold p5KnownScaleHtilde
    have hform : (fun x => (cσ - p5KnownScaleLogStatistic f r n δ t x) / (2 * Real.log n))
        = fun x => (2 * Real.log n)⁻¹ * (cσ - p5KnownScaleLogStatistic f r n δ t x) := by
      funext x; ring
    rw [hform, integral_const_mul, integral_sub (integrable_const cσ) hGint]
    have hc : ∫ _x : EuclideanSpace ℝ (Fin n), (cσ : ℝ) ∂featureGaussian (actualQ1Obs f n H)
        = cσ := by
      rw [integral_const]
      simp
    rw [hc]
    ring
  have hExpG : ∫ x, p5KnownScaleLogStatistic f r n δ t x ∂featureGaussian (actualQ1Obs f n H)
      = ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          (((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j)
            * (Real.log (‖∑ i, actualQ1Coeff n δ t j i • actualQ1Obs f n H i‖ ^ 2)
                + gaussianLogSquareMean) :=
    gaussianLogStatistic_expectation (actualQ1Obs f n H)
      (fun i => ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t i) (actualQ1Coeff n δ t) hane
  have hrow : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t j i • actualQ1Obs f n H i
        = ((1 : ℝ) / n) ^ ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ))
            • gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j) := by
    intro j
    unfold actualQ1Coeff actualQ1Obs
    simpa only [Nat.cast_one] using gridStrideFirst_feature_identity n 1 (by omega)
      (by norm_num) H (localWeightActiveIndex n 1 δ t j)
  have hlogrow : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      Real.log (‖∑ i, actualQ1Coeff n δ t j i • actualQ1Obs f n H i‖ ^ 2)
        = -2 * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)) * Real.log n
          + Real.log (‖gridStrideFirstActual n 1 H
              (localWeightActiveIndex n 1 δ t j)‖ ^ 2) := by
    intro j
    rw [hrow j]
    have hℓpos : (0 : ℝ) < 1 / n := by positivity
    have hnz : gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j) ≠ 0 := by
      intro hz
      have hcombo := hane j
      rw [hrow j, hz, smul_zero] at hcombo
      exact hcombo rfl
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.log_mul (pow_ne_zero 2 (Real.rpow_pos_of_pos hℓpos _).ne')
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnz)),
      Real.log_pow, Real.log_rpow hℓpos, one_div, Real.log_inv]
    ring
  rw [hsplit, hExpG]
  have hAB : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
        * (Real.log (‖∑ i, actualQ1Coeff n δ t j i • actualQ1Obs f n H i‖ ^ 2)
            + gaussianLogSquareMean)
      = (-2 * Real.log n) * (((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
            * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)))
        + ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * Real.log (‖gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)‖ ^ 2)
        + gaussianLogSquareMean
          * (((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j) := by
    intro j
    rw [hlogrow j]
    ring
  have hsumexp : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
        * (Real.log (‖∑ i, actualQ1Coeff n δ t j i • actualQ1Obs f n H i‖ ^ 2)
            + gaussianLogSquareMean)
      = (-2 * Real.log n) * (∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
              * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)))
        + ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
              * Real.log (‖gridStrideFirstActual n 1 H
                  (localWeightActiveIndex n 1 δ t j)‖ ^ 2)
        + gaussianLogSquareMean * (∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j) := by
    rw [Finset.sum_congr rfl (fun j _ => hAB j), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsumexp]
  rw [show (∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j) = 1 from hw1]
  set SX : ℝ := ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
    ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
      * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)) with hSXdef
  set TX : ℝ := ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
    ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
      * Real.log (‖gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)‖ ^ 2) with hTXdef
  have hLne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp
  ring
/-- The triangle inequality in the `a + b` form, via `abs_sub`. -/
theorem abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  have hrw : x + y = x - (-y) := by ring
  rw [hrw]
  have h2 := abs_sub x (-y)
  rw [abs_neg] at h2
  exact h2

/-- **The drift bound.**  From the exact expectation identity: the deviation of
`E Ĥtilde` from `f t` splits into the weighted-Hurst contraction error `D`
plus a `1/(2 log n)`-scaled constant-offset and per-row log-deviation term,
the latter bounded by `W · E` (total weight variation times the uniform log
bound). -/
theorem p5KnownScaleHtilde_drift_bound (f : ℝ → ℝ) (r n : ℕ) (hn : 1 < n) (δ t : ℝ)
    (hδ : 0 < δ) (cσ : ℝ) (H : Fin n → Ioo (0 : ℝ) 1) (W D E : ℝ) (hE : 0 ≤ E)
    (hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i • actualQ1Obs f n H i ≠ 0)
    (hw1 : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j = 1)
    (hWabs : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j| ≤ W)
    (hcontr : |∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)) - f t| ≤ D)
    (hlog : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      |Real.log (‖gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)‖ ^ 2)| ≤ E) :
    |(∫ x, p5KnownScaleHtilde f r n δ t cσ x ∂featureGaussian (actualQ1Obs f n H)) - f t|
      ≤ D + (|cσ - gaussianLogSquareMean| + W * E) / (2 * Real.log n) := by
  have hn1 : (0 : ℝ) < 2 * Real.log n := by
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    positivity
  have hid := p5KnownScaleHtilde_expectation_eq f r n hn δ t hδ cσ H hane hw1
  have hsumL : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
        * Real.log (‖gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)‖ ^ 2)| ≤ W * E := by
    have hmono : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
        |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * Real.log (‖gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)‖ ^ 2)|
        ≤ |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j| * E := by
      intro j
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hlog j) (abs_nonneg _)
    calc ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * Real.log (‖gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)‖ ^ 2)|
        ≤ ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j| * E :=
          Finset.sum_le_sum fun j _ => hmono j
      _ = (∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j|) * E := by
          rw [← Finset.sum_mul]
      _ ≤ W * E := mul_le_mul_of_nonneg_right hWabs hE
  rw [hid]
  have hkey : (∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)))
      + ((cσ - gaussianLogSquareMean
          - ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
              ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
                * Real.log (‖gridStrideFirstActual n 1 H
                    (localWeightActiveIndex n 1 δ t j)‖ ^ 2)) / (2 * Real.log n))
      - f t
      = ((∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
              * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ))) - f t)
        + ((cσ - gaussianLogSquareMean
            - ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
                ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
                  * Real.log (‖gridStrideFirstActual n 1 H
                      (localWeightActiveIndex n 1 δ t j)‖ ^ 2)) / (2 * Real.log n)) := by ring
  rw [hkey]
  have hterm2 : |(cσ - gaussianLogSquareMean
        - ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
              * Real.log (‖gridStrideFirstActual n 1 H
                  (localWeightActiveIndex n 1 δ t j)‖ ^ 2)) / (2 * Real.log n)|
      ≤ (|cσ - gaussianLogSquareMean| + W * E) / (2 * Real.log n) := by
    have habsS : |∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * Real.log (‖gridStrideFirstActual n 1 H
              (localWeightActiveIndex n 1 δ t j)‖ ^ 2)|
      ≤ W * E := by
      have h0 := Finset.abs_sum_le_sum_abs (fun j : Fin (localWeightActiveSet n 1 δ t).card =>
        ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * Real.log (‖gridStrideFirstActual n 1 H (localWeightActiveIndex n 1 δ t j)‖ ^ 2))
        Finset.univ
      exact h0.trans hsumL
    have hnum : |cσ - gaussianLogSquareMean
        - ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
              * Real.log (‖gridStrideFirstActual n 1 H
                  (localWeightActiveIndex n 1 δ t j)‖ ^ 2)|
      ≤ |cσ - gaussianLogSquareMean| + W * E :=
      (abs_sub _ _).trans (add_le_add (le_refl _) habsS)
    rw [abs_div, abs_of_pos hn1]
    exact div_le_div_of_nonneg_right hnum hn1.le
  calc |((∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
              * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ))) - f t)
        + ((cσ - gaussianLogSquareMean
            - ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
                ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
                  * Real.log (‖gridStrideFirstActual n 1 H
                      (localWeightActiveIndex n 1 δ t j)‖ ^ 2)) / (2 * Real.log n))|
      ≤ |(∑ j : Fin (localWeightActiveSet n 1 δ t).card,
            ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
              * ((H (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ))) - f t|
        + |(cσ - gaussianLogSquareMean
            - ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
                ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
                  * Real.log (‖gridStrideFirstActual n 1 H
                      (localWeightActiveIndex n 1 δ t j)‖ ^ 2)) / (2 * Real.log n)| :=
          abs_add_le _ _
    _ ≤ D + (|cσ - gaussianLogSquareMean| + W * E) / (2 * Real.log n) :=
          add_le_add hcontr hterm2

/-- **The abstract bias envelope (composition).**  For any real `X` on a
probability space with `E X ∈ [0, 1]` (the eventual center band), clipping
through `p5Trunc01` costs at most the fluctuation `F` while the drift of the
center costs at most `D`: `|E p5Trunc01(X) - θ₀| ≤ F + D`. -/
theorem knownScaleEstimator_bias_envelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable X μ) (hX : Integrable X μ)
    (hc : (∫ x, X x ∂μ) ∈ Icc 0 1) (θ₀ F D : ℝ)
    (hfluct : ∫ ω, |X ω - ∫ y, X y ∂μ| ∂μ ≤ F)
    (hdrift : |(∫ x, X x ∂μ) - θ₀| ≤ D) :
    |∫ ω, p5Trunc01 (X ω) ∂μ - θ₀| ≤ F + D := by
  have h1 := truncExpectation_le_fluctuation hXm hX hc
  have hsplit : ∫ ω, p5Trunc01 (X ω) ∂μ - θ₀
      = (∫ ω, p5Trunc01 (X ω) ∂μ - ∫ ω, X ω ∂μ) + ((∫ x, X x ∂μ) - θ₀) := by ring
  rw [hsplit]
  calc |(∫ ω, p5Trunc01 (X ω) ∂μ - ∫ ω, X ω ∂μ) + ((∫ x, X x ∂μ) - θ₀)|
      ≤ |∫ ω, p5Trunc01 (X ω) ∂μ - ∫ ω, X ω ∂μ| + |(∫ x, X x ∂μ) - θ₀| := abs_add_le _ _
    _ ≤ ∫ ω, |X ω - ∫ y, X y ∂μ| ∂μ + |(∫ x, X x ∂μ) - θ₀| := add_le_add h1 le_rfl
    _ ≤ F + D := add_le_add hfluct hdrift

/-- **The final conditional bias envelope for the grid estimator** (honest
rate window).  Under the unit-sum and total-variation weight premises, the
weight contraction at rate `δ^p`, the per-row log deviation bound at the
honest rate `n^{-(1-b)}` (task B), the fluctuation premise at rate `n^{-γ}`
(E5RateLink shape), the eventual center band, the center calibration
`cσ = gaussianLogSquareMean` (which kills the `1/log n` constant term), and
the window `γ ≤ 1 - b` (which makes the log-deviation term fit the budget),
the bias of the actual known-scale H estimator satisfies

`|E Ĥ_n - f t| ≤ (F + Cst + Clog·W/2) · n^{-γ}`.

Honest-scope note: at the endpoint's `γ = f t` with the long-memory band
`f t > 3/4` and Hurst band `f t ∈ (a, b] ⊂ (3/4, 1)` the window `γ ≤ 1 - b`
FAILS (since `b > f t > 1 - f t`), so this theorem does NOT discharge the
endpoint `hBias` at `γ = f t`; closing that gap requires a second-order
increment expansion (rate `n^{-(2-b)}` or better), which is NOT currently in
the repo. -/
theorem knownScaleEstimator_bias_envelope_grid
    (f : ℝ → ℝ) (p b M : ℝ)
    (hf : f ∈ hurstHolderClass p M)
    (r n : ℕ) (δ t cσ γ Cst Clog W F : ℝ) (hClog : 0 ≤ Clog) (hCst : 0 ≤ Cst) (hn : 3 ≤ n)
    (hδ : 0 < δ) (_ht : t ∈ Ioo (0 : ℝ) 1) (hγ : γ ≤ 1 - b)
    (hδp : δ ^ p ≤ (n : ℝ) ^ (-γ))
    (hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hw1 : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j = 1)
    (hWabs : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j| ≤ W)
    (hcontr : |∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * f (grid n (localWeightActiveIndex n 1 δ t j).val) - f t| ≤ Cst * δ ^ p)
    (hlog : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 δ t j)‖ ^ 2)| ≤ Clog * (n : ℝ) ^ (-(1 - b)))
    (hcσ : cσ = gaussianLogSquareMean)
    (hbandc : (∫ x, p5KnownScaleHtilde f r n δ t cσ x ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) ∈ Icc 0 1)
    (hfluct : ∫ x, |p5KnownScaleHtilde f r n δ t cσ x -
        ∫ y, p5KnownScaleHtilde f r n δ t cσ y ∂
          featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))| ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) ≤ F * (n : ℝ) ^ (-γ)) :
    |∫ x, p5KnownScaleEstimator f r n δ t cσ x ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n)) - f t|
      ≤ (F + Cst + Clog * W / 2) * (n : ℝ) ^ (-γ) := by
  classical
  have hn1 : (1 : ℕ) < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  -- the drift bound at the calibrated center (cσ = c₀ kills the offset term)
  have hHrow : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
      (midpointSampleHurst f hf.1 n (strideFirstLeft n 1
        (localWeightActiveIndex n 1 δ t j)) : ℝ)
      = f (grid n (localWeightActiveIndex n 1 δ t j).val) := fun j => rfl
  have hsumsame : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
        * (midpointSampleHurst f hf.1 n (strideFirstLeft n 1
            (localWeightActiveIndex n 1 δ t j)) : ℝ)
      = ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
          ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
            * f (grid n (localWeightActiveIndex n 1 δ t j).val) :=
    Finset.sum_congr rfl fun j _ => by rw [hHrow j]
  have hcontr' : |∑ j : Fin (localWeightActiveSet n 1 δ t).card,
      ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
        * (midpointSampleHurst f hf.1 n (strideFirstLeft n 1
            (localWeightActiveIndex n 1 δ t j)) : ℝ) - f t| ≤ Cst * δ ^ p := by
    rw [hsumsame]
    exact hcontr
  have hE0 : (0 : ℝ) ≤ Clog * (n : ℝ) ^ (-(1 - b)) :=
    mul_nonneg hClog (Real.rpow_nonneg hnR.le _)
  have hdrift0 := p5KnownScaleHtilde_drift_bound f r n hn1 δ t hδ cσ
    (midpointSampleHurst f hf.1 n) W (Cst * δ ^ p) (Clog * (n : ℝ) ^ (-(1 - b))) hE0
    hane hw1 hWabs hcontr' hlog
  rw [hcσ, sub_self, abs_zero, zero_add, ← hcσ] at hdrift0
  -- log n ≥ 1 at n ≥ 3
  have hlog1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hexp : Real.exp (1 : ℝ) ≤ (n : ℝ) := by
      have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact Real.exp_one_lt_three.le.trans h3n
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ)) hexp
    rwa [Real.log_exp] at h
  -- the n^{-(1-b)} ≤ n^{-γ} absorption (base ≥ 1)
  have habso : (n : ℝ) ^ (-(1 - b)) ≤ (n : ℝ) ^ (-γ) :=
    (Real.rpow_le_rpow_left_iff hnR1).mpr (by linarith)
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 - b)) := Real.rpow_nonneg hnR.le _
  have hdiv : (n : ℝ) ^ (-(1 - b)) / Real.log (n : ℝ) ≤ (n : ℝ) ^ (-(1 - b)) := by
    have hlogpos : (0 : ℝ) < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
    have hinv : (Real.log (n : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ hlogpos).mpr hlog1
    rw [div_eq_mul_inv]
    calc (n : ℝ) ^ (-(1 - b)) * (Real.log (n : ℝ))⁻¹
        ≤ (n : ℝ) ^ (-(1 - b)) * 1 :=
          mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hnR.le _)
      _ = (n : ℝ) ^ (-(1 - b)) := mul_one _
  have hW0 : (0 : ℝ) ≤ W :=
    le_trans (Finset.sum_nonneg fun j _ => abs_nonneg _) hWabs
  have hB : W * (Clog * (n : ℝ) ^ (-(1 - b))) / (2 * Real.log (n : ℝ))
      ≤ (Clog * W / 2) * (n : ℝ) ^ (-γ) := by
    calc W * (Clog * (n : ℝ) ^ (-(1 - b))) / (2 * Real.log (n : ℝ))
        = (Clog * W / 2) * ((n : ℝ) ^ (-(1 - b)) / Real.log (n : ℝ)) := by ring
      _ ≤ (Clog * W / 2) * (n : ℝ) ^ (-(1 - b)) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ (Clog * W / 2) * (n : ℝ) ^ (-γ) :=
          mul_le_mul_of_nonneg_left habso (by positivity)
  have hA : Cst * δ ^ p ≤ Cst * (n : ℝ) ^ (-γ) :=
    mul_le_mul_of_nonneg_left hδp hCst
  -- the drift bound packaged for the envelope
  have hdrift : |(∫ x, p5KnownScaleHtilde f r n δ t cσ x ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t|
      ≤ Cst * (n : ℝ) ^ (-γ) + (Clog * W / 2) * (n : ℝ) ^ (-γ) :=
    hdrift0.trans (add_le_add hA hB)
  -- the Htilde side conditions for the abstract envelope
  have hGm : MemLp (p5KnownScaleLogStatistic f r n δ t) 2
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
    gaussianLogStatistic_memLp_two (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (fun i => ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t i) (actualQ1Coeff n δ t) hane
  have hXm : AEStronglyMeasurable (p5KnownScaleHtilde f r n δ t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
    have hcont : Continuous (fun y : ℝ => (cσ - y) / (2 * Real.log (n : ℝ))) :=
      (continuous_const.sub continuous_id).div continuous_const
        (fun _ => by positivity)
    exact hcont.comp_aestronglyMeasurable hGm.aestronglyMeasurable
  have hX : Integrable (p5KnownScaleHtilde f r n δ t cσ)
      (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
    have hstep : Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => p5KnownScaleLogStatistic f r n δ t x - cσ)
        (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) :=
      (hGm.integrable one_le_two).sub (integrable_const cσ)
    have hint : Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (cσ - p5KnownScaleLogStatistic f r n δ t x) / (2 * Real.log (n : ℝ)))
        (featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) := by
      refine (hstep.neg.div_const (2 * Real.log (n : ℝ))).congr
        (Eventually.of_forall fun x => ?_)
      show -(p5KnownScaleLogStatistic f r n δ t x - cσ) / (2 * Real.log (n : ℝ))
        = (cσ - p5KnownScaleLogStatistic f r n δ t x) / (2 * Real.log (n : ℝ))
      ring
    exact hint
  -- the estimator is the clipped transform; apply the envelope and sum the budget
  have henv := knownScaleEstimator_bias_envelope hXm hX hbandc (f t)
    (F * (n : ℝ) ^ (-γ))
    (Cst * (n : ℝ) ^ (-γ) + (Clog * W / 2) * (n : ℝ) ^ (-γ)) hfluct hdrift
  exact henv.trans_eq (by ring)

end Hurst

#print axioms Hurst.abs_log_one_add_le_two_mul
#print axioms Hurst.abs_add_le
#print axioms Hurst.truncExpectation_le_fluctuation
#print axioms Hurst.varyingIncrement_norm_sq_error
#print axioms Hurst.varyingIncrement_logNormSq_error
#print axioms Hurst.gridStrideFirstActual_logNormSq_error
#print axioms Hurst.holderWeightContraction
#print axioms Hurst.localPolynomialWeights_abs_sum_active
#print axioms Hurst.holderWeightContraction_localPolynomialWeights_of_stable
#print axioms Hurst.exists_holderWeightContraction_localPolynomialWeights
#print axioms Hurst.unitStatWeight_eq_localPolynomialWeight
#print axioms Hurst.chainLogStatistic_eq_rpow_smul
#print axioms Hurst.chainCalibratedStatistic_eq
#print axioms Hurst.p5KnownScaleHtilde_expectation_eq
#print axioms Hurst.p5KnownScaleHtilde_drift_bound
#print axioms Hurst.knownScaleEstimator_bias_envelope
#print axioms Hurst.knownScaleEstimator_bias_envelope_grid
