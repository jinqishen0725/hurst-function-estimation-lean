import Hurst.P5L1Joining

/-!
# Concentration-to-truncation transfer (takeover9, task 3)

Abstract transfer theorems connecting (i) integral power bounds (as produced
by the all-order even-moment machinery `WeightedEvenMomentBound.lean`) to
tail probabilities, and (ii) tail probabilities plus a second central moment
to the truncation-expectation correction of the `p5Trunc01` clipping.

* `meas_ge_le_of_integral_pow` — Markov's inequality at power `k`: an
  integral `k`-th absolute-moment bound `≤ M` gives the tail bound
  `λ · μ{λ ≤ |Z|^k} ≤ M` (multiplicative form, `ℝ≥0∞` arithmetic).
* `abs_indicator_le_half_sq` — the pointwise Young bound
  `|Y|·1_A ≤ (Y² + 1_A²)/2`.
* `truncationCorrection_le` — the truncation transfer: with center `m = E X`
  in the clip range, the truncation-change set covered by a tail set
  `{d ≤ |X − m|}`, second-central-moment proxy `V`, and tail bound
  `μ{d ≤ |X − m|} ≤ ε` (real form), the clipping moves the mean by at most
  `V + ε`.

## Honest scope registration (takeover9 deviation)

Feeding the moment premise for the ACTUAL stride-row log statistic requires
the ε-uncorrelation premise of `bardetSurgailis_weighted_evenMoment_bound`,
which FAILS for adjacent stride rows (the adjacent-increment correlation is
`2^(2H−1) − 1 ≈ 0.52`, not ε-small) — the color-class decomposition
(`FeatureColorMoment.featureGaussian_colorClass_evenMoment_bound` keeps the
ε-premise as a hypothesis) is the repo's existing route and is NOT wired for
the log-statistic rows.  The present file therefore delivers the transfer
theorems as reusable abstract pieces with explicit premises; the
instantiation gap is registered in the takeover9 report.

The drift side remains the binding constraint of the hBias milestone: even
with a perfect fluctuation bound, the second-order drift window is
`γ ≤ 2 − 2·b` (`IncrementLogSecondOrder.lean`), strictly below the endpoint
rate `γ = f t > 3/4`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hurst

/-! ## (a) The Markov tail bound -/

/-- **Markov's inequality at power `k`** (`ℝ≥0∞`-native form, the
`mul_meas_ge_le_lintegral₀` wrapper): a lintegral moment bound
`∫⁻ |Z|^k ≤ M` gives the tail bound `t · μ{t ≤ |Z|^k} ≤ M`.  The set is
stated through `ENNReal.ofReal` so that `t` can be taken as
`(threshold)^k` directly.  (A Bochner-integral premise can be bridged by
`integral_eq_lintegral_of_nonneg_ae` plus the integrability-finiteness of
the lintegral; the bridge is left to the caller.) -/
theorem meas_ge_le_of_lintegral_pow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℝ} {k : ℕ}
    (hFmeas : AEMeasurable (fun ω => ENNReal.ofReal (|Z ω| ^ k)) μ)
    {M : ℝ≥0∞} (hM : ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ k) ∂μ ≤ M)
    {t : ℝ≥0∞} :
    t * μ {ω | t ≤ ENNReal.ofReal (|Z ω| ^ k)} ≤ M :=
  (mul_meas_ge_le_lintegral₀ hFmeas t).trans hM

/-- The indicator values dichotomy. -/
theorem indicator_values01 {Ω : Type*} (s : Set Ω) (ω : Ω) :
    s.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ s.indicator (fun _ => (1 : ℝ)) ω = 1 := by
  classical
  by_cases h : ω ∈ s
  · exact Or.inr (s.indicator_of_mem h _)
  · refine Or.inl ?_
    rw [Set.indicator_apply, if_neg (by simpa using h)]

/-- The pointwise Young bound `a · b ≤ (a² + b²) / 2` for `a ≥ 0` and
`b ∈ {0, 1}` (indicator values). -/
theorem abs_indicator_le_half_sq {Y u : ℝ} (hu : u = 0 ∨ u = 1) :
    |Y| * u ≤ (Y ^ 2 + u ^ 2) / 2 := by
  rcases hu with h | h
  · rw [h, mul_zero]
    positivity
  · rw [h, mul_one, ← sq_abs]
    have habs : (0 : ℝ) ≤ |Y| := abs_nonneg _
    nlinarith [sq_nonneg (|Y| - 1)]

/-- **The truncation transfer.**  If the mean `m = E X` lies in the clip
range `[0, 1]`, every point outside the clip range is caught by the tail set
`{d ≤ |X − m|}`, the second central moment is integrable with integral at
most `V`, and the tail measure is at most `ε` (real form), then clipping
through `p5Trunc01` moves the mean by at most `V + ε`.

Proof: pointwise `|p5Trunc01(X) − X| ≤ |X − m|·1_{X ∉ [0,1]}` (the clip
geometry), then Young's inequality `|Y|·1_A ≤ (Y² + 1_A²)/2` and
integration. -/
theorem truncationCorrection_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (Xm : AEStronglyMeasurable X μ) (Xint : Integrable X μ)
    {m V d ε : ℝ} (hm : m = ∫ y, X y ∂μ) (hc : m ∈ Icc 0 1)
    (hintY2 : Integrable (fun ω => (X ω - m) ^ 2) μ)
    (hV : 0 ≤ V) (hvar : ∫ ω, (X ω - m) ^ 2 ∂μ ≤ V) (hε : 0 ≤ ε)
    (hcover : ∀ ω, X ω ∉ Icc 0 1 → d ≤ |X ω - m|)
    (hAm : MeasurableSet {ω | d ≤ |X ω - m|})
    (htail : (μ {ω | d ≤ |X ω - m|}).toReal ≤ ε) :
    |∫ ω, p5Trunc01 (X ω) ∂μ - ∫ ω, X ω ∂μ| ≤ V + ε := by
  classical
  set A : Set Ω := {ω | d ≤ |X ω - m|} with hAdef
  have hIndm : AEStronglyMeasurable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω) μ := by
    fun_prop
  -- the pointwise clip-geometry bound
  have hclip : ∀ ω, |p5Trunc01 (X ω) - X ω|
      ≤ |X ω - m| * ({ω | X ω ∉ Icc 0 1}.indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    by_cases hmem : X ω ∈ Icc 0 1
    · rw [p5Trunc01_eq_self hmem, sub_self, abs_zero]
      rcases indicator_values01 {ω | X ω ∉ Icc 0 1} ω with h0 | h1
      · rw [h0, mul_zero]
      · rw [h1, mul_one]
        exact abs_nonneg _
    · have hind1 : {ω | X ω ∉ Icc 0 1}.indicator (fun _ => (1 : ℝ)) ω
          = (1 : ℝ) := {ω | X ω ∉ Icc 0 1}.indicator_of_mem hmem _
      rw [hind1, mul_one]
      rcases lt_trichotomy (X ω) 0 with hx | hx | hx
      · rw [p5Trunc01_eq_zero (le_of_lt hx),
          abs_of_pos (show (0 : ℝ) < 0 - X ω by linarith),
          abs_of_neg (show X ω - m < 0 by linarith [hc.1])]
        linarith [hc.1]
      · exact absurd (show X ω ∈ Icc 0 1 by rw [hx]; exact ⟨le_rfl, zero_le_one⟩) hmem
      · rcases lt_trichotomy (X ω) 1 with h1 | h1 | h1
        · exact absurd (show X ω ∈ Icc 0 1 from ⟨le_of_lt hx, le_of_lt h1⟩) hmem
        · exact absurd (show X ω ∈ Icc 0 1 by rw [h1]; exact ⟨zero_le_one, le_rfl⟩) hmem
        · rw [p5Trunc01_eq_one (le_of_lt h1),
            abs_of_neg (show (1 : ℝ) - X ω < 0 by linarith),
            abs_of_pos (show (0 : ℝ) < X ω - m by linarith [hc.2])]
          linarith [hc.2]
  -- the indicator cover
  have hcoverInd : ∀ ω, {ω | X ω ∉ Icc 0 1}.indicator (fun _ => (1 : ℝ)) ω
      ≤ A.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hAω : ω ∈ A
    · have e1 : A.indicator (fun _ => (1 : ℝ)) ω = 1 := A.indicator_of_mem hAω _
      rw [e1]
      rcases indicator_values01 {ω | X ω ∉ Icc 0 1} ω with h0 | h1
      · rw [h0]
        exact zero_le_one
      · rw [h1]
    · have h0S : ω ∉ {ω | X ω ∉ Icc 0 1} := fun hS => hAω (hcover ω hS)
      have e0 : {ω | X ω ∉ Icc 0 1}.indicator (fun _ => (1 : ℝ)) ω = 0 := by
        rw [Set.indicator_apply, if_neg (by simpa using h0S)]
      have eA0 : A.indicator (fun _ => (1 : ℝ)) ω = 0 := by
        rw [Set.indicator_apply, if_neg (by simpa using hAω)]
      rw [e0, eA0]
  -- integrability pieces
  have hdmeas : AEStronglyMeasurable (fun ω => p5Trunc01 (X ω)) μ :=
    Continuous.comp_aestronglyMeasurable p5Trunc01_continuous Xm
  have htrunc : Integrable (fun ω => p5Trunc01 (X ω)) μ := by
    have hb1 : ∀ ω, |p5Trunc01 (X ω)| ≤ 1 := by
      intro ω
      have hmem := p5Trunc01_mem_Icc (X ω)
      exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    exact ((MemLp.of_bound (p := 2) hdmeas 1
      (Filter.Eventually.of_forall fun ω => hb1 ω))).integrable one_le_two
  have hdiff : Integrable (fun ω => p5Trunc01 (X ω) - X ω) μ := htrunc.sub Xint
  have hintInd : Integrable (fun ω => (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2) μ := by
    have hb : ∀ ω, |(A.indicator (fun _ => (1 : ℝ)) ω) ^ 2| ≤ 1 := by
      intro ω
      rcases indicator_values01 A ω with h0 | h1
      · rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), abs_zero]
        exact zero_le_one
      · rw [h1, one_pow, abs_of_nonneg zero_le_one]
    exact ((MemLp.of_bound (p := 2) (hIndm.pow 2) 1
      (Filter.Eventually.of_forall fun ω => hb ω))).integrable one_le_two
  -- the tail integral bound
  have hintA : ∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂μ ≤ ε := by
    have hintEq : ∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂μ
        = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [] with ω
      rcases indicator_values01 A ω with h0 | h1
      · rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      · rw [h1, one_pow]
    rw [hintEq]
    have hconv : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ
        = ∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ := rfl
    rw [hconv, MeasureTheory.integral_indicator_one hAm]
    exact htail
  -- the pointwise Young chain
  have hptwise : ∀ ω, |p5Trunc01 (X ω) - X ω|
      ≤ ((X ω - m) ^ 2 + (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2) / 2 := by
    intro ω
    refine le_trans (hclip ω) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (hcoverInd ω) (abs_nonneg _)) ?_
    exact abs_indicator_le_half_sq (indicator_values01 A ω)
  -- final integration
  have hintSum : Integrable (fun ω => ((X ω - m) ^ 2
      + (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2) / 2) μ :=
    (hintY2.add hintInd).div_const (2 : ℝ)
  calc |∫ ω, p5Trunc01 (X ω) ∂μ - ∫ ω, X ω ∂μ|
      = |∫ ω, (p5Trunc01 (X ω) - X ω) ∂μ| := by
        rw [← integral_sub htrunc Xint]
    _ ≤ ∫ ω, |p5Trunc01 (X ω) - X ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ((X ω - m) ^ 2
          + (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2) / 2 ∂μ :=
          integral_mono (hdiff.abs) hintSum (fun ω => hptwise ω)
    _ = ((∫ ω, (X ω - m) ^ 2 ∂μ
          + ∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂μ)) / 2 := by
          rw [integral_div]
          congr 1
          exact integral_add hintY2 hintInd
    _ ≤ (V + ε) / 2 :=
          div_le_div_of_nonneg_right (add_le_add hvar hintA) (by norm_num)
    _ ≤ V + ε := by nlinarith


#print axioms Hurst.meas_ge_le_of_lintegral_pow
#print axioms Hurst.indicator_values01
#print axioms Hurst.abs_indicator_le_half_sq
#print axioms Hurst.truncationCorrection_le
end Hurst
