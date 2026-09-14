import Hurst.P5LogHLayers
import Hurst.GridErrorRate
import Hurst.FirstScaleLongRates

/-!
# P5 L1 joining: the Layer1 → Layer2 seam

This file closes the L1 seam of `Hurst.P5LogHLayers`: the Layer-2 transport cores
(`p5_transport_expectationCentered`) consume an explicit L1-smallness input

`∫ ω, |c n * (est n ω - E est n) - (-(specL n ω - E specL n))| ∂Pn n → 0`,

whose reduction (file 22 (27), left "upstream" in the P5 file) is exactly the
*projection error*: the clipped and unclipped scaled centered H-deviations are
L1-close.  With the pointwise reparametrization `gx = S^{-ψ} sx`
(`p5_YX_identity`), the unclipped scaled centered H-deviation EQUALS the
negated centered log statistic, so the transport L1 term reduces to

`∫ |c * (Π(H̃) - E Π(H̃)) - c * (H̃ - E H̃)| → 0`,

which is `logProjection_L1_tendsto_zero` below.

## Main statements

* `p5Trunc01_lipschitz` — the clipped projection is 1-Lipschitz
  (the "clipped_projection_lipschitz" deliverable).
* `p5Trunc01_shifted_projection_bound` — the quadratic-reflection bound
  `|Π(θ + y) - (θ + y)| ≤ y² / d` whenever the center `θ` sits a distance `d`
  from the clip boundary (`d ≤ θ ≤ 1 - d`).
* `p5_logStatistic_drift_le_sqrt_variance` — the L2→L1 drift bound
  `E|Ĝ - EĜ| ≤ √Var(Ĝ)` for the spectral log statistic (deliverable 2).
* `gaussianLogStatistic_variance_sqmass_row_bound` — the `hE2`/`hW0`-reduced
  variance bound: `Var(Ĝ_spec) ≤ 4 * gaussianLogSquareVariance * C * Σ w²`.
* `p5_projection_L1_single` and `logProjection_L1_tendsto_zero` — the joining
  lemma: under the explicit variance/band/window hypotheses the projection
  error is `≤ 2 * c * V / d → 0`.

## Deviation from the sketched constants

The sketch proposed the projection bound with clipping threshold `d = 2 log n`.
The TRUE geometry is: `p5Trunc01` clips to `[0, 1]`, so the projection error is
controlled by the distance of the CENTER `E H̃ = (cσ - E Ĝ)/(2 log n)` from the
boundary, i.e. by the file-22-W9 projection-center band hypothesis (kept
explicit as `hband` below), and the bound is `|Π(θ + y) - (θ + y)| ≤ y²/d` with
`y = H̃ - E H̃`, hence `E|Πerr| ≤ E(y²)/d = (E(Ĝ - EĜ)²)/(4 log² n · d)` —
`Var / (4 log² n)` DIVIDED by the band width `d`.  The closing scale is therefore
`S^ψ · V / (log n · d)` (hypothesis `hWin`), not `V / (4 log² n)`: under the
`hE2`+`hW0` variance bound `V = O(Σ w_spec²)` this tends to zero precisely when
the bandwidth window makes `S^ψ Σ w_spec² / log n → 0` (satisfied, e.g., by the
spectral-weight profile `Σ w_spec² = O(S^{2ψ - 2})` with `ψ < 1/2` from
`hlong`, since then `S^ψ Σ w² / log n = O(S^{3ψ - 2}/log n) → 0`).  The window
is kept as the explicit hypothesis `hWin` because the spectral-weight profile
rate is upstream work.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Hurst

/-! ## Part 1: the clipped projection (standalone real-lemma layer) -/

theorem p5Trunc01_eq_zero {x : ℝ} (hx : x ≤ 0) : p5Trunc01 x = 0 := by
  rw [p5Trunc01, max_eq_left hx, min_eq_right zero_le_one]

theorem p5Trunc01_eq_one {x : ℝ} (hx : 1 ≤ x) : p5Trunc01 x = 1 := by
  rw [p5Trunc01, max_eq_right (le_trans zero_le_one hx), min_eq_left hx]

theorem p5Trunc01_le_self {x : ℝ} (hx : 0 ≤ x) : p5Trunc01 x ≤ x := by
  rw [p5Trunc01, max_eq_right hx]
  exact min_le_right 1 x

theorem p5Trunc01_continuous : Continuous p5Trunc01 := by
  unfold p5Trunc01
  have h1 : Continuous fun x : ℝ => max (0 : ℝ) x :=
    continuous_const.max continuous_id
  exact (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).min h1

/-- One-sided contraction of the clipped projection. -/
theorem p5Trunc01_sub_le (x y : ℝ) (h : x ≤ y) : p5Trunc01 y - p5Trunc01 x ≤ y - x := by
  unfold p5Trunc01
  rcases le_total x 0 with hx | hx
  · rw [max_eq_left hx]
    rcases le_total 0 y with hy | hy
    · have h1 : min 1 y ≤ y := min_le_right 1 y
      rw [max_eq_right hy, min_eq_right zero_le_one]
      linarith
    · rw [max_eq_left hy, min_eq_right zero_le_one]
      linarith
  · rw [max_eq_right hx]
    have hy0 : 0 ≤ y := le_trans hx h
    rw [max_eq_right hy0]
    rcases le_total 1 y with hy1 | hy1
    · rw [min_eq_left hy1]
      rcases le_total x 1 with hx1 | hx1
      · rw [min_eq_right hx1]
        linarith
      · rw [min_eq_left hx1]
        linarith
    · rw [min_eq_right hy1, min_eq_right (le_trans h hy1)]

/-- **The clipped projection is 1-Lipschitz** (deliverable 1a). -/
theorem p5Trunc01_lipschitz (x y : ℝ) : |p5Trunc01 x - p5Trunc01 y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · have h2 : |p5Trunc01 x - p5Trunc01 y| = p5Trunc01 y - p5Trunc01 x := by
      rw [abs_sub_comm (p5Trunc01 x) (p5Trunc01 y)]
      exact abs_of_nonneg (sub_nonneg.mpr (p5Trunc01_mono h))
    have h3 : |x - y| = y - x := by
      rw [abs_sub_comm x y]
      exact abs_of_nonneg (sub_nonneg.mpr h)
    rw [h2, h3]
    exact p5Trunc01_sub_le x y h
  · have h2 : |p5Trunc01 x - p5Trunc01 y| = p5Trunc01 x - p5Trunc01 y :=
      abs_of_nonneg (sub_nonneg.mpr (p5Trunc01_mono h))
    have h3 : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr h)
    rw [h2, h3]
    exact p5Trunc01_sub_le y x h

/-- The excess bound `|y| ≤ y²/d` for `|y| ≥ d > 0`. -/
theorem abs_le_sq_div (y d : ℝ) (hd : 0 < d) (h : d ≤ |y|) : |y| ≤ y ^ 2 / d := by
  rw [le_div_iff₀ hd]
  calc |y| * d ≤ |y| * |y| := mul_le_mul_of_nonneg_left h (abs_nonneg y)
    _ ≤ y ^ 2 := by nlinarith [sq_abs y]

/-- **The shifted projection bound** (deliverable 1b, TRUE form).

If the center `θ` sits a distance `d > 0` from the clip boundary of
`p5Trunc01` (`d ≤ θ ≤ 1 - d`), then the clipped projection misses `θ + y` by at
most the quadratic reflection `y² / d`: the excess beyond the boundary is at
most `|y|` (whence `≤ y²/d` for `|y| ≥ d`). -/
theorem p5Trunc01_shifted_projection_bound (θ y d : ℝ) (hd : 0 < d) (h0 : d ≤ θ)
    (h1 : θ ≤ 1 - d) : |p5Trunc01 (θ + y) - (θ + y)| ≤ y ^ 2 / d := by
  by_cases hs0 : θ + y < 0
  · rw [p5Trunc01_eq_zero (le_of_lt hs0)]
    have h01 : (0 : ℝ) - (θ + y) = -(θ + y) := by ring
    rw [h01, abs_neg, abs_of_neg hs0]
    have hyneg : y < 0 := by linarith
    calc -(θ + y) ≤ -y := by linarith
      _ = |y| := (abs_of_neg hyneg).symm
      _ ≤ y ^ 2 / d := abs_le_sq_div y d hd (by rw [abs_of_neg hyneg]; linarith)
  · by_cases hle : θ + y ≤ 1
    · rw [p5Trunc01_eq_self ⟨by linarith, hle⟩, sub_self, abs_zero]
      exact div_nonneg (sq_nonneg y) hd.le
    · have hgt : (1 : ℝ) < θ + y := not_le.mp hle
      have habs : |1 - (θ + y)| = θ + y - 1 := by
        rw [abs_sub_comm 1 (θ + y)]
        exact abs_of_nonneg (sub_nonneg.mpr hgt.le)
      rw [p5Trunc01_eq_one hgt.le, habs]
      have hyd : d ≤ y := by linarith
      have hypos : 0 < y := lt_of_lt_of_le hd hyd
      calc θ + y - 1 ≤ y := by linarith
        _ ≤ y ^ 2 / d := by
            have hb := abs_le_sq_div y d hd (show d ≤ |y| by
              rw [abs_of_pos hypos]; exact hyd)
            rwa [abs_of_pos hypos] at hb

/-! ## Part 2: the variance facts for the spectral log statistic -/

/-- **Row bound from total energy.**  If the squared-correlation energy is
uniformly bounded (the `hE2` hypothesis, a doubly-indexed sum), then every row
is bounded by the same constant. -/
theorem sqEnergy_row_le {κ : Type*} [Fintype κ] (c : κ → κ → ℝ) (C : ℝ)
    (hC : ∑ i, ∑ j, c i j ≤ C) (hpos : ∀ i j, 0 ≤ c i j) (j : κ) :
    ∑ k, c j k ≤ C := by
  refine le_trans (Finset.single_le_sum (f := fun i => ∑ k, c i k)
    (fun i _ => Finset.sum_nonneg fun k _ => hpos i k) (Finset.mem_univ j)) ?_
  exact hC

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

theorem featureCorrelation_comm (v : ι → E) (a b : EuclideanSpace ℝ ι) :
    featureCorrelation v a b = featureCorrelation v b a := by
  unfold featureCorrelation
  rw [real_inner_comm, mul_comm]

/-- **The `hE2`+`hW0`-reduced variance bound (file 22 (26)).**

Under a uniform row bound `C` on the squared-correlation matrix (implied by
`hE2` up to index permutation), the variance of the log statistic is bounded by
`4 * gaussianLogSquareVariance * C * Σ w²`, which is `o(1)` under `hW0`. -/
theorem gaussianLogStatistic_variance_sqmass_row_bound {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) (C : ℝ)
    (hC : ∀ j, ∑ k, (featureCorrelation v (a j) (a k)) ^ 2 ≤ C) :
    Var[gaussianLogStatistic w a; featureGaussian v] ≤
      4 * gaussianLogSquareVariance * C * ∑ j, w j ^ 2 := by
  refine le_trans (gaussianLogStatistic_variance_correlation_bound v w a h) ?_
  have h4pos : (0 : ℝ) ≤ 4 * gaussianLogSquareVariance :=
    mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg
  have hinner : ∑ j, ∑ k, |w j| * |w k| * (featureCorrelation v (a j) (a k)) ^ 2
      ≤ C * ∑ j, w j ^ 2 := by
    have hsplit : ∑ j, ∑ k, ((w j ^ 2 + w k ^ 2) / 2) * (featureCorrelation v (a j) (a k)) ^ 2
        = ∑ j, ∑ k, (w j ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
          + ∑ j, ∑ k, (w k ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2 := by
      have h1 : (∑ j, ∑ k, (w j ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
            + ∑ j, ∑ k, (w k ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2)
          = ∑ j, (∑ k, (w j ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
            + ∑ k, (w k ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2) :=
        Finset.sum_add_distrib.symm
      have h2 : ∀ j : κ, (∑ k, (w j ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
            + ∑ k, (w k ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2)
          = ∑ k, ((w j ^ 2 + w k ^ 2) / 2) * (featureCorrelation v (a j) (a k)) ^ 2 := by
        intro j
        exact Eq.trans Finset.sum_add_distrib.symm
          (Finset.sum_congr rfl fun k _ => by ring)
      exact Eq.trans (Finset.sum_congr rfl fun j _ => (h2 j).symm) (Eq.symm h1)
    have hA1 : ∑ j, ∑ k, (w j ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
        ≤ (C / 2) * ∑ j, w j ^ 2 := by
      calc ∑ j, ∑ k, (w j ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
          = ∑ j, (w j ^ 2 / 2) * ∑ k, (featureCorrelation v (a j) (a k)) ^ 2 :=
            Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ j, (w j ^ 2 / 2) * C :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hC j) (by positivity)
        _ = (C / 2) * ∑ j, w j ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
    have hA2 : ∑ j, ∑ k, (w k ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
        ≤ (C / 2) * ∑ k, w k ^ 2 := by
      rw [Finset.sum_comm]
      calc ∑ k, ∑ j, (w k ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
          = ∑ k, (w k ^ 2 / 2) * ∑ j, (featureCorrelation v (a k) (a j)) ^ 2 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [featureCorrelation_comm]
        _ ≤ ∑ k, (w k ^ 2 / 2) * C :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hC k) (by positivity)
        _ = (C / 2) * ∑ k, w k ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ j, ∑ k, |w j| * |w k| * (featureCorrelation v (a j) (a k)) ^ 2
        ≤ ∑ j, ∑ k, ((w j ^ 2 + w k ^ 2) / 2) * (featureCorrelation v (a j) (a k)) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          nlinarith [sq_nonneg (|w j| - |w k|), sq_abs (w j), sq_abs (w k)]
      _ = ∑ j, ∑ k, (w j ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2
          + ∑ j, ∑ k, (w k ^ 2 / 2) * (featureCorrelation v (a j) (a k)) ^ 2 := hsplit
      _ ≤ (C / 2) * ∑ j, w j ^ 2 + (C / 2) * ∑ k, w k ^ 2 := add_le_add hA1 hA2
      _ = C * ∑ j, w j ^ 2 := by ring
  exact le_trans (mul_le_mul_of_nonneg_left hinner h4pos)
    (le_of_eq (by ring : (4 : ℝ) * gaussianLogSquareVariance * (C * ∑ j, w j ^ 2)
      = 4 * gaussianLogSquareVariance * C * ∑ j, w j ^ 2))

/-- **The L2→L1 drift bound (deliverable 2).**
`E|Ĝ_spec - EĜ_spec| ≤ √Var(Ĝ_spec)` on the feature-Gaussian space, with the
variance itself available from
`gaussianLogStatistic_variance_correlation_bound` /
`gaussianLogStatistic_variance_sqmass_row_bound`. -/
theorem p5_logStatistic_drift_le_sqrt_variance {κ : Type*} [Fintype κ]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j, ∑ i, a j i • v i ≠ 0) :
    ∫ x, |gaussianLogStatistic w a x
        - ∫ y, gaussianLogStatistic w a y ∂featureGaussian v| ∂featureGaussian v
      ≤ Real.sqrt (Var[gaussianLogStatistic w a; featureGaussian v]) := by
  have hX : MemLp (fun x => gaussianLogStatistic w a x
      - (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)) 2 (featureGaussian v) :=
    (gaussianLogStatistic_memLp_two v w a h).sub
      (memLp_const (∫ y, gaussianLogStatistic w a y ∂featureGaussian v))
  have hmse := gaussianLogStatistic_mse v w a
    (∫ y, gaussianLogStatistic w a y ∂featureGaussian v) h
  have h2 : ∫ x, (gaussianLogStatistic w a x
      - (∫ y, gaussianLogStatistic w a y ∂featureGaussian v)) ^ 2 ∂featureGaussian v
      = Var[gaussianLogStatistic w a; featureGaussian v] := by
    rw [hmse, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  exact (integral_abs_le_sqrt_second_moment _ _ hX).trans (by rw [h2])

/-! ## Part 3: the L1 joining -/

/-- **Per-instance projection L1 bound.**  On one probability space, with `H`
the untruncated transform, `c ≥ 0` the transport scale and `d` the distance of
the center `E H` from the clip boundary, the scaled centered clipped deviation
and the scaled centered deviation are `2 * c * V / d`-close in L1 whenever
`E (H - E H)² ≤ V`. -/
theorem p5_projection_L1_single {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (H : Ω → ℝ) (c d V : ℝ) (hc : 0 ≤ c) (hd : 0 < d)
    (hband0 : d ≤ ∫ x, H x ∂μ) (hband1 : (∫ x, H x ∂μ) ≤ 1 - d)
    (hH : MemLp H 2 μ) (hMom : ∫ x, (H x - ∫ y, H y ∂μ) ^ 2 ∂μ ≤ V) :
    ∫ x, |c * (p5Trunc01 (H x) - ∫ y, p5Trunc01 (H y) ∂μ)
        - c * (H x - ∫ y, H y ∂μ)| ∂μ ≤ 2 * c * V / d := by
  set mH : ℝ := ∫ x, H x ∂μ with hmH
  have hMemSub : MemLp (fun x => H x - mH) 2 μ := hH.sub (memLp_const mH)
  have hSq : Integrable (fun x => (H x - mH) ^ 2) μ := hMemSub.integrable_sq
  have hSqD : Integrable (fun x => (H x - mH) ^ 2 / d) μ := hSq.div_const d
  have hHint : Integrable H μ := hH.integrable one_le_two
  have hPi : AEMeasurable (fun x => p5Trunc01 (H x)) μ :=
    p5Trunc01_continuous.measurable.comp_aemeasurable hH.aemeasurable
  have hPiInt : Integrable (fun x => p5Trunc01 (H x)) μ := by
    refine Integrable.of_bound hPi.aestronglyMeasurable (1 : ℝ)
      (Eventually.of_forall fun x => ?_)
    obtain ⟨h1, h2⟩ := p5Trunc01_mem_Icc (H x)
    exact abs_le.mpr ⟨by linarith, h2⟩
  have hE : Integrable (fun x => p5Trunc01 (H x) - H x) μ := hPiInt.sub hHint
  have hAbsE : Integrable (fun x => |p5Trunc01 (H x) - H x|) μ := hE.abs
  -- the deterministic drift `δ = E(Π(H) - H)`
  set δ : ℝ := ∫ x, p5Trunc01 (H x) - H x ∂μ with hδ
  have hδdef : δ = ∫ y, p5Trunc01 (H y) ∂μ - ∫ y, H y ∂μ := by
    rw [hδ, integral_sub hPiInt hHint]
  have hintE : ∫ x, |p5Trunc01 (H x) - H x| ∂μ ≤ V / d := by
    refine le_trans (integral_mono hAbsE hSqD (fun x => ?_)) ?_
    · have hp := p5Trunc01_shifted_projection_bound mH (H x - mH) d hd hband0 hband1
      simpa using hp
    · rw [integral_div d]
      exact (div_le_div_iff₀ hd (by positivity)).mpr (by nlinarith [hMom, hd.le])
  have hδle : |δ| ≤ V / d := by
    rw [hδ]
    exact abs_integral_le_integral_abs.trans hintE
  -- pointwise rewrite of the integrand, then the triangle chain
  have hcongr : ∫ x, |c * (p5Trunc01 (H x) - ∫ y, p5Trunc01 (H y) ∂μ)
      - c * (H x - ∫ y, H y ∂μ)| ∂μ
      = ∫ x, c * |p5Trunc01 (H x) - H x - δ| ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [hδdef]
    have hpt : |c * (p5Trunc01 (H x) - ∫ y, p5Trunc01 (H y) ∂μ)
        - c * (H x - ∫ y, H y ∂μ)|
        = c * |p5Trunc01 (H x) - H x
          - (∫ y, p5Trunc01 (H y) ∂μ - ∫ y, H y ∂μ)| := by
      have h1 : c * (p5Trunc01 (H x) - ∫ y, p5Trunc01 (H y) ∂μ)
          - c * (H x - ∫ y, H y ∂μ)
          = c * (p5Trunc01 (H x) - H x
            - (∫ y, p5Trunc01 (H y) ∂μ - ∫ y, H y ∂μ)) := by ring
      rw [h1, abs_mul, abs_of_nonneg hc]
    exact hpt
  have hAbsSub : Integrable (fun x => |p5Trunc01 (H x) - H x - δ|) μ :=
    (hE.sub (integrable_const δ)).abs
  have hAbsAdd : Integrable (fun x => |p5Trunc01 (H x) - H x| + |δ|) μ :=
    hAbsE.add (integrable_const |δ|)
  have hmono : ∫ x, |p5Trunc01 (H x) - H x - δ| ∂μ
      ≤ ∫ x, |p5Trunc01 (H x) - H x| ∂μ + |δ| := by
    refine le_trans (integral_mono hAbsSub hAbsAdd (fun x => ?_)) ?_
    · have hx := abs_add_le (p5Trunc01 (H x) - H x) (-δ)
      rw [abs_neg] at hx
      exact hx
    · rw [integral_add hAbsE (integrable_const |δ|), integral_const, probReal_univ,
        smul_eq_mul, one_mul]
  calc ∫ x, |c * (p5Trunc01 (H x) - ∫ y, p5Trunc01 (H y) ∂μ)
        - c * (H x - ∫ y, H y ∂μ)| ∂μ
      = ∫ x, c * |p5Trunc01 (H x) - H x - δ| ∂μ := hcongr
    _ = c * ∫ x, |p5Trunc01 (H x) - H x - δ| ∂μ := integral_const_mul _ _
    _ ≤ c * (∫ x, |p5Trunc01 (H x) - H x| ∂μ + |δ|) :=
        mul_le_mul_of_nonneg_left hmono hc
    _ ≤ c * (V / d + V / d) :=
        mul_le_mul_of_nonneg_left (add_le_add hintE hδle) hc
    _ = 2 * c * V / d := by ring

/-- **The L1 joining lemma (the deliverable).**

`X_n := c n * (Π(H̃_n) - E Π(H̃_n))`, the scaled centered CLIPPED H-deviation
(the Layer-2 transport source, after the `p5_YX_identity` reparametrization
which makes the unclipped scaled centered deviation EXACTLY the negated
centered log statistic), and `Y_n := c n * (H̃_n - E H̃_n)`, the scaled centered
H-deviation.  Under the per-instance second-moment bound `E(Ĝ - EĜ)² ≤ V n`
(itself `≤ 4 * gaussianLogSquareVariance * C₂ * Σ w_spec²` via
`gaussianLogStatistic_mse` + `gaussianLogStatistic_variance_sqmass_row_bound`),
the projection-center band `d n ≤ E H̃_n ≤ 1 - d n` and the bandwidth window
`S^ψ n * V n / (L n * d n) → 0` (with `c n = 2 S^ψ n L n`, `L n = log n`),
`∫ |X_n - Y_n| → 0`. -/
theorem logProjection_L1_tendsto_zero
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (Pn : ∀ n : ℕ, Measure (Ωn n)) [∀ n : ℕ, IsProbabilityMeasure (Pn n)]
    (G : (n : ℕ) → Ωn n → ℝ) (cσ : ℝ) (Sψ L d V : ℕ → ℝ)
    (hMem : ∀ n, MemLp (G n) 2 (Pn n))
    (hMom : ∀ᶠ n in atTop, ∫ x, (G n x - ∫ y, G n y ∂Pn n) ^ 2 ∂Pn n ≤ V n)
    (hLpos : ∀ᶠ n in atTop, 0 < L n)
    (hSψpos : ∀ᶠ n in atTop, 0 ≤ Sψ n)
    (hdpos : ∀ᶠ n in atTop, 0 < d n)
    (hband : ∀ᶠ n in atTop, d n ≤ (cσ - ∫ y, G n y ∂Pn n) / (2 * L n)
      ∧ (cσ - ∫ y, G n y ∂Pn n) / (2 * L n) ≤ 1 - d n)
    (hWin : Tendsto (fun n => Sψ n * V n / (L n * d n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |(2 * Sψ n * L n) * (p5Trunc01 ((cσ - G n x) / (2 * L n))
        - ∫ y, p5Trunc01 ((cσ - G n y) / (2 * L n)) ∂Pn n)
      - (2 * Sψ n * L n) * ((cσ - G n x) / (2 * L n)
        - ∫ y, (cσ - G n y) / (2 * L n) ∂Pn n)| ∂Pn n) atTop (𝓝 0) := by
  have hbd : ∀ᶠ n in atTop, ∫ x, |(2 * Sψ n * L n)
      * (p5Trunc01 ((cσ - G n x) / (2 * L n))
        - ∫ y, p5Trunc01 ((cσ - G n y) / (2 * L n)) ∂Pn n)
    - 2 * Sψ n * L n * ((cσ - G n x) / (2 * L n)
        - ∫ y, (cσ - G n y) / (2 * L n) ∂Pn n)| ∂Pn n
      ≤ Sψ n * V n / (L n * d n) := by
    filter_upwards [hLpos, hSψpos, hdpos, hMom, hband] with n hL hSψ hd hM hb
    have h2L : 2 * L n ≠ 0 := by linarith [hL]
    have h2Lpos : (0 : ℝ) < 2 * L n := by linarith [hL]
    have hHL0 : MemLp (fun x => -(1 / (2 * L n)) * (G n x - cσ)) 2 (Pn n) :=
      ((hMem n).sub (memLp_const cσ)).const_mul (-(1 / (2 * L n)))
    have hHL : MemLp (fun x => (cσ - G n x) / (2 * L n)) 2 (Pn n) :=
      ((memLp_congr_ae (Eventually.of_forall fun x => by
        have hx : -(1 / (2 * L n)) * (G n x - cσ)
            = (cσ - G n x) / (2 * L n) := by
          field_simp
          ring
        rw [hx])).mpr hHL0)
    have hmean : ∫ x, (cσ - G n x) / (2 * L n) ∂Pn n
        = (cσ - ∫ y, G n y ∂Pn n) / (2 * L n) := by
      rw [integral_div (2 * L n) (fun x => cσ - G n x),
        integral_sub (integrable_const cσ) ((hMem n).integrable one_le_two),
        integral_const, smul_eq_mul, probReal_univ, one_mul]
    have hb2 : d n ≤ ∫ x, (cσ - G n x) / (2 * L n) ∂Pn n
        ∧ ∫ x, (cσ - G n x) / (2 * L n) ∂Pn n ≤ 1 - d n := by
      rw [hmean]
      exact hb
    have hmom2 : ∫ x, ((cσ - G n x) / (2 * L n)
        - ∫ y, (cσ - G n y) / (2 * L n) ∂Pn n) ^ 2 ∂Pn n
        = (∫ x, (G n x - ∫ y, G n y ∂Pn n) ^ 2 ∂Pn n) / (2 * L n) ^ 2 := by
      have hcong : ∀ x, ((cσ - G n x) / (2 * L n)
          - ∫ y, (cσ - G n y) / (2 * L n) ∂Pn n) ^ 2
          = (G n x - ∫ y, G n y ∂Pn n) ^ 2 / (2 * L n) ^ 2 := by
        intro x
        rw [hmean]
        field_simp
        ring
      rw [integral_congr_ae (Eventually.of_forall hcong),
        integral_div ((2 * L n) ^ 2) (fun a => (G n a - ∫ y, G n y ∂Pn n) ^ 2)]
    have hres := p5_projection_L1_single (fun x => (cσ - G n x) / (2 * L n))
      (2 * Sψ n * L n) (d n) (V n / (2 * L n) ^ 2)
      (mul_nonneg (mul_nonneg (by norm_num) hSψ) hL.le) hd hb2.1 hb2.2 hHL (by
        rw [hmom2]
        exact (div_le_div_iff₀ (pow_pos h2Lpos 2) (pow_pos h2Lpos 2)).mpr
          (mul_le_mul_of_nonneg_right hM (pow_nonneg h2Lpos.le 2)))
    refine le_trans hres ?_
    field_simp
    linarith
  exact squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun _ => abs_nonneg _)
    hbd hWin

end Hurst
