import Hurst.E5BiasExpansion
import Hurst.IncrementLogSecondOrder
import Hurst.TruncationTransfer

/-!
# hBias honest closure (takeover9, task 4)

This file assembles the second-order increment refinement of task 2 into
the drift side of the E5 bias envelope, and REGISTERS — as formally proved
arithmetic — the impossibility of discharging the endpoint's `hBias`
premise at the endpoint rate `γ = f t` by the per-row log route.

* `gridStrideFirstActual_logNormSq_secondOrder` — the log-level second-order
  per-row bound `|log ‖inc‖²| ≤ C·n^(-(2-2b))` (task 2's norm-square bound +
  the `|log(1+x)| ≤ 2|x|` amplification under smallness).
* `knownScaleEstimator_bias_envelope_grid_secondOrder` — the E5 bias
  envelope with the honest second-order window `γ ≤ 2 - 2*b` (strictly
  better than the first-order `γ ≤ 1 - b` because `2 - 2*b > 1 - b ⟺ b < 1`).
* `bias_window_firstOrder_infeasible` / `bias_window_secondOrder_infeasible`
  — the §3 audit theorems: on the long-memory band `3/4 < f t` with
  `f t ≤ b < 1`, NEITHER the first-order window `f t ≤ 1 - b` NOR the
  second-order window `f t ≤ 2 - 2*b` can hold at `γ = f t`.

## The honest verdict (takeover9 conclusion; not papered over)

The task book's second-order target rate `n^(-(2-b))` is unattainable: the
normalization `ℓ^(-2h)` eats two powers of the stride scale, and the honest
rate is `ℓ^(2-2b) = n^(-(2-2b))` with `2-2b < 1` (IncrementLogSecondOrder's
module docstring).  Since the endpoint rate is `γ = f t > 3/4` and
`2 - 2*b < 1/2 < 3/4`, the per-row log route CANNOT reach `γ = f t` at ANY
order of the mismatch expansion (the deviation is Θ(|k-h|·ℓ^(1-2h)) with a
generically nonzero coefficient).  Consequently:

* the endpoint premise `hBias : |E Ĥ_n - f t| ≤ C·n^(-(f t))` is NOT
  dischargeable from the standing model premises — it is satisfiable only
  under additional degeneracy (e.g. a constant Hurst profile, where every
  row log-deviation vanishes exactly);
* this file delivers the strict improvement `γ ≤ 2 - 2*b` of the honest
  window and stops; per the task book's honest clause, the statistical
  closure of the endpoint at `γ = f t` is REFUTED for this estimator
  family and is REGISTERED, not claimed.

The truncation-side wiring point: `truncationCorrection_le`
(TruncationTransfer) can replace the crude fluctuation premise `hfluct` of
the envelope once a variance-rate and a tail bound for `p5KnownScaleHtilde`
are available (the latter needs the color-class even-moment machinery —
registered gap).
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology

namespace Hurst

/-! ## The log-level second-order per-row bound -/

/-- **The log-level second-order per-row bound.**  For the Hölder-sampled
stride rows, `|log ‖inc‖²| ≤ 2·C·n^(-(2-2b))` once `C·n^(-(2-2b)) ≤ 1/2`
(the norm-square bound of task 2 plus the `|log(1+x)| ≤ 2|x|`
amplification of E5BiasExpansion). -/
theorem gridStrideFirstActual_logNormSq_secondOrder (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 1 / 2 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C' ≥ 0, ∀ n : ℕ, 1 < n → ∀ (f : ℝ → ℝ) (hfclass : f ∈ hurstHolderClass p M),
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ i : Fin (n - 1),
        C' * (n : ℝ) ^ (-(2 - 2 * b)) ≤ 1 / 2 →
        |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i‖ ^ 2)|
          ≤ C' * (n : ℝ) ^ (-(2 - 2 * b)) := by
  obtain ⟨C, hC, hbound⟩ :=
    gridStrideFirstActual_norm_sq_secondOrder p a b M hp ha hb hab hM
  refine ⟨2 * C, by positivity, ?_⟩
  intro n hn f hfclass hF i hsmall
  have herr := hbound n hn f hfclass hF i
  have hCsmall : C * (n : ℝ) ^ (-(2 - 2 * b)) ≤ 1 / 2 := by
    have hnn := hsmall
    have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 - 2 * b)) :=
      Real.rpow_nonneg (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast (show 0 ≤ n by omega))
        (-(2 - 2 * b))
    have hC' := hC
    nlinarith [hpos, hnn, hC']
  have habs : |‖gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i‖ ^ 2 - 1|
      ≤ 1 / 2 := herr.trans hCsmall
  have hlogle := abs_log_one_add_le_two_mul
    (x := ‖gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i‖ ^ 2 - 1) habs
  calc |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i‖ ^ 2)|
      = |Real.log (1 + (‖gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i‖ ^ 2
          - 1))| := by congr 1; ring
    _ ≤ 2 * |‖gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i‖ ^ 2 - 1| :=
          hlogle
    _ ≤ 2 * (C * (n : ℝ) ^ (-(2 - 2 * b))) :=
          mul_le_mul_of_nonneg_left herr zero_le_two
    _ = 2 * C * (n : ℝ) ^ (-(2 - 2 * b)) := by ring

/-- **The E5 bias envelope at the honest second-order rate.**  Identical to
`knownScaleEstimator_bias_envelope_grid` except that the per-row log
deviation is fed at the second-order rate `n^(-(2-2b))` (task 2), which
IMPROVES the admissible window from `γ ≤ 1 - b` to `γ ≤ 2 - 2*b`
(strictly, since `2 - 2*b > 1 - b ⟺ b < 1`).  All other premises are
unchanged. -/
theorem knownScaleEstimator_bias_envelope_grid_secondOrder
    (f : ℝ → ℝ) (p b M : ℝ)
    (hf : f ∈ hurstHolderClass p M)
    (r n : ℕ) (δ t cσ γ Cst Clog W F : ℝ) (hClog : 0 ≤ Clog) (hCst : 0 ≤ Cst) (hn : 3 ≤ n)
    (hδ : 0 < δ) (_ht : t ∈ Ioo (0 : ℝ) 1) (hγ : γ ≤ 2 - 2 * b)
    (hδp : δ ^ p ≤ (n : ℝ) ^ (-γ))
    (hw1 : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j = 1)
    (hWabs : ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        |((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j| ≤ W)
    (hcontr : |∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        ((n : ℝ) * δ)⁻¹ * actualQ1ChainWeight f r n δ t j
          * f (grid n (localWeightActiveIndex n 1 δ t j).val) - f t| ≤ Cst * δ ^ p)
    (hlog : ∀ j : Fin (localWeightActiveSet n 1 δ t).card,
        |Real.log (‖gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
            (localWeightActiveIndex n 1 δ t j)‖ ^ 2)| ≤ Clog * (n : ℝ) ^ (-(2 - 2 * b)))
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
  have hane : ∀ k : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ i, actualQ1Coeff n δ t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 :=
    fun k => actualQ1_hane_discharged f hf n (by omega) δ t k
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
  have hE0 : (0 : ℝ) ≤ Clog * (n : ℝ) ^ (-(2 - 2 * b)) :=
    mul_nonneg hClog (Real.rpow_nonneg hnR.le _)
  have hdrift0 := p5KnownScaleHtilde_drift_bound f r n hn1 δ t hδ cσ
    (midpointSampleHurst f hf.1 n) W (Cst * δ ^ p) (Clog * (n : ℝ) ^ (-(2 - 2 * b))) hE0
    hane hw1 hWabs hcontr' hlog
  rw [hcσ, sub_self, abs_zero, zero_add, ← hcσ] at hdrift0
  have hlog1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hexp : Real.exp (1 : ℝ) ≤ (n : ℝ) := by
      have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact Real.exp_one_lt_three.le.trans h3n
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ)) hexp
    rwa [Real.log_exp] at h
  have habso : (n : ℝ) ^ (-(2 - 2 * b)) ≤ (n : ℝ) ^ (-γ) :=
    (Real.rpow_le_rpow_left_iff hnR1).mpr (by linarith)
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 - 2 * b)) := Real.rpow_nonneg hnR.le _
  have hdiv : (n : ℝ) ^ (-(2 - 2 * b)) / Real.log (n : ℝ) ≤ (n : ℝ) ^ (-(2 - 2 * b)) := by
    have hlogpos : (0 : ℝ) < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
    have hinv : (Real.log (n : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ hlogpos).mpr hlog1
    rw [div_eq_mul_inv]
    calc (n : ℝ) ^ (-(2 - 2 * b)) * (Real.log (n : ℝ))⁻¹
        ≤ (n : ℝ) ^ (-(2 - 2 * b)) * 1 :=
          mul_le_mul_of_nonneg_left hinv hx0
      _ = (n : ℝ) ^ (-(2 - 2 * b)) := mul_one _
  have hW0 : (0 : ℝ) ≤ W :=
    le_trans (Finset.sum_nonneg fun j _ => abs_nonneg _) hWabs
  have hB : W * (Clog * (n : ℝ) ^ (-(2 - 2 * b))) / (2 * Real.log (n : ℝ))
      ≤ (Clog * W / 2) * (n : ℝ) ^ (-γ) := by
    calc W * (Clog * (n : ℝ) ^ (-(2 - 2 * b))) / (2 * Real.log (n : ℝ))
        = (Clog * W / 2) * ((n : ℝ) ^ (-(2 - 2 * b)) / Real.log (n : ℝ)) := by ring
      _ ≤ (Clog * W / 2) * (n : ℝ) ^ (-(2 - 2 * b)) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ (Clog * W / 2) * (n : ℝ) ^ (-γ) :=
          mul_le_mul_of_nonneg_left habso (by positivity)
  have hA : Cst * δ ^ p ≤ Cst * (n : ℝ) ^ (-γ) :=
    mul_le_mul_of_nonneg_left hδp hCst
  have hdrift : |(∫ x, p5KnownScaleHtilde f r n δ t cσ x ∂
        featureGaussian (actualQ1Obs f n (midpointSampleHurst f hf.1 n))) - f t|
      ≤ Cst * (n : ℝ) ^ (-γ) + (Clog * W / 2) * (n : ℝ) ^ (-γ) :=
    hdrift0.trans (add_le_add hA hB)
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
  have henv := knownScaleEstimator_bias_envelope hXm hX hbandc (f t)
    (F * (n : ℝ) ^ (-γ))
    (Cst * (n : ℝ) ^ (-γ) + (Clog * W / 2) * (n : ℝ) ^ (-γ)) hfluct hdrift
  exact henv.trans_eq (by ring)

/-! ## The window infeasibility audit (§3 of the task book, both orders) -/

/-- **The first-order window audit.**  On the long-memory band `3/4 < f t`
with `f t ≤ b`, the first-order window `f t ≤ 1 - b` is contradictory:
it forces `f t ≤ 1/2`. -/
theorem bias_window_firstOrder_infeasible {ft b : ℝ} (hlong : 3 / 4 < ft)
    (hftb : ft ≤ b) : ¬ (ft ≤ 1 - b) := by
  intro h
  nlinarith

/-- **The second-order window audit.**  On the long-memory band `3/4 < f t`
with `f t ≤ b`, even the second-order window `f t ≤ 2 - 2*b` is
contradictory: it forces `f t ≤ 2/3`.  This is the formal registration of
the takeover9 honest verdict: the per-row log route cannot reach the
endpoint rate `γ = f t`, at first OR second order. -/
theorem bias_window_secondOrder_infeasible {ft b : ℝ} (hlong : 3 / 4 < ft)
    (hftb : ft ≤ b) : ¬ (ft ≤ 2 - 2 * b) := by
  intro h
  nlinarith

end Hurst

#print axioms Hurst.gridStrideFirstActual_logNormSq_secondOrder
#print axioms Hurst.knownScaleEstimator_bias_envelope_grid_secondOrder
#print axioms Hurst.bias_window_firstOrder_infeasible
#print axioms Hurst.bias_window_secondOrder_infeasible
