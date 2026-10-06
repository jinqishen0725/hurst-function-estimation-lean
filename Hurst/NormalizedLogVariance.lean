import Hurst.GaussianLogRisk
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Log variance from normalized correlation energy

The unit weights are `S⁻¹ * u i`, with bounded scaled weights `u`.  The
correlation energy supplied here is `S^(2ψ-2) * ∑ᵢⱼ ρᵢⱼ²`, not the generally
divergent unnormalized sum.  This supplies the variance estimate required
by the projection/clipping step of the long-memory repair.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem gaussianLogStatistic_variance_uniformWeight_bound
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j, ∑ i, a j i • v i ≠ 0)
    {A : ℝ} (hA : 0 ≤ A) (hw : ∀ j, |w j| ≤ A) :
    Var[gaussianLogStatistic w a; featureGaussian v] ≤
      4 * gaussianLogSquareVariance * A ^ 2 *
        (∑ j, ∑ k, featureCorrelation v (a j) (a k) ^ 2) := by
  refine (gaussianLogStatistic_variance_correlation_bound v w a ha).trans ?_
  have hsum : (∑ j, ∑ k, |w j| * |w k| * featureCorrelation v (a j) (a k) ^ 2)
      ≤ A ^ 2 * (∑ j, ∑ k, featureCorrelation v (a j) (a k) ^ 2) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [pow_two] using
      mul_le_mul (hw j) (hw k) (abs_nonneg _) hA
  have := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) gaussianLogSquareVariance_nonneg)
  simpa only [mul_assoc] using this

/-- The normalized second-order correlation energy controls the scaled
variance of the actual unit-weight log statistic, allowing signed weights. -/
theorem gaussianLogStatistic_scaled_variance_of_normalizedEnergy
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (u : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j, ∑ i, a j i • v i ≠ 0)
    {S ψ U C : ℝ} (hS : 0 < S) (hU : 0 ≤ U) (hu : ∀ j, |u j| ≤ U)
    (hE : S ^ (2 * ψ - 2) *
      (∑ j, ∑ k, featureCorrelation v (a j) (a k) ^ 2) ≤ C) :
    S ^ (2 * ψ) *
      Var[gaussianLogStatistic (fun j => S⁻¹ * u j) a; featureGaussian v] ≤
        4 * gaussianLogSquareVariance * U ^ 2 * C := by
  have hb := gaussianLogStatistic_variance_uniformWeight_bound v
    (fun j => S⁻¹ * u j) a ha (mul_nonneg (inv_nonneg.mpr hS.le) hU)
    (fun j => by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hS)]
      exact mul_le_mul_of_nonneg_left (hu j) (inv_nonneg.mpr hS.le))
  have hscale : S ^ (2 * ψ) * (S⁻¹) ^ 2 = S ^ (2 * ψ - 2) := by
    rw [Real.rpow_sub hS, Real.rpow_two, div_eq_mul_inv, inv_pow]
  calc
    _ ≤ S ^ (2 * ψ) * (4 * gaussianLogSquareVariance * (S⁻¹ * U) ^ 2 *
        (∑ j, ∑ k, featureCorrelation v (a j) (a k) ^ 2)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hS.le _)
    _ = (4 * gaussianLogSquareVariance * U ^ 2) *
        ((S ^ (2 * ψ) * (S⁻¹) ^ 2) *
          (∑ j, ∑ k, featureCorrelation v (a j) (a k) ^ 2)) := by ring
    _ = (4 * gaussianLogSquareVariance * U ^ 2) *
        (S ^ (2 * ψ - 2) *
          (∑ j, ∑ k, featureCorrelation v (a j) (a k) ^ 2)) := by rw [hscale]
    _ ≤ _ := mul_le_mul_of_nonneg_left hE
      (mul_nonneg (mul_nonneg (by norm_num) gaussianLogSquareVariance_nonneg)
        (sq_nonneg U))

/-- The variance estimate in the unscaled form consumed by clipping. -/
theorem gaussianLogStatistic_variance_of_normalizedEnergy
    {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (u : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (ha : ∀ j, ∑ i, a j i • v i ≠ 0)
    {S ψ U C : ℝ} (hS : 0 < S) (hU : 0 ≤ U) (hu : ∀ j, |u j| ≤ U)
    (hE : S ^ (2 * ψ - 2) *
      (∑ j, ∑ k, featureCorrelation v (a j) (a k) ^ 2) ≤ C) :
    Var[gaussianLogStatistic (fun j => S⁻¹ * u j) a; featureGaussian v] ≤
      (4 * gaussianLogSquareVariance * U ^ 2 * C) * S ^ (-(2 * ψ)) := by
  have h := gaussianLogStatistic_scaled_variance_of_normalizedEnergy v u a ha hS hU hu hE
  rw [Real.rpow_neg hS.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hS _)).mpr
  simpa only [mul_comm] using h

/-- With normalized energy, the clipping window vanishes for every positive
long-memory exponent; no unnormalized correlation-energy bound is needed. -/
theorem normalized_variance_clipping_window
    (S L : ℕ → ℝ) {ψ d : ℝ} (C : ℝ) (hψ : 0 < ψ) (hd : 0 < d)
    (hS : Tendsto S atTop atTop) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => S n ^ ψ * (C * S n ^ (-(2 * ψ))) / (L n * d))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun n => S n ^ (-ψ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hψ).comp hS
  have hnum : Tendsto (fun n => C * S n ^ (-ψ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul C
  have h := hnum.div_atTop (hL.atTop_mul_const hd)
  apply h.congr'
  filter_upwards [hS.eventually_gt_atTop 0] with n hn
  congr 1
  calc C * S n ^ (-ψ) = C * S n ^ (ψ + -(2 * ψ)) := by ring_nf
    _ = C * (S n ^ ψ * S n ^ (-(2 * ψ))) := by rw [Real.rpow_add hn]
    _ = S n ^ ψ * (C * S n ^ (-(2 * ψ))) := by ring

end Hurst
