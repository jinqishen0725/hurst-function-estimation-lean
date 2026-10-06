import Hurst.NormalizedLogVariance
import Hurst.P5L1Joining

/-!
# Clipping under normalized correlation energy

This consumes the corrected variance bound directly. It does not require the
unnormalized total correlation energy to stay bounded. The center-band condition
is kept explicit: identifying the statistical center is a separate model step.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem normalized_logProjection_L1_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℕ) (v : (n : ℕ) → Fin n → E)
    (u : (n : ℕ) → Fin (m n) → ℝ)
    (a : (n : ℕ) → Fin (m n) → EuclideanSpace ℝ (Fin n))
    (S L : ℕ → ℝ) {ψ U C d : ℝ} (cσ : ℝ)
    (hψ : 0 < ψ) (hU : 0 ≤ U) (hd : 0 < d)
    (hS : Tendsto S atTop atTop) (hL : Tendsto L atTop atTop)
    (ha : ∀ n j, ∑ i, a n j i • v n i ≠ 0)
    (hu : ∀ᶠ n in atTop, ∀ j, |u n j| ≤ U)
    (hE : ∀ᶠ n in atTop, S n ^ (2 * ψ - 2) *
      (∑ j, ∑ k, featureCorrelation (v n) (a n j) (a n k) ^ 2) ≤ C)
    (hband : ∀ᶠ n in atTop,
      d ≤ (cσ - ∫ y, gaussianLogStatistic (fun j => (S n)⁻¹ * u n j) (a n) y
        ∂featureGaussian (v n)) / (2 * L n) ∧
      (cσ - ∫ y, gaussianLogStatistic (fun j => (S n)⁻¹ * u n j) (a n) y
        ∂featureGaussian (v n)) / (2 * L n) ≤ 1 - d) :
    let G := fun n => gaussianLogStatistic (fun j => (S n)⁻¹ * u n j) (a n)
    Tendsto (fun n => ∫ x,
      |(2 * S n ^ ψ * L n) * (p5Trunc01 ((cσ - G n x) / (2 * L n))
          - ∫ y, p5Trunc01 ((cσ - G n y) / (2 * L n)) ∂featureGaussian (v n))
        - (2 * S n ^ ψ * L n) * ((cσ - G n x) / (2 * L n)
          - ∫ y, (cσ - G n y) / (2 * L n) ∂featureGaussian (v n))|
        ∂featureGaussian (v n)) atTop (𝓝 0) := by
  let G := fun n => gaussianLogStatistic (fun j => (S n)⁻¹ * u n j) (a n)
  let K : ℝ := 4 * gaussianLogSquareVariance * U ^ 2 * C
  have hMem : ∀ n, MemLp (G n) 2 (featureGaussian (v n)) := fun n =>
    gaussianLogStatistic_memLp_two (v n) (fun j => (S n)⁻¹ * u n j) (a n) (ha n)
  have hMom : ∀ᶠ n in atTop,
      (∫ x, (G n x - ∫ y, G n y ∂featureGaussian (v n)) ^ 2
        ∂featureGaussian (v n)) ≤ K * S n ^ (-(2 * ψ)) := by
    filter_upwards [hS.eventually_gt_atTop 0, hu, hE] with n hn hUn hEn
    have hvar := gaussianLogStatistic_variance_of_normalizedEnergy
      (v n) (u n) (a n) (ha n) hn hU hUn hEn
    have hmean := gaussianLogStatistic_mse (v n)
      (fun j => (S n)⁻¹ * u n j) (a n)
      (∫ y, G n y ∂featureGaussian (v n)) (ha n)
    have heq : (∫ x, (G n x - ∫ y, G n y ∂featureGaussian (v n)) ^ 2
        ∂featureGaussian (v n)) = Var[G n; featureGaussian (v n)] := by
      simpa only [G, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hmean
    rw [heq]
    exact hvar
  exact logProjection_L1_tendsto_zero
    (fun n => featureGaussian (v n)) G cσ (fun n => S n ^ ψ) L (fun _ => d)
    (fun n => K * S n ^ (-(2 * ψ))) hMem hMom
    (hL.eventually_gt_atTop 0)
    ((hS.eventually_gt_atTop 0).mono fun n hn => Real.rpow_nonneg hn.le _)
    (Eventually.of_forall fun _ => hd) hband
    (normalized_variance_clipping_window S L K hψ hd hS hL)

end Hurst
