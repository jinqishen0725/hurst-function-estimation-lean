import Hurst.FirstLongRealScaleHilbertSchmidt
import Hurst.ActualFirstLongQuadraticReindex

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- The number of nonzero local-polynomial weights is at most three times the
effective local sample size. -/
theorem localWeightActive_card_div_effective_le_three
    (q : ℕ) (δ : ℕ → ℝ) (t : ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ᶠ n in atTop,
      ((localWeightActiveSet n q (δ n) t).card : ℝ) /
          ((n : ℝ) * δ n) ≤ 3 := by
  filter_upwards [hδpos, hN.eventually_ge_atTop 1,
      eventually_ge_atTop (q + 1)] with n hδ hN1 hn
  have hn0 : 0 < n := by omega
  have hcard := localWeightActiveSet_card n q hn0 (δ n) t hδ hN1
  exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) * δ n)).2 (by
    simpa only [Nat.cast_ofNat] using hcard)

/-- The near-diagonal Hilbert--Schmidt energy of the actual q=1 correlation
step kernel vanishes under the explicit deterministic cutoff rate. -/
theorem hurstHolder_q1_actual_correlation_band_energy_tendsto_zero
    (p a b M h ψ : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (δ : ℕ → ℝ) (R : ℕ → ℕ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * ψ - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      realScaleMeshBandEnergy ((n : ℝ) * δ n) (R n)
        (fun i j => ((n : ℝ) * δ n) ^ ψ *
          vectorCorrelation
            (gridStrideFirstActual n 1
              (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 (δ n) t i))
            (gridStrideFirstActual n 1
              (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 (δ n) t j))))
      atTop (𝓝 0) := by
  apply realScaleMeshBandEnergy_scaled_tendsto_zero
      (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card) R
      (fun n : ℕ => (n : ℝ) * δ n) ψ
      (fun n : ℕ => fun i j => vectorCorrelation
        (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 (δ n) t i))
        (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 (δ n) t j)))
  · exact (hN.eventually_gt_atTop 0)
  · exact Eventually.of_forall fun n i j => vectorCorrelation_abs_le_one _ _
  · exact hcut

end Hurst
