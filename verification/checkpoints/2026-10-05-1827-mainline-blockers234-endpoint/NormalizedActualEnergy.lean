import Hurst.NormalizedHermiteEnergy
import Hurst.ActualFirstLongHilbertSchmidtClosed

/-!
# Bounded normalized energy of the actual q1 correlations

The actual-to-Riesz mesh error and the unweighted Riesz reference energy
supply `S^(2ψ-2) ∑ ρ² = O(1)`. No unnormalized square-sum bound, signed
quadratic-form variance bound, or target energy bound is assumed.
-/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- The unweighted Riesz reference has uniformly bounded mesh energy on the
actual active window. Only eventual nonempty windows are used. -/
theorem q1RieszActiveKernel_eventually_energy_le
    (t ψ c : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hψ0 : 0 ≤ ψ) (hψhalf : ψ < 1 / 2)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n) ψ c) ≤
      2 * c ^ 2 * (3 + 3 * 4 ^ (1 - 2 * ψ) / (1 - 2 * ψ)) := by
  have hcardpos := (localWeightActiveSet_card_ratio_tendsto_two
    1 t ht δ hδpos hδ0 hN).1
  filter_upwards [eventually_gt_atTop (0 : ℕ), hδpos, hcardpos,
    hN.eventually_ge_atTop 1] with n hn hδ hcard hS1
  have hm : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≤
      3 * ((n : ℝ) * δ n) :=
    localWeightActiveSet_card n 1 hn (δ n) t hδ hS1
  have hSn : 0 < (n : ℝ) * δ n := zero_lt_one.trans_le hS1
  rw [q1RieszActiveKernel_eq_rankRieszKernel n hn (δ n) t
    ((n : ℝ) * δ n) ψ c hδ hSn hcard]
  exact rankRieszKernel_energy_le_const ((n : ℝ) * δ n) ψ c hS1 hm hψ0 hψhalf

/-- The actual unweighted normalized second energy is eventually bounded.
The existential covariance/tail constants are the same witnesses returned by
the internally proved HS convergence theorem. Remaining assumptions are only
the scalar bandwidth/cutoff rates already required by that theorem. -/
theorem hurstHolder_q1_actual_normalized_energy_eventually_bounded
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t) :
    ∃ Ccov ≥ 0, ∃ Ctail ≥ 0, ∃ L > 0, ∃ C ≥ 0,
      ∀ (δ : ℕ → ℝ) (R : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop, 0 < δ n) →
      Tendsto δ atTop (𝓝 0) →
      Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop →
      (∀ᶠ n : ℕ in atTop, 1 ≤ R n) →
      Tendsto (fun n : ℕ =>
        ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          (2 * (R n : ℝ) + 1)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n) (R n)) atTop (𝓝 0) →
      ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
          (∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
            ∑ j : Fin (localWeightActiveSet n 1 (δ n) t).card,
              (vectorCorrelation
                (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 (δ n) t i))
                (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
                  (localWeightActiveIndex n 1 (δ n) t j))) ^ 2) ≤ C := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hHS⟩ :=
    hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed
      p a b M hp ha hb hab hM f hf hF t ht hlong
  let ψ := 2 - 2 * f t
  let c := f t * (2 * f t - 1)
  let Cref := 2 * c ^ 2 * (3 + 3 * 4 ^ (1 - 2 * ψ) / (1 - 2 * ψ))
  have hψ0 : 0 ≤ ψ := by
    dsimp [ψ]
    have hfb : f t ≤ b := (hF ht).2
    linarith
  have hψhalf : ψ < 1 / 2 := by dsimp [ψ]; linarith
  have hCref : 0 ≤ Cref := by
    dsimp [Cref]
    have hden : 0 < 1 - 2 * ψ := by linarith
    positivity
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, 2 + 2 * Cref, by positivity, ?_⟩
  intro δ R hδpos hδ0 hN hR hcut hEnv
  let m := fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card
  let S := fun n : ℕ => (n : ℝ) * δ n
  let A := fun n => q1ActualLongActiveKernel f hf n (δ n) t (S n) ψ
  let B := fun n => q1RieszActiveKernel n (δ n) t (S n) ψ c
  have herror : Tendsto (fun n => realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j)) atTop (𝓝 0) :=
    hHS δ R hδpos hδ0 hN hR hcut hEnv
  have hB : ∀ᶠ n : ℕ in atTop, realScaleMeshEnergy (S n) (B n) ≤ Cref :=
    q1RieszActiveKernel_eventually_energy_le t ψ c ht hψ0 hψhalf δ hδpos hδ0 hN
  have henergy := realScaleMeshEnergy_eventually_bounded_of_approximation
    m S A B Cref herror hB
  filter_upwards [henergy, hN.eventually_gt_atTop 0] with n hn hSn
  change realScaleMeshEnergy (S n) (fun i j => S n ^ ψ *
    vectorCorrelation
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
        (localWeightActiveIndex n 1 (δ n) t i))
      (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
        (localWeightActiveIndex n 1 (δ n) t j))) ≤ 2 + 2 * Cref at hn
  rw [realScaleMeshEnergy_scaled_eq (S n) ψ hSn] at hn
  exact hn

end Hurst

#print axioms Hurst.q1RieszActiveKernel_eventually_energy_le
#print axioms Hurst.hurstHolder_q1_actual_normalized_energy_eventually_bounded
