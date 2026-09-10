import Hurst.FirstLongRieszEnergy

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Fully internal q=1 actual-to-discrete-Riesz Hilbert--Schmidt convergence.
The remaining scalar hypotheses are the bandwidth/cutoff rates themselves;
the Riesz reference energy estimates are proved in `FirstLongRieszEnergy`. -/
theorem hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t) :
    ∃ Ccov ≥ 0, ∃ Ctail ≥ 0, ∃ L > 0,
      ∀ (δ : ℕ → ℝ) (R : ℕ → ℕ),
      (∀ᶠ n in atTop, 0 < δ n) →
      Tendsto δ atTop (𝓝 0) →
      Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop →
      (∀ᶠ n in atTop, 1 ≤ R n) →
      Tendsto (fun n : ℕ =>
        ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          (2 * (R n : ℝ) + 1)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n) (R n)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ =>
        realScaleMeshEnergy ((n : ℝ) * δ n)
          (fun i j =>
            q1ActualLongActiveKernel f hf n (δ n) t
                ((n : ℝ) * δ n) (2 - 2 * f t) i j -
              q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n)
                (2 - 2 * f t) (f t * (2 * f t - 1)) i j))
        atTop (𝓝 0) := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hmain⟩ :=
    hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz
      p a b M hp ha hb hab hM f hf hF t ht hlong
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  intro δ R hδpos hδ0 hN hR hcut hEnv
  let S := fun n : ℕ => (n : ℝ) * δ n
  let m := fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card
  let ψ := 2 - 2 * f t
  let c := f t * (2 * f t - 1)
  let Cref := 2 * c ^ 2 * (3 + 3 * 4 ^ (1 - 2 * ψ) / (1 - 2 * ψ))
  have hψ0 : 0 ≤ ψ := by
    dsimp only [ψ]
    have hfb : f t ≤ b := (hF ht).2
    linarith
  have hψhalf : ψ < 1 / 2 := by
    dsimp only [ψ]
    linarith
  have hCref : 0 ≤ Cref := by
    dsimp only [Cref]
    have hden : 0 < 1 - 2 * ψ := by linarith
    positivity
  have hgeom := localWeightActiveSet_card_ratio_tendsto_two
    1 t ht δ hδpos hδ0 hN
  have hcardpos : ∀ᶠ n in atTop, 0 < m n := by
    simpa only [m] using hgeom.1
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hSpos : ∀ᶠ n in atTop, 0 < S n := hN.eventually_gt_atTop 0
  have hBnear : Tendsto (fun n : ℕ =>
      realScaleMeshBandEnergy (S n) (R n)
        (q1RieszActiveKernel n (δ n) t (S n) ψ c)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ => c ^ 2 *
        (S n ^ (2 * ψ - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1)))
        atTop (𝓝 0) := by
      have hc := hcut.const_mul (c ^ 2)
      simpa only [S, m, ψ, mul_zero] using hc
    apply squeeze_zero' (g := fun n : ℕ => c ^ 2 *
      (S n ^ (2 * ψ - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1)))
    · exact Eventually.of_forall fun n => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    · filter_upwards [hnpos, hδpos, hSpos, hcardpos] with n hn hδ hSn hcard
      rw [q1RieszActiveKernel_eq_rankRieszKernel n hn (δ n) t (S n) ψ c
        hδ hSn hcard]
      exact rankRieszKernel_band_energy_le (S n) ψ c hSn hψ0
    · exact hupper
  have hBbound : ∀ᶠ n in atTop,
      realScaleMeshEnergy (S n)
        (q1RieszActiveKernel n (δ n) t (S n) ψ c) ≤ Cref := by
    filter_upwards [hnpos, hδpos, hcardpos, hN.eventually_ge_atTop 1]
      with n hn hδ hcard hS1
    have hm : (m n : ℝ) ≤ 3 * S n := by
      dsimp only [m, S]
      exact localWeightActiveSet_card n 1 hn (δ n) t hδ hS1
    have hSn : 0 < S n := zero_lt_one.trans_le hS1
    rw [q1RieszActiveKernel_eq_rankRieszKernel n hn (δ n) t (S n) ψ c
      hδ hSn hcard]
    exact rankRieszKernel_energy_le_const (S n) ψ c hS1 hm hψ0 hψhalf
  exact hmain δ R hδpos hN hR hcut hEnv Cref hCref
    (by simpa only [S, ψ, c] using hBnear)
    (by simpa only [S, ψ, c, Cref] using hBbound)

end Hurst
