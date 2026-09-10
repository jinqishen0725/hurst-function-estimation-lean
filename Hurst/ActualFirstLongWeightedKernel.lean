import Hurst.ActualFirstLongHilbertSchmidtClosed
import Hurst.ActiveWeightProfile
import Hurst.FirstLongWeightedKernel

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- The actual q=1 covariance step kernel after multiplication by the signed
local-polynomial weights converges in Hilbert--Schmidt energy to the weighted
discrete Riesz kernel.  This is the full model-specific operator input for a
second-chaos argument. -/
theorem hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz
    (p a b M : ℝ) (r : ℕ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
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
        let S := (n : ℝ) * δ n
        let psi := 2 - 2 * f t
        realScaleMeshEnergy S (fun i j =>
          (S * localPolynomialWeights r n 1 (δ n) t
              (localWeightActiveIndex n 1 (δ n) t i)) *
              q1ActualLongActiveKernel f hf n (δ n) t S psi i j -
            equivalentKernel r
              (2 * (((i.val + 1 : ℕ) : ℝ) /
                ((localWeightActiveSet n 1 (δ n) t).card : ℝ)) - 1) *
              q1RieszActiveKernel n (δ n) t S psi
                (f t * (2 * f t - 1)) i j)
        ) atTop (𝓝 0) := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hraw⟩ :=
    hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz_closed
      p a b M hp ha hb hab hM f hf hF t ht hlong
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  intro δ R hδpos hδ0 hS hR hcut henv
  let m := fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card
  let S := fun n : ℕ => (n : ℝ) * δ n
  let psi := 2 - 2 * f t
  let c := f t * (2 * f t - 1)
  let A := fun n : ℕ => q1ActualLongActiveKernel f hf n (δ n) t (S n) psi
  let B := fun n : ℕ => q1RieszActiveKernel n (δ n) t (S n) psi c
  let u := fun n : ℕ => fun i : Fin (m n) =>
    S n * localPolynomialWeights r n 1 (δ n) t
      (localWeightActiveIndex n 1 (δ n) t i)
  let v := fun n : ℕ => fun i : Fin (m n) =>
    equivalentKernel r
      (2 * (((i.val + 1 : ℕ) : ℝ) / (m n : ℝ)) - 1)
  obtain ⟨D, hD, hDbound⟩ := equivalentKernel_bounded r
  let U := D + 1
  have huv : ∀ eps > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n),
      |u n i - v n i| ≤ eps := by
    intro eps heps
    simpa only [m, S, u, v] using
      (localPolynomialWeights_active_rank_uniform_tendsto
        r 1 t ht δ hδpos hδ0 hS eps heps)
  have hu : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n), |u n i| ≤ U := by
    filter_upwards [huv 1 zero_lt_one] with n hn
    intro i
    have htri : |u n i| ≤ |u n i - v n i| + |v n i| := by
      have heq : u n i = (u n i - v n i) + v n i := by ring
      calc
        |u n i| = |(u n i - v n i) + v n i| := congrArg abs heq
        _ ≤ |u n i - v n i| + |v n i| :=
          abs_add_le (u n i - v n i : ℝ) (v n i)
    have hvbound : |v n i| ≤ D := by
      dsimp only [v]
      exact hDbound
        (2 * (((i.val + 1 : ℕ) : ℝ) / (m n : ℝ)) - 1)
    calc
      |u n i| ≤ |u n i - v n i| + |v n i| := htri
      _ ≤ 1 + D := add_le_add (hn i) hvbound
      _ = U := by dsimp only [U]; ring
  have hAB : Tendsto (fun n => realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j)) atTop (𝓝 0) := by
    simpa only [S, psi, c, A, B] using
      hraw δ R hδpos hδ0 hS hR hcut henv
  let Cref := 2 * c ^ 2 *
    (3 + 3 * 4 ^ (1 - 2 * psi) / (1 - 2 * psi))
  have hpsi0 : 0 ≤ psi := by
    dsimp only [psi]
    have hfb : f t ≤ b := (hF ht).2
    linarith
  have hpsihalf : psi < 1 / 2 := by
    dsimp only [psi]
    linarith
  have hCref : 0 ≤ Cref := by
    dsimp only [Cref]
    have hden : 0 < 1 - 2 * psi := by linarith
    positivity
  have hgeom := localWeightActiveSet_card_ratio_tendsto_two
    1 t ht δ hδpos hδ0 hS
  have hcardpos : ∀ᶠ n in atTop, 0 < m n := by
    simpa only [m] using hgeom.1
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hBbound : ∀ᶠ n in atTop,
      realScaleMeshEnergy (S n) (B n) ≤ Cref := by
    filter_upwards [hnpos, hδpos, hcardpos, hS.eventually_ge_atTop 1]
      with n hn hδ hcard hS1
    have hm : (m n : ℝ) ≤ 3 * S n := by
      dsimp only [m, S]
      exact localWeightActiveSet_card n 1 hn (δ n) t hδ hS1
    have hSn : 0 < S n := zero_lt_one.trans_le hS1
    dsimp only [B]
    rw [q1RieszActiveKernel_eq_rankRieszKernel n hn (δ n) t
      (S n) psi c hδ hSn hcard]
    exact rankRieszKernel_energy_le_const (S n) psi c hS1 hm
      hpsi0 hpsihalf
  have hweighted := realScaleMeshEnergy_left_weight_sub_tendsto_zero
    m S A B u v U Cref hCref hu huv hAB hBbound
  simpa only [m, S, psi, c, A, B, u, v] using hweighted

end Hurst
