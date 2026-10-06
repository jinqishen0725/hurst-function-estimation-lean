import Hurst.NormalizedActualEnergy
import Hurst.ActiveWeightProfile

/-!
# Actual q1 weighted fourth-correlation energy

The normalized energy, scaled local-weight bound, and distant-correlation
bound are discharged internally. The only extra rate input is the existing
scalar tail-envelope convergence, stated for every fixed admissible set of
constants. This deliberately keeps independent existential witnesses from
the HS and tail theorems separate.
-/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

def q1ActiveCorrelation (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (n : ℕ) (δ t : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) : ℝ :=
  vectorCorrelation
    (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 δ t i))
    (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 δ t j))

/-- The literal absolute-weight fourth energy, with the original local
polynomial weights and the long-memory normalization. -/
def q1ActiveWeightedFourthEnergy (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r n : ℕ) (δ t : ℝ) : ℝ :=
  ((n : ℝ) * δ) ^ (2 * (2 - 2 * f t)) *
    ∑ i : Fin (localWeightActiveSet n 1 δ t).card,
      ∑ j : Fin (localWeightActiveSet n 1 δ t).card,
        |localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t i) *
          localPolynomialWeights r n 1 δ t (localWeightActiveIndex n 1 δ t j)| *
        |q1ActiveCorrelation f hf n δ t i j| ^ 4

/-- The full-row equivalent-kernel approximation provides a fixed bound on
scaled weights, also for signed higher-order local-polynomial weights. -/
theorem localPolynomialWeights_scaled_eventually_bounded
    (r q : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    ∃ U ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (n - q),
      |((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t i| ≤ U := by
  obtain ⟨D, hD, hDbound⟩ := equivalentKernel_bounded r
  refine ⟨D + 1, by linarith, ?_⟩
  filter_upwards [localPolynomialWeights_scaled_uniform_tendsto
    r q t ht δ hδpos hδ0 hN 1 zero_lt_one] with n hn
  intro i
  have htri := abs_add_le
    (((n : ℝ) * δ n) * localPolynomialWeights r n q (δ n) t i -
      equivalentKernel r ((grid n i.val - t) / δ n))
    (equivalentKernel r ((grid n i.val - t) / δ n))
  simp only [sub_add_cancel] at htri
  linarith [hn i, hDbound ((grid n i.val - t) / δ n)]

/-- **Actual E3/W8 energy:** all signed local-polynomial weights are allowed.
There is no assumed normalized-energy bound or fourth-energy convergence.
The `hEnv` quantifier covers two independently obtained sets of fixed
constants rather than identifying their existential witnesses. -/
theorem hurstHolder_q1_actual_weighted_fourth_tendsto_zero
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (r : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (R : ℕ → ℕ)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hR : Tendsto (fun n => (R n : ℝ)) atTop atTop)
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (hEnv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0,
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n) (R n)) atTop (𝓝 0)) :
    Tendsto (fun n => q1ActiveWeightedFourthEnergy f hf r n (δ n) t)
      atTop (𝓝 0) := by
  let S := fun n : ℕ => (n : ℝ) * δ n
  let m := fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card
  let ψ := 2 - 2 * f t
  let c := f t * (2 * f t - 1)
  let ρ := fun n => q1ActiveCorrelation f hf n (δ n) t
  let w := fun n => fun i : Fin (m n) => localPolynomialWeights r n 1 (δ n) t
    (localWeightActiveIndex n 1 (δ n) t i)
  let u := fun n => fun i : Fin (m n) => S n * w n i
  have hψ : 0 < ψ := by
    dsimp [ψ]
    have hfb := (hF ht).2
    linarith
  have hRn : ∀ᶠ n : ℕ in atTop, 1 ≤ R n := by
    filter_upwards [hR.eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  obtain ⟨A, hA, B, hB, L₀, hL₀, C, hC, hEnergy⟩ :=
    hurstHolder_q1_actual_normalized_energy_eventually_bounded
      p a b M hp ha hb hab hM f hf hF t ht hlong
  have hE : ∀ᶠ n : ℕ in atTop,
      S n ^ (2 * ψ - 2) * ∑ i, ∑ j, ρ n i j ^ 2 ≤ C :=
    hEnergy δ R hδpos hδ0 hN hRn hcut (hEnv A hA B hB L₀ hL₀)
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hTail⟩ :=
    hurstHolder_q1_active_scaled_actual_tail_error_le_envelope
      p a b M hp ha hb hab hM f hf hF t ht
  let η := fun n => q1ActualLongTailEnvelope b Ccov Ctail L M (f t)
    n (δ n) (S n) (R n)
  let ε := fun n => (|c| + |η n|) * (R n : ℝ) ^ (-ψ)
  have hη : Tendsto η atTop (𝓝 0) := hEnv Ccov hCcov Ctail hCtail L hL
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    scaled_tail_envelope_tendsto_zero (fun n => (R n : ℝ)) η ψ c hψ hR hη
  have hε : ∀ᶠ n : ℕ in atTop, 0 ≤ ε n := Eventually.of_forall fun n =>
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsmall : ∀ᶠ n : ℕ in atTop, gridCovarianceError b Ccov n ≤ 1 / 2 :=
    (gridCovarianceError_tendsto b Ccov hb).eventually_le_const (by norm_num)
  have hcard := (localWeightActiveSet_card_ratio_tendsto_two
    1 t ht δ hδpos hδ0 hN).1
  have hfar : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin (m n),
      R n < Nat.dist j.val i.val → |ρ n i j| ≤ ε n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hδpos, hRn, hsmall, hcard]
      with n hn hδ hRn' hsmall' hcard'
    intro i j hij
    have hn0 : 0 < n := by omega
    have hd := localWeightActiveIndex_physical_dist_eq_rank_dist
      n 1 hn0 (δ n) t hδ hcard' i j
    have hdist : R n < Nat.dist
        (localWeightActiveIndex n 1 (δ n) t i).val
        (localWeightActiveIndex n 1 (δ n) t j).val := by
      rw [hd, Nat.dist_comm]
      exact hij
    have ht := hTail n hn (δ n) (S n) hδ rfl (R n) hRn' hsmall' i j hdist
    rw [hd, Nat.dist_comm i.val j.val] at ht
    have hRpos : (0 : ℝ) < R n := by exact_mod_cast (by omega : 0 < R n)
    have hRd : (R n : ℝ) ≤ (Nat.dist j.val i.val : ℝ) := by exact_mod_cast hij.le
    exact correlation_le_of_scaled_tail (Nat.dist j.val i.val : ℝ)
      (R n : ℝ) ψ c (η n) (ρ n i j) hRpos hRd hψ.le ht
  obtain ⟨U, hU, hUw⟩ := localPolynomialWeights_scaled_eventually_bounded
    r 1 t ht δ hδpos hδ0 hN
  have hu : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m n), |u n i| ≤ U := by
    filter_upwards [hUw] with n hn
    intro i
    exact hn (localWeightActiveIndex n 1 (δ n) t i)
  have hρ : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin (m n), |ρ n i j| ≤ 1 :=
    Eventually.of_forall fun n i j => vectorCorrelation_abs_le_one _ _
  have hSpos : ∀ᶠ n : ℕ in atTop, 0 < S n := hN.eventually_gt_atTop 0
  have hfour := normalized_weighted_fourth_tendsto_zero m R S ε ψ U C ρ u
    hSpos hU hu hρ hε hfar hE hcut hε0
  apply hfour.congr'
  filter_upwards [hSpos] with n hSn
  have hscale := normalized_weighted_fourth_eq_original (S n) ψ hSn (w n) (ρ n)
  have hpow : (S n ^ ψ) ^ (2 : ℕ) = S n ^ (2 * ψ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hSn.le]
    congr 1
    norm_num
    ring
  rw [hpow] at hscale
  exact hscale

end Hurst

#print axioms Hurst.localPolynomialWeights_scaled_eventually_bounded
#print axioms Hurst.hurstHolder_q1_actual_weighted_fourth_tendsto_zero
