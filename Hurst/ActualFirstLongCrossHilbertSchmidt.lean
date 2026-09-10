import Hurst.ActualFirstLongCrossCorrelation
import Hurst.ActualFirstLongHilbertSchmidtClosed

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- The actual cross-correlation kernel of two first-increment strides, both
restricted to the common `Fin (n-2)` pilot window. -/
def q1ActualCrossLongActiveKernel
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (d e : ℕ) (hd : d ≤ 2) (he : e ≤ 2)
    (n : ℕ) (δ t S psi : ℝ)
    (i j : Fin (localWeightActiveSet n 2 δ t).card) : ℝ :=
  S ^ psi * vectorCorrelation
    (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n)
      (commonFirstStrideIndex n d 2 hd
        (localWeightActiveIndex n 2 δ t i)))
    (gridStrideFirstActual n e (midpointSampleHurst f hf.1 n)
      (commonFirstStrideIndex n e 2 he
        (localWeightActiveIndex n 2 δ t j)))

/-- Discrete Riesz reference on the common q=2 active window. -/
def q1CrossRieszActiveKernel
    (n : ℕ) (δ t S psi c : ℝ)
    (i j : Fin (localWeightActiveSet n 2 δ t).card) : ℝ :=
  if Nat.dist
      (localWeightActiveIndex n 2 δ t i).val
      (localWeightActiveIndex n 2 δ t j).val = 0 then 0
  else c * (S / (Nat.dist
      (localWeightActiveIndex n 2 δ t i).val
      (localWeightActiveIndex n 2 δ t j).val : ℝ)) ^ psi

theorem q1CrossRieszActiveKernel_eq_rankRieszKernel
    (n : ℕ) (hn : 0 < n) (δ t S ψ c : ℝ) (hδ : 0 < δ)
    (hS : 0 < S) (hcard : 0 < (localWeightActiveSet n 2 δ t).card) :
    q1CrossRieszActiveKernel n δ t S ψ c =
      (rankRieszKernel S ψ c :
        Fin (localWeightActiveSet n 2 δ t).card →
          Fin (localWeightActiveSet n 2 δ t).card → ℝ) := by
  funext i j
  have hdist := localWeightActiveIndex_physical_dist_eq_rank_dist
    n 2 hn δ t hδ hcard i j
  unfold q1CrossRieszActiveKernel rankRieszKernel rankRieszUnitKernel
  rw [hdist]
  split_ifs with hzero
  · ring
  · have hk0 : (0 : ℝ) ≤ Nat.dist i.val j.val := by positivity
    rw [Real.div_rpow hS.le hk0, Real.rpow_neg hk0]
    rw [div_eq_mul_inv]
    ring

/-- Near-diagonal energy of an actual unequal-stride cross-correlation kernel
vanishes under the same scalar cutoff rate as in the one-stride proof. -/
theorem hurstHolder_q1_actual_cross_correlation_band_energy_tendsto_zero
    (p M : ℝ) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (d e : ℕ) (hd : d ≤ 2) (he : e ≤ 2)
    (t : ℝ) (δ : ℕ → ℝ) (R : ℕ → ℕ) (ψ : ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * ψ - 2) *
        ((localWeightActiveSet n 2 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      realScaleMeshBandEnergy ((n : ℝ) * δ n) (R n)
        (q1ActualCrossLongActiveKernel f hf d e hd he n (δ n) t
          ((n : ℝ) * δ n) ψ)) atTop (𝓝 0) := by
  apply realScaleMeshBandEnergy_scaled_tendsto_zero
      (fun n : ℕ => (localWeightActiveSet n 2 (δ n) t).card) R
      (fun n : ℕ => (n : ℝ) * δ n) ψ
      (fun n : ℕ => fun i j => vectorCorrelation
        (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n)
          (commonFirstStrideIndex n d 2 hd
            (localWeightActiveIndex n 2 (δ n) t i)))
        (gridStrideFirstActual n e (midpointSampleHurst f hf.1 n)
          (commonFirstStrideIndex n e 2 he
            (localWeightActiveIndex n 2 (δ n) t j))))
  · exact hN.eventually_gt_atTop 0
  · exact Eventually.of_forall fun n i j => vectorCorrelation_abs_le_one _ _
  · exact hcut

/-- Cross-stride Hilbert--Schmidt gluing on the actual q=1 pilot window.
All near-diagonal and Riesz-energy estimates are internal.  Its one remaining
input is precisely the uniform relative off-band tail estimate `hoff`. -/
theorem hurstHolder_q1_actual_cross_kernel_hilbertSchmidt_to_riesz_of_relative_tail
    (p M : ℝ) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (d e : ℕ) (hd0 : 0 < d) (he0 : 0 < e) (hd : d ≤ 2) (he : e ≤ 2)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (h0 : ℝ) (hh0 : 3 / 4 < h0) (hh01 : h0 < 1)
    (δ : ℕ → ℝ) (R : ℕ → ℕ) (err : ℕ → ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hcut : Tendsto (fun n : ℕ =>
      ((n : ℝ) * δ n) ^ (2 * (2 - 2 * h0) - 2) *
        ((localWeightActiveSet n 2 (δ n) t).card : ℝ) *
        (2 * (R n : ℝ) + 1)) atTop (𝓝 0))
    (herr0 : ∀ᶠ n in atTop, 0 ≤ err n)
    (herr : Tendsto err atTop (𝓝 0))
    (hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val →
        |q1ActualCrossLongActiveKernel f hf d e hd he n (δ n) t
              ((n : ℝ) * δ n) (2 - 2 * h0) i j -
          q1CrossRieszActiveKernel n (δ n) t ((n : ℝ) * δ n)
              (2 - 2 * h0) (firstLongTwoStrideConstant h0 d e) i j| ≤
          err n * |q1CrossRieszActiveKernel n (δ n) t
              ((n : ℝ) * δ n) (2 - 2 * h0)
              (firstLongTwoStrideConstant h0 d e) i j|) :
    Tendsto (fun n : ℕ =>
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (fun i j =>
          q1ActualCrossLongActiveKernel f hf d e hd he n (δ n) t
              ((n : ℝ) * δ n) (2 - 2 * h0) i j -
          q1CrossRieszActiveKernel n (δ n) t ((n : ℝ) * δ n)
              (2 - 2 * h0) (firstLongTwoStrideConstant h0 d e) i j))
      atTop (𝓝 0) := by
  let S := fun n : ℕ => (n : ℝ) * δ n
  let m := fun n : ℕ => (localWeightActiveSet n 2 (δ n) t).card
  let ψ := 2 - 2 * h0
  let c := firstLongTwoStrideConstant h0 d e
  let A := fun n : ℕ => q1ActualCrossLongActiveKernel
    f hf d e hd he n (δ n) t (S n) ψ
  let B := fun n : ℕ => q1CrossRieszActiveKernel
    n (δ n) t (S n) ψ c
  let Cref := 2 * c ^ 2 * (3 + 3 * 4 ^ (1 - 2 * ψ) / (1 - 2 * ψ))
  have hψ0 : 0 ≤ ψ := by dsimp only [ψ]; linarith
  have hψhalf : ψ < 1 / 2 := by dsimp only [ψ]; linarith
  have hCref : 0 ≤ Cref := by
    dsimp only [Cref]
    have hden : 0 < 1 - 2 * ψ := by linarith
    positivity
  have hgeom := localWeightActiveSet_card_ratio_tendsto_two
    2 t ht δ hδpos hδ0 hN
  have hcardpos : ∀ᶠ n in atTop, 0 < m n := by
    simpa only [m] using hgeom.1
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hSpos : ∀ᶠ n in atTop, 0 < S n := hN.eventually_gt_atTop 0
  have hAnear : Tendsto (fun n =>
      realScaleMeshBandEnergy (S n) (R n) (A n)) atTop (𝓝 0) := by
    simpa only [A, S, ψ] using
      hurstHolder_q1_actual_cross_correlation_band_energy_tendsto_zero
        p M f hf d e hd he t δ R ψ hδpos hN
        (by simpa only [S, ψ] using hcut)
  have hBnear : Tendsto (fun n =>
      realScaleMeshBandEnergy (S n) (R n) (B n)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ => c ^ 2 *
        (S n ^ (2 * ψ - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa only [S, m, ψ, mul_zero] using hcut.const_mul (c ^ 2)
    apply squeeze_zero' (g := fun n : ℕ => c ^ 2 *
      (S n ^ (2 * ψ - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1)))
    · exact Eventually.of_forall fun n => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    · filter_upwards [hnpos, hδpos, hSpos, hcardpos] with n hn hδ hSn hcard
      rw [show B n = (rankRieszKernel (S n) ψ c :
          Fin (m n) → Fin (m n) → ℝ) by
        exact q1CrossRieszActiveKernel_eq_rankRieszKernel
          n hn (δ n) t (S n) ψ c hδ hSn hcard]
      exact rankRieszKernel_band_energy_le (S n) ψ c hSn hψ0
    · exact hupper
  have hBbound : ∀ᶠ n in atTop,
      realScaleMeshEnergy (S n) (B n) ≤ Cref := by
    filter_upwards [hnpos, hδpos, hcardpos, hN.eventually_ge_atTop 1]
      with n hn hδ hcard hS1
    have hm : (m n : ℝ) ≤ 3 * S n := by
      dsimp only [m, S]
      exact localWeightActiveSet_card n 2 hn (δ n) t hδ hS1
    have hSn : 0 < S n := zero_lt_one.trans_le hS1
    rw [show B n = (rankRieszKernel (S n) ψ c :
        Fin (m n) → Fin (m n) → ℝ) by
      exact q1CrossRieszActiveKernel_eq_rankRieszKernel
        n hn (δ n) t (S n) ψ c hδ hSn hcard]
    exact rankRieszKernel_energy_le_const (S n) ψ c hS1 hm hψ0 hψhalf
  have hfinal := realScaleMeshEnergy_sub_tendsto_zero_of_relative
    m R S A B err Cref herr0 hCref
    (by simpa only [A, B, S, ψ, c] using hoff)
    hAnear hBnear hBbound herr
  simpa only [A, B, S, ψ, c, m] using hfinal

end Hurst
