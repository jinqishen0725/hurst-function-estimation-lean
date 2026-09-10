import Hurst.ActualFirstLongOffDiagonal
import Hurst.ActualFirstLongBandEnergy
import Hurst.ActiveWindowDistance

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

def q1ActualLongActiveKernel
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (n : ℕ) (δ t S psi : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) : ℝ :=
  S ^ psi * vectorCorrelation
    (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 δ t i))
    (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 δ t j))

def q1RieszActiveKernel
    (n : ℕ) (δ t S psi c : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) : ℝ :=
  if Nat.dist
      (localWeightActiveIndex n 1 δ t i).val
      (localWeightActiveIndex n 1 δ t j).val = 0 then 0
  else c * (S / (Nat.dist
      (localWeightActiveIndex n 1 δ t i).val
      (localWeightActiveIndex n 1 δ t j).val : ℝ)) ^ psi

def q1ActualLongTailEnvelope
    (b Ccov Ctail L M h0 : ℝ) (n : ℕ) (δ S : ℝ) (R : ℕ) : ℝ :=
  let psi := 2 - 2 * h0
  let D := 2 * L * (1 + M) * δ
  let E := D * Real.log n
  18 * Ctail * D * (1 + Real.exp E * E) +
    9 * Real.exp E * E + 16 * ((R + 1 : ℕ) : ℝ)⁻¹ +
    (3 / 2 : ℝ) * D +
    4 * (2 * S) ^ psi * gridCovarianceError b Ccov n

private theorem fin_dist_lt_grid_size
    (n : ℕ) (i j : Fin (n - 1)) : Nat.dist i.val j.val < n := by
  rcases le_total i.val j.val with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    have hj := j.isLt
    omega
  · rw [Nat.dist_eq_sub_of_le_right hji]
    have hi := i.isLt
    omega

/-- The pair-dependent model bound is dominated by the deterministic tail
envelope uniformly over every active pair outside the cutoff. -/
theorem hurstHolder_q1_active_scaled_actual_tail_error_le_envelope
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ Ccov ≥ 0, ∃ Ctail ≥ 0, ∃ L > 0,
      ∀ n : ℕ, 2 ≤ n → ∀ δ S : ℝ, 0 < δ → S = (n : ℝ) * δ →
      ∀ R : ℕ, 1 ≤ R →
      gridCovarianceError b Ccov n ≤ 1 / 2 →
      ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      R < Nat.dist
        (localWeightActiveIndex n 1 δ t i).val
        (localWeightActiveIndex n 1 δ t j).val →
      |(Nat.dist
          (localWeightActiveIndex n 1 δ t i).val
          (localWeightActiveIndex n 1 δ t j).val : ℝ) ^ (2 - 2 * f t) *
          vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 δ t i))
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 δ t j)) -
          f t * (2 * f t - 1)| ≤
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n δ S R := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hcore⟩ :=
    hurstHolder_q1_active_scaled_actual_tail_error
      p a b M hp ha hb hab hM f hf hF t ht
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  intro n hn δ S hδ hS R hR hsmall i j hoff
  let ii := localWeightActiveIndex n 1 δ t i
  let jj := localWeightActiveIndex n 1 δ t j
  let x : ℝ := Nat.dist ii.val jj.val
  let psi := 2 - 2 * f t
  let D := 2 * L * (1 + M) * δ
  let Ex := D * |Real.log x|
  let En := D * Real.log n
  have hn0 : 0 < n := by omega
  have hoff' : R < Nat.dist ii.val jj.val := by simpa only [ii, jj] using hoff
  have hxNat : 2 ≤ Nat.dist ii.val jj.val := by omega
  have hx : 2 ≤ x := by dsimp only [x]; exact_mod_cast hxNat
  have hx0 : 0 < x := by linarith
  have hxnNat : Nat.dist ii.val jj.val < n := fin_dist_lt_grid_size n ii jj
  have hxn : x ≤ (n : ℝ) := by dsimp only [x]; exact_mod_cast hxnNat.le
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogle : |Real.log x| ≤ Real.log n := by
    rw [abs_of_nonneg hlogx0]
    exact Real.log_le_log hx0 hxn
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hEx0 : 0 ≤ Ex := by dsimp only [Ex]; positivity
  have hEn0 : 0 ≤ En := by dsimp only [En]; positivity
  have hExEn : Ex ≤ En := by
    dsimp only [Ex, En]
    exact mul_le_mul_of_nonneg_left hlogle hD0
  have hexp : Real.exp Ex ≤ Real.exp En := Real.exp_le_exp.mpr hExEn
  have hexpmul : Real.exp Ex * Ex ≤ Real.exp En * En :=
    mul_le_mul hexp hExEn hEx0 (Real.exp_pos _).le
  have hxS := localWeightActiveIndex_dist_lt_two_effective n δ t hδ i j
  rw [← hS] at hxS
  have hpsi0 : 0 ≤ psi := by
    dsimp only [psi]
    have := (hF ht).2
    linarith
  have hxpow : x ^ psi ≤ (2 * S) ^ psi :=
    Real.rpow_le_rpow hx0.le hxS.le hpsi0
  have hRcast : ((R + 1 : ℕ) : ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast (show R + 1 ≤ Nat.dist ii.val jj.val by omega)
  have hinv : x⁻¹ ≤ ((R + 1 : ℕ) : ℝ)⁻¹ :=
    (inv_le_inv₀ hx0 (by positivity)).2 hRcast
  have hbase := hcore n hn0 δ hδ i j hsmall (by simpa only [x, ii, jj] using hx)
  dsimp only at hbase
  apply hbase.trans
  change
    18 * Ctail * D * (1 + Real.exp Ex * Ex) +
          9 * Real.exp Ex * Ex + 16 * x⁻¹ +
          (3 / 2 : ℝ) * D +
          4 * x ^ psi * gridCovarianceError b Ccov n ≤ _
  have hgrid0 : 0 ≤ gridCovarianceError b Ccov n := by
    unfold gridCovarianceError
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith)
    positivity
  have h1 : 18 * Ctail * D * (1 + Real.exp Ex * Ex) ≤
      18 * Ctail * D * (1 + Real.exp En * En) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hexpmul)
      (mul_nonneg (mul_nonneg (by norm_num) hCtail) hD0)
  have h2 : 9 * Real.exp Ex * Ex ≤ 9 * Real.exp En * En :=
    by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hexpmul (by norm_num : (0 : ℝ) ≤ 9)
  have h3 : 16 * x⁻¹ ≤ 16 * ((R + 1 : ℕ) : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  have h5 : 4 * x ^ psi * gridCovarianceError b Ccov n ≤
      4 * (2 * S) ^ psi * gridCovarianceError b Ccov n :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hxpow (by norm_num)) hgrid0
  unfold q1ActualLongTailEnvelope
  dsimp only [psi, D, En] at h1 h2 h5 ⊢
  exact add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) le_rfl) h5

/-- Actual q=1 Hilbert--Schmidt convergence to the discrete Riesz reference
kernel.  All mBm-specific applicability is discharged here; the remaining
premises concern only the deterministic cutoff and reference-kernel energies. -/
theorem hurstHolder_q1_actual_kernel_hilbertSchmidt_to_riesz
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t) :
    ∃ Ccov ≥ 0, ∃ Ctail ≥ 0, ∃ L > 0,
      ∀ (δ : ℕ → ℝ) (R : ℕ → ℕ),
      (∀ᶠ n in atTop, 0 < δ n) →
      Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop →
      (∀ᶠ n in atTop, 1 ≤ R n) →
      Tendsto (fun n : ℕ =>
        ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
          ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
          (2 * (R n : ℝ) + 1)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ =>
        q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n)
          ((n : ℝ) * δ n) (R n)) atTop (𝓝 0) →
      (∀ Cref : ℝ, 0 ≤ Cref →
        Tendsto (fun n : ℕ =>
          realScaleMeshBandEnergy ((n : ℝ) * δ n) (R n)
            (q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n)
              (2 - 2 * f t) (f t * (2 * f t - 1)))) atTop (𝓝 0) →
        (∀ᶠ n : ℕ in atTop,
          realScaleMeshEnergy ((n : ℝ) * δ n)
            (q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n)
              (2 - 2 * f t) (f t * (2 * f t - 1))) ≤ Cref) →
        Tendsto (fun n : ℕ =>
          realScaleMeshEnergy ((n : ℝ) * δ n)
            (fun i j =>
              q1ActualLongActiveKernel f hf n (δ n) t
                  ((n : ℝ) * δ n) (2 - 2 * f t) i j -
                q1RieszActiveKernel n (δ n) t ((n : ℝ) * δ n)
                  (2 - 2 * f t) (f t * (2 * f t - 1)) i j))
          atTop (𝓝 0)) := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, henvPair⟩ :=
    hurstHolder_q1_active_scaled_actual_tail_error_le_envelope
      p a b M hp ha hb hab hM f hf hF t ht
  refine ⟨Ccov, hCcov, Ctail, hCtail, L, hL, ?_⟩
  intro δ R hδpos hN hR hcut hEnv Cref hCref hBnear hBbound
  let S := fun n : ℕ => (n : ℝ) * δ n
  let psi := 2 - 2 * f t
  let c := f t * (2 * f t - 1)
  let A := fun n : ℕ =>
    q1ActualLongActiveKernel f hf n (δ n) t (S n) psi
  let B := fun n : ℕ =>
    q1RieszActiveKernel n (δ n) t (S n) psi c
  let e := fun n : ℕ =>
    q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) (S n) (R n) / c
  have hc : 0 < c := by
    dsimp only [c]
    have hft0 : 0 < f t := by
      have hfa : a ≤ f t := (hF ht).1
      linarith
    have hft34 : 3 / 4 < f t := hlong
    have hfactor : 0 < 2 * f t - 1 := by linarith
    exact mul_pos hft0 hfactor
  have hsmall : ∀ᶠ n in atTop,
      gridCovarianceError b Ccov n ≤ 1 / 2 :=
    (gridCovarianceError_tendsto b Ccov hb).eventually_le_const (by norm_num)
  have hn2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have hSpos : ∀ᶠ n in atTop, 0 < S n := by
    filter_upwards [hδpos, hn2] with n hδ hn
    dsimp only [S]
    positivity
  have hAnear : Tendsto (fun n =>
      realScaleMeshBandEnergy (S n) (R n) (A n)) atTop (𝓝 0) := by
    have h := hurstHolder_q1_actual_correlation_band_energy_tendsto_zero
      p a b M (f t) psi hp ha hb hab hM f hf hF t δ R hδpos hN
      (by simpa only [psi, S] using hcut)
    change Tendsto (fun n : ℕ =>
      realScaleMeshBandEnergy ((n : ℝ) * δ n) (R n)
        (fun i j => ((n : ℝ) * δ n) ^ psi *
          vectorCorrelation
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 (δ n) t i))
            (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
              (localWeightActiveIndex n 1 (δ n) t j))))
      atTop (𝓝 0)
    exact h
  have he0 : ∀ᶠ n in atTop, 0 ≤ e n := by
    filter_upwards [hn2, hδpos, hR] with n hn hδ hRn
    have hn0 : 0 < n := by omega
    have hgrid0 : 0 ≤ gridCovarianceError b Ccov n := by
      unfold gridCovarianceError
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        linarith)
      positivity
    apply div_nonneg _ hc.le
    unfold q1ActualLongTailEnvelope
    dsimp only
    positivity
  have herr : Tendsto e atTop (𝓝 0) := by
    dsimp only [e, c]
    simpa only [zero_div] using hEnv.div_const c
  have hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val →
        |A n i j - B n i j| ≤ e n * |B n i j| := by
    filter_upwards [hn2, hδpos, hR, hsmall, hSpos] with n hn hδ hRn hsm hSn
    intro i j hij
    have hn0 : 0 < n := by omega
    have hcard : 0 < (localWeightActiveSet n 1 (δ n) t).card := by
      have hi := i.isLt
      omega
    have hij' : R n < Nat.dist
        (localWeightActiveIndex n 1 (δ n) t i).val
        (localWeightActiveIndex n 1 (δ n) t j).val := by
      rw [localWeightActiveIndex_physical_dist_eq_rank_dist
        n 1 hn0 (δ n) t hδ hcard i j]
      rwa [Nat.dist_comm]
    have htail := henvPair n hn (δ n) (S n) hδ rfl (R n) hRn hsm i j hij'
    let x : ℝ := Nat.dist
      (localWeightActiveIndex n 1 (δ n) t i).val
      (localWeightActiveIndex n 1 (δ n) t j).val
    have hxNat : 0 < Nat.dist
        (localWeightActiveIndex n 1 (δ n) t i).val
        (localWeightActiveIndex n 1 (δ n) t j).val := by omega
    have hx : 0 < x := by dsimp only [x]; exact_mod_cast hxNat
    have hF0 : 0 ≤ q1ActualLongTailEnvelope b Ccov Ctail L M (f t)
        n (δ n) (S n) (R n) := by
      unfold q1ActualLongTailEnvelope
      dsimp only
      have hgrid0 : 0 ≤ gridCovarianceError b Ccov n := by
        unfold gridCovarianceError
        have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          linarith)
        positivity
      positivity
    have hrel := scaled_tail_error_to_relative_riesz
      (S n) x psi c
      (vectorCorrelation
        (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 (δ n) t i))
        (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 (δ n) t j)))
      (q1ActualLongTailEnvelope b Ccov Ctail L M (f t)
        n (δ n) (S n) (R n)) hSn hx hc hF0
      (by simpa only [x, psi, c] using htail)
    have hdistne : Nat.dist
        (localWeightActiveIndex n 1 (δ n) t i).val
        (localWeightActiveIndex n 1 (δ n) t j).val ≠ 0 := ne_of_gt hxNat
    simpa only [A, B, e, q1ActualLongActiveKernel, q1RieszActiveKernel,
      S, psi, c, hdistne, if_false, x] using hrel
  have hfinal := realScaleMeshEnergy_sub_tendsto_zero_of_relative
    (fun n => (localWeightActiveSet n 1 (δ n) t).card) R S A B e Cref
    he0 hCref hoff hAnear
    (by simpa only [B, S, psi, c] using hBnear)
    (by simpa only [B, S, psi, c] using hBbound) herr
  simpa only [A, B, S, psi, c] using hfinal

end Hurst
