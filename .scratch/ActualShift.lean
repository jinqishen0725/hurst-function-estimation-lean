import Hurst.ShiftedWeightEnergy

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem localPolynomialWeights_fixedShift_scaledL2_tendsto
    (r q k : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * δ n *
      ∑ i, (finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i -
        localPolynomialWeights r n q (δ n) t i) ^ 2) atTop (𝓝 0) := by
  classical
  choose L hL using fun j : Fin (r + 1) => kernelMomentFunction_lipschitz j.val
  obtain ⟨Ni, hNi, D, hD, hinv⟩ := localDesignGram_uniform_inverse r q
  obtain ⟨Nw, hNw, Cw, hCw, hw⟩ := localPolynomialWeights_uniform_stability r q
  let C : ℝ := ∑ j : Fin (r + 1), D * (L j : ℝ)
  let N : ℕ → ℝ := fun n => (n : ℝ) * δ n
  let a : ℕ → ℝ := fun n => (N n)⁻¹ * C * ((k : ℝ) / N n)
  let b : ℕ → ℝ := fun n => Cw / N n
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg hD (L j).coe_nonneg)
  have hInv : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (by simpa only [N] using hN)
  let U : ℕ → ℝ := fun n =>
    6 * (C * (k : ℝ)) ^ 2 * (N n)⁻¹ ^ 2 +
      (k : ℝ) * Cw ^ 2 * (N n)⁻¹
  have hU : Tendsto U atTop (𝓝 0) := by
    have h1 := (hInv.pow 2).const_mul (6 * (C * (k : ℝ)) ^ 2)
    have h2 := hInv.const_mul ((k : ℝ) * Cw ^ 2)
    simpa [U] using h1.add h2
  apply squeeze_zero'
  · filter_upwards [hδpos, eventually_ge_atTop 1] with n hnδ hn
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hnδ.le)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · filter_upwards [hδpos,
      hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hN.eventually_ge_atTop (max Ni (max Nw 1)),
      eventually_ge_atTop (q + 1)] with n hnδ hnδhalf hnN hnq
    have hn0 : 0 < n := by omega
    have hqn : q ≤ n := by omega
    have hNpos : 0 < N n := by
      dsimp [N]
      positivity
    have hNiN : Ni ≤ N n := le_trans (le_max_left _ _) hnN
    have hNwN : Nw ≤ N n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hnN)
    have hOneN : 1 ≤ N n :=
      le_trans (le_max_right Nw 1) (le_trans (le_max_right Ni _) hnN)
    obtain ⟨_, hinvN⟩ :=
      hinv n hn0 hqn (δ n) t hnδ hnδhalf.le ⟨ht.1.le, ht.2.le⟩ hNiN
    obtain ⟨_, hweight, _, _⟩ :=
      hw n hn0 hqn (δ n) t hnδ hnδhalf.le ⟨ht.1.le, ht.2.le⟩ hNwN
    let active : Fin (n - q) → Prop := fun i =>
      |(grid n i.val - t) / δ n| < 1
    have hactive : (((Finset.univ.filter active).card : ℝ) ≤ 3 * N n) := by
      have hc := midpoint_active_card_bound n (n - q) hn0 (δ n) t hnδ
        (Finset.univ.filter active) (fun i hi => by
          simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
      dsimp [N]
      linarith
    have ha0 : 0 ≤ a n := by
      dsimp [a]
      positivity
    have hb0 : 0 ≤ b n := by
      dsimp [b]
      positivity
    have hsum := finZeroExtendedShift_sq_sum_bound k
      (localPolynomialWeights r n q (δ n) t) active
      (a n) (b n) (3 * N n) ha0 hb0 (by positivity)
      (fun i hi => by
        have hp := localPolynomialWeights_fixedShift_pointwise r n q k
          (δ n) t D hn0 hnδ hD L hL (fun j => hinvN 0 j) i hi
        convert hp using 1
        dsimp [a, C, N]
        simp only [← Finset.sum_mul]
        ring)
      (fun i hi hia his => by
        have hz1 := localPolynomialWeights_zero r n q (δ n) t i (le_of_not_gt hia)
        have hz2 := localPolynomialWeights_zero r n q (δ n) t
          ⟨i.val + k, hi⟩ (le_of_not_gt his)
        rw [hz1, hz2, sub_self])
      (fun i => by
        simpa only [b, N] using hweight i)
      hactive
    have hmul := mul_le_mul_of_nonneg_left hsum hNpos.le
    calc
      N n * ∑ i, (finZeroExtendedShift k
          (localPolynomialWeights r n q (δ n) t) i -
        localPolynomialWeights r n q (δ n) t i) ^ 2
          ≤ N n * (2 * (3 * N n) * (a n) ^ 2 + (k : ℝ) * (b n) ^ 2) := hmul
      _ = U n := by
        dsimp [a, b, U]
        field_simp
        ring
  · exact hU

end Hurst
