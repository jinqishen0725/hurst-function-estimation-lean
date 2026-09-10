import Hurst.ActualTruncatedVarianceJunction
import Hurst.FirstStrideDecay
import Hurst.StrideDecay
import Hurst.SecondFrozenCrossLagCorrelation

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem firstIncrementLagCorrelation_abs_le_decay
    (h : ℝ) (hh : 0 < h) (hhb : h < 3 / 4) :
    ∃ A ≥ 0, ∀ k : ℕ,
      |firstIncrementLagCorrelation h k| ≤ A * strideFirstDecay h 1 k := by
  obtain ⟨A, hA, hdec⟩ := frozen_stride_first_grid_decay h h hh hhb le_rfl 1 (by norm_num)
  refine ⟨A, by linarith, ?_⟩
  intro k
  let H : Fin (k + 1) → Ioo (0 : ℝ) 1 := fun _ => ⟨h, hh, by linarith⟩
  let i : Fin (k + 1) := ⟨0, by omega⟩
  let j : Fin (k + 1) := ⟨k, by omega⟩
  have hd := hdec 1 (k + 1) (by norm_num) H
    (fun z => by simp only [H]; exact ⟨le_rfl, le_rfl⟩) i j
  have hinner :
      ⟪normalizedFrozenIncrement (H i) (grid 1 i.val) 1,
        normalizedFrozenIncrement (H j) (grid 1 j.val) 1⟫ =
      firstIncrementLagCorrelation h k := by
    have he := normalizedFrozenIncrement_same_parameter_nat_lag
      ⟨h, hh, by linarith⟩ (grid 1 i.val) 1 k (by norm_num)
    convert he using 1
    simp only [H]
    congr 2
    dsimp only [i, j]
    unfold grid
    norm_num
    ring
  rw [← hinner]
  have hdist : Nat.dist j.val i.val = k := by
    dsimp only [i, j]
    rw [Nat.dist_comm]
    rw [Nat.dist_eq_sub_of_le (Nat.zero_le k)]
    omega
  rw [hdist] at hd
  norm_num at hd
  exact hd

theorem firstIncrementLagCorrelation_abs_le_one
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) (k : ℕ) :
    |firstIncrementLagCorrelation h k| ≤ 1 := by
  let H : Ioo (0 : ℝ) 1 := ⟨h, hh, hh1⟩
  have he := normalizedFrozenIncrement_same_parameter_nat_lag H 0 1 k (by norm_num)
  rw [← he]
  have hcs := abs_real_inner_le_norm
    (normalizedFrozenIncrement H 0 1)
    (normalizedFrozenIncrement H (0 + k * 1) 1)
  rw [normalizedFrozenIncrement_norm _ _ _ (by norm_num),
    normalizedFrozenIncrement_norm _ _ _ (by norm_num)] at hcs
  norm_num at hcs ⊢
  exact hcs

theorem summable_symmetric_gaussianLogTruncationCovariance
    (K : ℕ) (rho d : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hd : Summable (fun k => d k ^ 2))
    (hrho : ∀ k, |rho k| ≤ 1)
    (hdec : ∀ k, |rho k| ≤ A * d k) :
    Summable (fun k => (if k = 0 then 1 else 2) *
      gaussianLogTruncationCovariance K (rho k)) := by
  let E : ℝ := ∑ j ∈ Finset.range K, gaussianLogHermiteCoefficient j ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  apply Summable.of_norm_bounded
    (hd.mul_left (2 * E * A ^ 2))
  intro k
  have hc := gaussianLogTruncationCovariance_abs_le_square K (rho k) (hrho k)
  have hs : (if k = 0 then (1 : ℝ) else 2) ≤ 2 := by
    split_ifs <;> norm_num
  have hs0 : 0 ≤ (if k = 0 then (1 : ℝ) else 2) := by
    split_ifs <;> norm_num
  have hd2 : |rho k| ^ 2 ≤ (A * d k) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hdec k) 2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0]
  calc
    (if k = 0 then (1 : ℝ) else 2) *
        |gaussianLogTruncationCovariance K (rho k)| ≤
        2 * (|rho k| ^ 2 * E) := by gcongr
    _ ≤ 2 * ((A * d k) ^ 2 * E) := by gcongr
    _ = (2 * E * A ^ 2) * d k ^ 2 := by ring

theorem firstIncrement_symmetric_truncationCovariance_summable
    (K : ℕ) (h : ℝ) (hh : 0 < h)
    (hhb : h < 3 / 4) :
    Summable (fun (k : ℕ) => (if k = 0 then 1 else 2) *
      gaussianLogTruncationCovariance K (firstIncrementLagCorrelation h k)) := by
  obtain ⟨A, hA, hdec⟩ := firstIncrementLagCorrelation_abs_le_decay h hh hhb
  exact summable_symmetric_gaussianLogTruncationCovariance K
    (fun k => firstIncrementLagCorrelation h k) (strideFirstDecay h 1) A hA
    (strideFirstDecay_square_summable h hhb 1 (by norm_num))
    (firstIncrementLagCorrelation_abs_le_one h hh (by linarith)) hdec

theorem secondIncrementLagCorrelation_eq_vectorCorrelation
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) (s : ℝ) (k : ℕ) :
    secondIncrementLagCorrelation h k =
      vectorCorrelation
        (normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ s 1)
        (normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (s + k) 1) := by
  let H : Ioo (0 : ℝ) 1 := ⟨h, hh, hh1⟩
  let U := normalizedFrozenSecondIncrement H s 1
  let V := normalizedFrozenSecondIncrement H (s + k) 1
  let q : ℝ := 4 - (2 : ℝ) ^ (2 * h)
  have hq : 0 < q := by
    dsimp only [q]
    have hp : (2 : ℝ) ^ (2 * h) < (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    norm_num at hp ⊢
    exact hp
  have hU : ‖U‖ ^ 2 = q := by
    exact normalizedFrozenSecondIncrement_norm_sq H s 1 (by norm_num)
  have hV : ‖V‖ ^ 2 = q := by
    exact normalizedFrozenSecondIncrement_norm_sq H (s + k) 1 (by norm_num)
  have hden : ‖U‖ * ‖V‖ = q := by
    have huv : ‖U‖ = ‖V‖ :=
      (sq_eq_sq₀ (norm_nonneg U) (norm_nonneg V)).mp (hU.trans hV.symm)
    rw [huv]
    simpa only [pow_two] using hV
  have hinner := normalizedFrozenSecondIncrement_cross_parameter_lag
    H H s 1 k (by norm_num)
  have hself := secondIncrementCrossLagCovariance_self h k hh hh1
  rw [show s + (k : ℝ) * 1 = s + k by ring] at hinner
  unfold secondIncrementLagCorrelation vectorCorrelation
  rw [← hself, ← hinner]
  change _ / _ = ⟪U, V⟫ / (‖U‖ * ‖V‖)
  rw [hden]

theorem secondIncrementLagCorrelation_abs_le_one
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) (k : ℕ) :
    |secondIncrementLagCorrelation h k| ≤ 1 := by
  rw [secondIncrementLagCorrelation_eq_vectorCorrelation h hh hh1 0 k]
  simpa only [vectorCorrelation] using
    abs_real_inner_div_norm_mul_norm_le_one
      (normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ 0 1)
      (normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (0 + k) 1)

theorem secondIncrementLagCorrelation_abs_le_decay
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    ∃ A ≥ 0, ∀ k : ℕ,
      |secondIncrementLagCorrelation h k| ≤ A * strideSecondDecay h 1 k := by
  obtain ⟨C, hC, hdec⟩ := frozen_stride_second_grid_decay h h hh hh1 le_rfl 1 (by norm_num)
  let q : ℝ := 4 - (2 : ℝ) ^ (2 * h)
  have hq : 0 < q := by
    dsimp only [q]
    have hp : (2 : ℝ) ^ (2 * h) < (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    norm_num at hp ⊢
    exact hp
  refine ⟨C / q, div_nonneg (by linarith) hq.le, ?_⟩
  intro k
  let H : Fin (k + 1) → Ioo (0 : ℝ) 1 := fun _ => ⟨h, hh, hh1⟩
  let i : Fin (k + 1) := ⟨0, by omega⟩
  let j : Fin (k + 1) := ⟨k, by omega⟩
  have hd := hdec 1 (k + 1) (by norm_num) H
    (fun z => by simp only [H]; exact ⟨le_rfl, le_rfl⟩) i j
  have hdist : Nat.dist j.val i.val = k := by
    dsimp only [i, j]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.zero_le k)]
    omega
  rw [hdist] at hd
  norm_num at hd
  rw [secondIncrementLagCorrelation_eq_vectorCorrelation h hh hh1
    (grid 1 i.val) k]
  unfold vectorCorrelation
  have hden :
      ‖normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (grid 1 i.val) 1‖ *
        ‖normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (grid 1 i.val + k) 1‖ = q := by
    have hU := normalizedFrozenSecondIncrement_norm_sq
      ⟨h, hh, hh1⟩ (grid 1 i.val) 1 (by norm_num)
    have hV := normalizedFrozenSecondIncrement_norm_sq
      ⟨h, hh, hh1⟩ (grid 1 i.val + k) 1 (by norm_num)
    change _ = q at hU hV
    have huv :
        ‖normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (grid 1 i.val) 1‖ =
          ‖normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (grid 1 i.val + k) 1‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hU.trans hV.symm)
    rw [huv]
    simpa only [pow_two] using hV
  rw [hden, abs_div, abs_of_pos hq]
  have hpos : grid 1 j.val = grid 1 i.val + (k : ℝ) := by
    dsimp only [i, j]
    unfold grid
    norm_num
    ring
  rw [← hpos]
  calc
    |⟪normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (grid 1 i.val) 1,
      normalizedFrozenSecondIncrement ⟨h, hh, hh1⟩ (grid 1 j.val) 1⟫| / q ≤
        (C * strideSecondDecay h 1 k) / q :=
      div_le_div_of_nonneg_right hd hq.le
    _ = (C / q) * strideSecondDecay h 1 k := by ring

theorem secondIncrement_symmetric_truncationCovariance_summable
    (K : ℕ) (h : ℝ) (hh : 0 < h)
    (hh1 : h < 1) :
    Summable (fun (k : ℕ) => (if k = 0 then 1 else 2) *
      gaussianLogTruncationCovariance K (secondIncrementLagCorrelation h k)) := by
  obtain ⟨A, hA, hdec⟩ := secondIncrementLagCorrelation_abs_le_decay h hh hh1
  exact summable_symmetric_gaussianLogTruncationCovariance K
    (fun k => secondIncrementLagCorrelation h k) (strideSecondDecay h 1) A hA
    (strideSecondDecay_square_summable h hh1 1 (by norm_num))
    (secondIncrementLagCorrelation_abs_le_one h hh hh1) hdec

end Hurst
