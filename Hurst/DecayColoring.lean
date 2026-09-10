import Hurst.ActualPointwiseDecay
import Hurst.WeakCorrelationGrouping

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem tendsto_zero_of_summable_sq_nonneg (u : ℕ → ℝ)
    (hu : Summable (fun n => u n ^ 2)) (hu0 : ∀ n, 0 ≤ u n) :
    Tendsto u atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hs := hu.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at hs
  obtain ⟨N, hN⟩ := hs (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq, sub_zero, abs_sq] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu0 n)]
  nlinarith

theorem strideFirstDecay_tendsto_zero (b : ℝ) (hb : b < 3 / 4)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (strideFirstDecay b d) atTop (nhds 0) :=
  tendsto_zero_of_summable_sq_nonneg _
    (strideFirstDecay_square_summable b hb d hd) (strideFirstDecay_nonneg b d)

theorem strideSecondDecay_tendsto_zero (b : ℝ) (hb : b < 1)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (strideSecondDecay b d) atTop (nhds 0) :=
  tendsto_zero_of_summable_sq_nonneg _
    (strideSecondDecay_square_summable b hb d hd) (strideSecondDecay_nonneg b d)

/-- A fixed residue coloring turns any correlation bound with a vanishing distance
profile into the uniform small-correlation hypothesis used by Bardet--Surgailis. -/
theorem exists_residueColor_small_correlation
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds 0))
    (A ε e : ℝ) (hA : 0 ≤ A) (hε : 0 < ε)
    (he : e ≤ ε / 2) :
    ∃ d : ℕ, ∃ hd : 0 < d, ∀ {n : ℕ} (r : Fin n → Fin n → ℝ),
      (∀ i j, |r i j| ≤ A * u (Nat.dist j.val i.val) + e) →
      ∀ i j, i ≠ j → residueColor d hd i = residueColor d hd j →
        |r i j| ≤ ε := by
  have ht : 0 < ε / (2 * (A + 1)) := by positivity
  have hev := (Metric.tendsto_atTop.1 hu) _ ht
  obtain ⟨N, hN⟩ := hev
  let d := max 1 N
  have hd : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine ⟨d, hd, ?_⟩
  intro n r hr i j hij hc
  have hsep := residueColor_equal_separation d hd hij hc
  have hdist : d ≤ Nat.dist j.val i.val := by
    rcases le_total i.val j.val with hle | hle
    · rw [Nat.dist_eq_sub_of_le_right hle]
      omega
    · rw [Nat.dist_eq_sub_of_le hle]
      omega
  have hDN : N ≤ Nat.dist j.val i.val := (le_max_right 1 N).trans hdist
  have hut := hN _ hDN
  rw [Real.dist_eq, sub_zero] at hut
  have hAu : A * u (Nat.dist j.val i.val) ≤ ε / 2 := by
    calc
      A * u (Nat.dist j.val i.val) ≤ A * |u (Nat.dist j.val i.val)| := by
        gcongr
        exact le_abs_self _
      _ ≤ A * (ε / (2 * (A + 1))) := mul_le_mul_of_nonneg_left hut.le hA
      _ ≤ ε / 2 := by
        have hA1 : 0 < A + 1 := by linarith
        have hfrac : A / (A + 1) ≤ 1 := (div_le_one hA1).2 (by linarith)
        rw [show A * (ε / (2 * (A + 1))) = (ε / 2) * (A / (A + 1)) by
          field_simp
          <;> ring]
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hfrac (show 0 ≤ ε / 2 by positivity))
  exact (hr i j).trans (by linarith)

end Hurst
