import Hurst.SecondFrozen
import Hurst.SecondCorrelationSums
import Hurst.GridLogMean

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

def strideSecondDecay (b : ℝ) (d k : ℕ) : ℝ :=
  if k ≤ 3*d then 1 else (((k-2*d : ℕ):ℝ)/(d:ℝ)) ^ (2*b-4)

theorem strideSecondDecay_nonneg (b : ℝ) (d k : ℕ) : 0 ≤ strideSecondDecay b d k := by
  unfold strideSecondDecay
  split_ifs <;> positivity

theorem strideSecondDecay_square_summable (b : ℝ) (hb : b < 1) (d : ℕ) (hd : 0 < d) :
    Summable (fun k => (strideSecondDecay b d k)^2) := by
  have hs : Summable (fun k : ℕ => (k:ℝ)^(4*b-8)) := Real.summable_nat_rpow.mpr (by linarith)
  have hs' := ((summable_nat_add_iff (d+1)).mpr hs).div_const ((d:ℝ)^(4*b-8))
  apply (summable_nat_add_iff (3*d+1)).mp
  apply hs'.congr
  intro k
  have hk : ¬k+(3*d+1) ≤ 3*d := by omega
  simp only [strideSecondDecay, hk, if_false, show k+(3*d+1)-2*d = k+(d+1) by omega]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) (by positivity)]
  congr 2 <;> ring

theorem grid_stride_separated_gap (n d i j : ℕ) (hn : 0 < n) (hd : 0 < d) (hij : i+2*d ≤ j) :
    grid n j - (grid n i + 2*((d:ℝ)/n)) = (((j-i-2*d:ℕ):ℝ)/d)*((d:ℝ)/n) := by
  have hj : i ≤ j := by omega
  have hjd : 2*d ≤ j-i := by omega
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  rw [Nat.cast_sub hjd, Nat.cast_sub hj]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  unfold grid
  field_simp
  <;> ring

theorem frozen_stride_second_grid_decay (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (d : ℕ) (hd : 0 < d) :
    ∃ C ≥ 1, ∀ n m : ℕ, 0 < n → ∀ H : Fin m → Ioo (0 : ℝ) 1,
      (∀ i, (H i : ℝ) ∈ Icc a b) → ∀ i j : Fin m,
      |⟪normalizedFrozenSecondIncrement (H i) (grid n i.val) ((d:ℝ)/n),
        normalizedFrozenSecondIncrement (H j) (grid n j.val) ((d:ℝ)/n)⟫| ≤ C * strideSecondDecay b d (Nat.dist j.val i.val) := by
  obtain ⟨C, hC, hdec⟩ := normalizedFrozenSecondIncrement_uniform_decay a b ha hb hab
  refine ⟨C+4, by linarith, ?_⟩
  intro n m hn H hH
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hord : ∀ i j : Fin m, i.val ≤ j.val →
      |⟪normalizedFrozenSecondIncrement (H i) (grid n i.val) ((d:ℝ)/n),
        normalizedFrozenSecondIncrement (H j) (grid n j.val) ((d:ℝ)/n)⟫| ≤ (C+4) * strideSecondDecay b d (Nat.dist j.val i.val) := by
    intro i j hij
    rw [Nat.dist_eq_sub_of_le_right hij]
    by_cases hnear : j.val-i.val ≤ 3*d
    · have hcs := abs_real_inner_le_norm (normalizedFrozenSecondIncrement (H i) (grid n i.val) ((d:ℝ)/n))
        (normalizedFrozenSecondIncrement (H j) (grid n j.val) ((d:ℝ)/n))
      have h1 := normalizedFrozenSecondIncrement_norm_le (H i) (grid n i.val) ((d:ℝ)/n) (by positivity)
      have h2 := normalizedFrozenSecondIncrement_norm_le (H j) (grid n j.val) ((d:ℝ)/n) (by positivity)
      have hh := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
      simp only [strideSecondDecay, hnear, if_true, mul_one]
      linarith
    · have hgap : i.val+2*d ≤ j.val := by omega
      have hg : (d:ℝ) ≤ ((j.val-i.val-2*d:ℕ):ℝ) := by exact_mod_cast (show d ≤ j.val-i.val-2*d by omega)
      have hrat : (1:ℝ) ≤ ((j.val-i.val-2*d:ℕ):ℝ)/(d:ℝ) := (le_div_iff₀ hdR).mpr (by simpa only [one_mul] using hg)
      have he := hdec (H i) (H j) (hH i) (hH j) (grid n i.val) (grid n j.val) ((d:ℝ)/n)
        (((j.val-i.val-2*d:ℕ):ℝ)/(d:ℝ)) (by positivity) hrat (grid_stride_separated_gap n d i.val j.val hn hd hgap)
      simp only [strideSecondDecay, hnear, if_false]
      exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))
  intro i j
  rcases le_total i.val j.val with hij | hji
  · exact hord i j hij
  · rw [real_inner_comm, Nat.dist_comm]
    exact hord j i hji

theorem stride_second_correlation_square_row_bound (b A e : ℝ) (d : ℕ) (hd : 0 < d) (hb : b < 1) (hA : 0 ≤ A) (he : 0 ≤ e)
    (n : ℕ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, |r i j| ≤ A * strideSecondDecay b d (Nat.dist j.val i.val) + e) (i : Fin n) :
    (∑ j, (r i j) ^ 2) ≤ 4 * A ^ 2 * (∑' k, (strideSecondDecay b d k) ^ 2) + 2 * n * e ^ 2 := by
  have hsum : (∑ j, (r i j) ^ 2) ≤ ∑ j : Fin n, (2 * A ^ 2 * (strideSecondDecay b d (Nat.dist j.val i.val)) ^ 2 + 2 * e ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hr i j) 2
    rw [sq_abs] at h
    nlinarith [sq_nonneg (A * strideSecondDecay b d (Nat.dist j.val i.val) - e)]
  have hdist := grid_distance_sum_le_tsum (fun k => (strideSecondDecay b d k) ^ 2)
    (strideSecondDecay_square_summable b hb d hd) (fun k => sq_nonneg _) n i
  have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2 * A ^ 2 by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith

end Hurst
