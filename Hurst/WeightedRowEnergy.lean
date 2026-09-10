import Hurst.WeightEnergy
import Hurst.GaussianLogRisk
import Hurst.Rates

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

theorem weighted_double_sum_le_max_l1_row {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (A : ι → ι → ℝ) (W L B : ℝ)
    (hW0 : 0 ≤ W) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B)
    (hW : ∀ i, |w i| ≤ W) (hL : ∑ i, |w i| ≤ L)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j ≤ B) :
    (∑ i, ∑ j, |w i| * |w j| * A i j) ≤ W * L * B := by
  calc
    (∑ i, ∑ j, |w i| * |w j| * A i j)
        ≤ ∑ i, ∑ j, |w i| * W * A i j := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          calc
            |w i| * |w j| * A i j = (|w i| * A i j) * |w j| := by ring
            _ ≤ (|w i| * A i j) * W :=
              mul_le_mul_of_nonneg_left (hW j)
                (mul_nonneg (abs_nonneg (w i)) (hA i j))
            _ = |w i| * W * A i j := by ring
    _ = ∑ i, |w i| * W * (∑ j, A i j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ ≤ ∑ i, |w i| * W * B := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hrow i)
            (mul_nonneg (abs_nonneg (w i)) (le_trans (abs_nonneg (w i)) (hW i)))
    _ ≤ W * L * B := by
          rw [← Finset.sum_mul]
          calc
            (∑ i, |w i| * W) * B = W * (∑ i, |w i|) * B := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ ≤ W * L * B := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hL hW0) hB0

theorem fourth_row_le_second_row {ι : Type*} [Fintype ι]
    (r : ι → ι → ℝ) (B : ℝ) (hr : ∀ i j, |r i j| ≤ 1)
    (hrow : ∀ i, ∑ j, r i j ^ 2 ≤ B) :
    ∀ i, ∑ j, |r i j| ^ 4 ≤ B := by
  intro i
  calc
    (∑ j, |r i j| ^ 4) ≤ ∑ j, r i j ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h0 := abs_nonneg (r i j)
      have h1 := hr i j
      rw [← sq_abs]
      nlinarith [sq_nonneg (|r i j|), mul_self_le_mul_self h0 h1]
    _ ≤ B := hrow i

theorem featureCorrelation_abs_le_one {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a b : EuclideanSpace ℝ ι)
    (_ha : ∑ i, a i • v i ≠ 0) (_hb : ∑ i, b i • v i ≠ 0) :
    abs (featureCorrelation v a b) ≤ 1 := by
  simpa only [featureCorrelation] using
    abs_real_inner_div_norm_mul_norm_le_one
      (∑ i, a i • v i) (∑ i, b i • v i)

theorem weighted_fourth_energy_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (r : ι → ι → ℝ) (W L B : ℝ)
    (hW0 : 0 ≤ W) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B)
    (hW : ∀ i, |w i| ≤ W) (hL : ∑ i, |w i| ≤ L)
    (hr : ∀ i j, |r i j| ≤ 1) (hrow : ∀ i, ∑ j, r i j ^ 2 ≤ B) :
    (∑ i, ∑ j, |w i| * |w j| * |r i j| ^ 4) ≤ W * L * B := by
  exact weighted_double_sum_le_max_l1_row w (fun i j => |r i j| ^ 4) W L B
    hW0 hL0 hB0 hW hL (fun _ _ => by positivity) (fourth_row_le_second_row r B hr hrow)

theorem weighted_fourth_energy_tendsto_zero
    (κ : ℕ → Type*) [∀ n, Fintype (κ n)]
    (w : ∀ n, κ n → ℝ) (r : ∀ n, κ n → κ n → ℝ)
    (c W L B : ℕ → ℝ)
    (hW0 : ∀ n, 0 ≤ W n) (hL0 : ∀ n, 0 ≤ L n) (hB0 : ∀ n, 0 ≤ B n)
    (hW : ∀ n i, |w n i| ≤ W n) (hL : ∀ n, ∑ i, |w n i| ≤ L n)
    (hr : ∀ n i j, |r n i j| ≤ 1)
    (hrow : ∀ n i, ∑ j, r n i j ^ 2 ≤ B n)
    (hsmall : Tendsto (fun n => c n ^ 2 * (W n * L n * B n)) atTop (𝓝 0)) :
    Tendsto (fun n => c n ^ 2 *
      (∑ i, ∑ j, |w n i| * |w n j| * |r n i j| ^ 4)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => by positivity)))
  · intro n
    have h := weighted_fourth_energy_le (w n) (r n) (W n) (L n) (B n)
      (hW0 n) (hL0 n) (hB0 n) (hW n) (hL n) (hr n) (hrow n)
    exact mul_le_mul_of_nonneg_left h (sq_nonneg (c n))
  · convert hsmall using 1 <;> first | rfl | ring

end Hurst
