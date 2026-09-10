import Hurst.ActualFirstLongCrossStride
import Hurst.ActualFirstLongCorrelationPerturbation
import Hurst.FirstLongTwoStrideKernel
import Hurst.ActiveSetReindex

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- Uniform local Hurst drift on the common q=2 active window used by both
first-increment pilot strides. -/
theorem hurstHolder_common_q2_active_hurst_drift
    (p M : ℝ) (hp : 1 ≤ p) (hM : 0 ≤ M) :
    ∃ L > 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      ∀ d : ℕ, ∀ hd : d ≤ 2,
      ∀ n : ℕ, 0 < n → ∀ δ t : ℝ, 0 < δ → t ∈ Ioo (0 : ℝ) 1 →
      ∀ i : Fin (localWeightActiveSet n 2 δ t).card,
      |(midpointSampleHurst f hf.1 n
          (strideFirstLeft n d
            (commonFirstStrideIndex n d 2 hd
              (localWeightActiveIndex n 2 δ t i))) : ℝ) - f t| ≤
        L * (1 + M) * δ := by
  obtain ⟨L, hL, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  refine ⟨L, hL, ?_⟩
  intro f hf d hd n hn δ t hδ ht i
  let ii := localWeightActiveIndex n 2 δ t i
  have hgrid := grid_mem n ii.val hn
    (strideFirstLeft n d (commonFirstStrideIndex n d 2 hd ii)).isLt
  have hactive :=
    (Finset.mem_filter.mp (localWeightActiveIndex_mem n 2 δ t i)).2
  have hdist : |grid n ii.val - t| < δ := by
    calc
      _ = δ * |(grid n ii.val - t) / δ| := by
        rw [abs_div, abs_of_pos hδ]
        field_simp
      _ < δ * 1 := mul_lt_mul_of_pos_left hactive hδ
      _ = δ := mul_one δ
  have h := hLip M hM f hf 0
    (by have := hurstHolder_floor_pos p hp; omega)
    t ht (grid n ii.val) hgrid
  simp only [iteratedDeriv_zero] at h
  change |f (grid n ii.val) - f t| ≤ L * (1 + M) * δ
  exact h.trans (mul_le_mul_of_nonneg_left hdist.le (by positivity))

/-- Any two indices in a local active window are separated by less than twice
the effective local sample size.  The statement is uniform in the cutoff q. -/
theorem localWeightActiveIndex_dist_lt_two_effective_general
    (n q : ℕ) (δ t : ℝ) (hδ : 0 < δ)
    (i j : Fin (localWeightActiveSet n q δ t).card) :
    (Nat.dist
        (localWeightActiveIndex n q δ t i).val
        (localWeightActiveIndex n q δ t j).val : ℝ) <
      2 * ((n : ℝ) * δ) := by
  let ii := localWeightActiveIndex n q δ t i
  let jj := localWeightActiveIndex n q δ t j
  have hi := (Finset.mem_filter.mp (localWeightActiveIndex_mem n q δ t i)).2
  have hj := (Finset.mem_filter.mp (localWeightActiveIndex_mem n q δ t j)).2
  have hi' : |grid n ii.val - t| < δ := by
    calc
      _ = δ * |(grid n ii.val - t) / δ| := by
        rw [abs_div, abs_of_pos hδ]
        field_simp
      _ < δ * 1 := mul_lt_mul_of_pos_left hi hδ
      _ = δ := mul_one δ
  have hj' : |grid n jj.val - t| < δ := by
    calc
      _ = δ * |(grid n jj.val - t) / δ| := by
        rw [abs_div, abs_of_pos hδ]
        field_simp
      _ < δ * 1 := mul_lt_mul_of_pos_left hj hδ
      _ = δ := mul_one δ
  have hn : 0 < n := by have := ii.isLt; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgrid : |grid n ii.val - grid n jj.val| =
      (Nat.dist ii.val jj.val : ℝ) / n := by
    unfold grid
    rcases le_total ii.val jj.val with hij | hji
    · have hijR : (ii.val : ℝ) ≤ jj.val := by exact_mod_cast hij
      rw [show ((ii.val : ℝ) + 1 / 2) / n -
          ((jj.val : ℝ) + 1 / 2) / n =
          ((ii.val : ℝ) - jj.val) / n by ring,
        abs_div, abs_of_pos hnR,
        abs_of_nonpos (sub_nonpos.mpr hijR),
        Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij]
      ring
    · have hjiR : (jj.val : ℝ) ≤ ii.val := by exact_mod_cast hji
      rw [show ((ii.val : ℝ) + 1 / 2) / n -
          ((jj.val : ℝ) + 1 / 2) / n =
          ((ii.val : ℝ) - jj.val) / n by ring,
        abs_div, abs_of_pos hnR,
        abs_of_nonneg (sub_nonneg.mpr hjiR),
        Nat.dist_eq_sub_of_le_right hji, Nat.cast_sub hji]
  have htri : |grid n ii.val - grid n jj.val| < 2 * δ := by
    calc
      _ = |(grid n ii.val - t) - (grid n jj.val - t)| := by ring_nf
      _ ≤ |grid n ii.val - t| + |grid n jj.val - t| := abs_sub _ _
      _ < δ + δ := add_lt_add hi' hj'
      _ = 2 * δ := by ring
  rw [hgrid] at htri
  have hscaled := (div_lt_iff₀ hnR).mp htri
  dsimp only [ii, jj] at hscaled ⊢
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Actual-to-frozen correlation control for two possibly different first-
increment strides.  The diagonal estimates used by normalization are obtained
from the corresponding equal-stride covariance estimates. -/
theorem hurstHolder_cross_stride_first_correlation_perturbation
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → gridCovarianceError b C n ≤ 1 / 2 →
      ∀ i : Fin (n - d), ∀ j : Fin (n - e),
      |vectorCorrelation
          (gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i)
          (gridStrideFirstActual n e (midpointSampleHurst f hf.1 n) j) -
        ⟪normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n d i))
            (grid n i.val) ((d : ℝ) / n),
          normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n e j))
            (grid n j.val) ((e : ℝ) / n)⟫| ≤
        4 * gridCovarianceError b C n := by
  obtain ⟨Cde, hCde, hcde⟩ :=
    hurstHolder_cross_stride_first_covariance
      p a b M hp ha hb hab hM d e hd he
  obtain ⟨Cd, hCd, hcd⟩ :=
    hurstHolder_cross_stride_first_covariance
      p a b M hp ha hb hab hM d d hd hd
  obtain ⟨Ce, hCe, hce⟩ :=
    hurstHolder_cross_stride_first_covariance
      p a b M hp ha hb hab hM e e he he
  let C := Cde + Cd + Ce
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn hsmall i j
  let H := midpointSampleHurst f hf.1 n
  let U := gridStrideFirstActual n d H i
  let V := gridStrideFirstActual n e H j
  let A := normalizedFrozenIncrement (H (strideFirstLeft n d i))
    (grid n i.val) ((d : ℝ) / n)
  let B := normalizedFrozenIncrement (H (strideFirstLeft n e j))
    (grid n j.val) ((e : ℝ) / n)
  have hbase : 0 ≤ (1 + Real.log (2 * (n : ℝ))) *
      ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    positivity
  have hmono (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (hC₁C : C₁ ≤ C) :
      gridCovarianceError b C₁ n ≤ gridCovarianceError b C n := by
    unfold gridCovarianceError
    calc
      C₁ * (1 + Real.log (2 * (n : ℝ))) *
          ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) =
        C₁ * ((1 + Real.log (2 * (n : ℝ))) *
          ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))) := by ring
      _ ≤ C * ((1 + Real.log (2 * (n : ℝ))) *
          ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))) :=
        mul_le_mul_of_nonneg_right hC₁C hbase
      _ = _ := by ring
  have hde := hcde n hn f hf hF i j
  have hdd := hcd n hn f hf hF i i
  have hee := hce n hn f hf hF j j
  have hde' := hde.trans (hmono Cde hCde (by dsimp [C]; linarith))
  have hdd' := hdd.trans (hmono Cd hCd (by dsimp [C]; linarith))
  have hee' := hee.trans (hmono Ce hCe (by dsimp [C]; linarith))
  have hstepd : 0 < (d : ℝ) / n := by positivity
  have hstepe : 0 < (e : ℝ) / n := by positivity
  have hAA : ‖A‖ ^ 2 = 1 :=
    normalizedFrozenIncrement_norm_sq _ _ _ hstepd
  have hBB : ‖B‖ ^ 2 = 1 :=
    normalizedFrozenIncrement_norm_sq _ _ _ hstepe
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hdd' hee'
  exact vectorCorrelation_sub_unitGram_le U V A B
    (gridCovarianceError b C n)
    (by
      unfold gridCovarianceError
      simpa only [mul_assoc] using mul_nonneg hC hbase) hsmall hAA hBB
    (by simpa only [U, A, H] using hdd')
    (by simpa only [V, B, H] using hee')
    (by simpa only [U, V, A, B, H] using hde')

/-- Exact frozen covariance formula when the left endpoint of the stride-`d`
increment precedes that of the stride-`e` increment. -/
theorem normalizedFrozenIncrement_grid_inner_eq_two_stride_cross_lag_of_le
    (n d e : ℕ) (hn : 0 < n) (hd : 0 < d) (he : 0 < e)
    (H : Fin n → Ioo (0 : ℝ) 1)
    (i : Fin (n - d)) (j : Fin (n - e)) (hij : i.val ≤ j.val) :
    ⟪normalizedFrozenIncrement (H (strideFirstLeft n d i))
        (grid n i.val) ((d : ℝ) / n),
      normalizedFrozenIncrement (H (strideFirstLeft n e j))
        (grid n j.val) ((e : ℝ) / n)⟫ =
      firstIncrementTwoStrideCrossLagCorrelation
        (H (strideFirstLeft n d i)) (H (strideFirstLeft n e j)) d e
        (Nat.dist i.val j.val) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hgrid : grid n j.val = grid n i.val +
      (j.val - i.val : ℕ) * (1 / (n : ℝ)) := by
    unfold grid
    rw [Nat.cast_sub hij]
    field_simp
    ring
  rw [Nat.dist_eq_sub_of_le hij, hgrid]
  have hform := normalizedFrozenIncrement_two_stride_cross_lag
    (H (strideFirstLeft n d i)) (H (strideFirstLeft n e j))
    (grid n i.val) (1 / (n : ℝ)) d e (j.val - i.val : ℕ)
    (by positivity) hdR heR
  convert hform using 1 <;> ring

end Hurst
