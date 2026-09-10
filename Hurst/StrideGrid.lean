import Hurst.SecondGridActual

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def strideSecondLeft (n d : ℕ) (i : Fin (n - 2*d)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def strideSecondMiddle (n d : ℕ) (i : Fin (n - 2*d)) : Fin n := ⟨i.val+d, by have := i.isLt; omega⟩
def strideSecondRight (n d : ℕ) (i : Fin (n - 2*d)) : Fin n := ⟨i.val+2*d, by have := i.isLt; omega⟩

theorem grid_stride_middle (n d : ℕ) (i : Fin (n - 2*d)) :
    grid n (strideSecondMiddle n d i).val = grid n i.val + (d : ℝ)/n := by
  simp only [grid, strideSecondMiddle, Nat.cast_add]
  ring

theorem grid_stride_right (n d : ℕ) (i : Fin (n - 2*d)) :
    grid n (strideSecondRight n d i).val = grid n i.val + 2*((d : ℝ)/n) := by
  simp only [grid, strideSecondRight, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

def gridStrideSecondActual (n d : ℕ) (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - 2*d)) : Lp ℂ 2 (volume : Measure ℝ) :=
  ((d : ℝ)/n) ^ (-(H (strideSecondLeft n d i) : ℝ)) •
    varyingSecondIncrement (H (strideSecondLeft n d i)) (H (strideSecondMiddle n d i)) (H (strideSecondRight n d i))
      (grid n i.val) ((d : ℝ)/n)

theorem stride_log_error_le_grid_error (d : ℕ) (hd : 0 < d) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (hn : d ≤ n) :
    C * ((d : ℝ)/n) * (1 + |Real.log ((d : ℝ)/n)|) ≤ gridCovarianceError (1/2) (C*d) n := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := hd0.trans_le (by exact_mod_cast hn)
  have hn1 : (1 : ℝ) ≤ n := hd1.trans (by exact_mod_cast hn)
  have hlogd := Real.log_nonneg hd1
  have hlogn := Real.log_nonneg hn1
  have hlogdn := Real.log_le_log hd0 (show (d : ℝ) ≤ n by exact_mod_cast hn)
  rw [Real.log_div (ne_of_gt hd0) (ne_of_gt hn0), abs_of_nonpos (sub_nonpos.mpr hlogdn)]
  have he := reciprocal_log_error_le_grid_error (C*d) (by positivity) n (by omega)
  rw [one_div, Real.log_inv, abs_neg, abs_of_nonneg hlogn] at he
  apply le_trans _ he
  have hm := mul_nonneg (show 0 ≤ C*((d:ℝ)/n) by positivity) hlogd
  rw [div_eq_mul_inv] at hm ⊢
  nlinarith

/-- The actual stride-d observation keeps the original grid; no smaller independent experiment is substituted. -/
theorem hurstHolder_grid_stride_second_remainder (p a b M : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) (d : ℕ) (hd : 0 < d) :
    ∃ C ≥ 0, ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ n : ℕ, d ≤ n → ∀ i : Fin (n - 2*d),
      ‖gridStrideSecondActual n d (midpointSampleHurst f hf.1 n) i -
        normalizedFrozenSecondIncrement (midpointSampleHurst f hf.1 n (strideSecondLeft n d i))
          (grid n i.val) ((d : ℝ)/n)‖ ≤ gridCovarianceError (1/2) C n := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_second_increment_remainder p a b M hp ha hb hab hM
  refine ⟨C*d, by positivity, ?_⟩
  intro f hf hF n hn i
  have hnpos : 0 < n := lt_of_lt_of_le hd hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ht := grid_mem n i.val hnpos (strideSecondLeft n d i).isLt
  have ht2 : grid n i.val + 2*((d:ℝ)/n) ∈ Ioo (0 : ℝ) 1 := by
    rw [← grid_stride_right]
    exact grid_mem n _ hnpos (strideSecondRight n d i).isLt
  let H := midpointSampleHurst f hf.1 n
  have he := hc f hf hF (grid n i.val) ((d:ℝ)/n) (by positivity) ht ht2
    (H (strideSecondLeft n d i)) (H (strideSecondMiddle n d i)) (H (strideSecondRight n d i))
    rfl (by dsimp [H, midpointSampleHurst]; rw [grid_stride_middle])
    (by dsimp [H, midpointSampleHurst]; rw [grid_stride_right])
  have hid : gridStrideSecondActual n d H i - normalizedFrozenSecondIncrement (H (strideSecondLeft n d i)) (grid n i.val) ((d:ℝ)/n) =
      ((d:ℝ)/n)^(-(H (strideSecondLeft n d i):ℝ)) •
      (varyingSecondIncrement (H (strideSecondLeft n d i)) (H (strideSecondMiddle n d i)) (H (strideSecondRight n d i))
        (grid n i.val) ((d:ℝ)/n) - frozenSecondIncrement (H (strideSecondLeft n d i)) (grid n i.val) ((d:ℝ)/n)) := by
    unfold gridStrideSecondActual normalizedFrozenSecondIncrement
    rw [smul_sub]
  rw [hid]
  exact he.trans (stride_log_error_le_grid_error d hd C hC n hn)

end Hurst
