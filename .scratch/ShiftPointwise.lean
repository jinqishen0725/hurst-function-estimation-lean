import Hurst.ShiftedWeightEnergy

noncomputable section
open Filter
open scoped Topology
namespace Hurst

theorem localPolynomialWeights_fixedShift_pointwise
    (r n q k : ℕ) (δ t D : ℝ) (hn : 0 < n) (hδ : 0 < δ) (hD : 0 ≤ D)
    (L : Fin (r + 1) → NNReal)
    (hL : ∀ j, LipschitzWith (L j) (kernelMomentFunction j.val))
    (hinv : ∀ j : Fin (r + 1), |(localDesignGram r n q δ t)⁻¹ 0 j| ≤ D)
    (i : Fin (n - q)) (hik : i.val + k < n - q) :
    |localPolynomialWeights r n q δ t ⟨i.val + k, hik⟩ -
        localPolynomialWeights r n q δ t i| ≤
      ((n : ℝ) * δ)⁻¹ * ∑ j : Fin (r + 1),
        D * (L j : ℝ) * ((k : ℝ) / ((n : ℝ) * δ)) := by
  let N : ℝ := (n : ℝ) * δ
  have hN : 0 < N := by
    dsimp [N]
    positivity
  let x : ℝ := (grid n i.val - t) / δ
  have hxshift : (grid n (i.val + k) - t) / δ =
      x + (k : ℝ) / N := by
    dsimp [x, N]
    exact normalized_grid_fixedShift n i.val k δ t hn hδ
  rw [localPolynomialWeights_formula_kernelMoments,
    localPolynomialWeights_formula_kernelMoments, hxshift]
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hN.le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN.le)
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub, abs_mul]
  have hLip := (hL j).norm_sub_le (x + (k : ℝ) / N) x
  have hstep : |kernelMomentFunction j.val (x + (k : ℝ) / N) -
      kernelMomentFunction j.val x| ≤ (L j : ℝ) * ((k : ℝ) / N) := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left,
      abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) / N)] using hLip
  dsimp [x, N] at hstep ⊢
  exact (mul_le_mul (hinv j) hstep (abs_nonneg _) hD).trans_eq (by ring)

end Hurst
