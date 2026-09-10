import Hurst.GridMixedCovariance
import Hurst.VaryingIncrement

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem inverse_mesh_rpow (n : ℕ) (hn : 0 < n) (p : ℝ) :
    (1 / (n : ℝ)) ^ p = (n : ℝ) ^ (-p) := by
  rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

theorem normalizedFrozenIncrement_grid (h : Ioo (0 : ℝ) 1) (s : ℝ) (n : ℕ) (hn : 0 < n) :
    normalizedFrozenIncrement h s (1 / n) = ((n : ℝ) ^ (h : ℝ)) •
      (harmonizableFeature h (s + 1 / n) - harmonizableFeature h s) := by
  rw [normalizedFrozenIncrement, inverse_mesh_rpow n hn, neg_neg]

theorem normalizedVaryingIncrement_grid_remainder (h k : Ioo (0 : ℝ) 1) (s : ℝ) (n : ℕ) (hn : 0 < n) :
    normalizedVaryingIncrement h k s (1 / n) - normalizedFrozenIncrement h s (1 / n) =
      ((n : ℝ) ^ (h : ℝ)) • (harmonizableFeature k (s + 1 / n) - harmonizableFeature h (s + 1 / n)) := by
  rw [normalizedVaryingIncrement, normalizedFrozenIncrement, inverse_mesh_rpow n hn, neg_neg]
  module

/-- Uniform covariance perturbation of actual varying-parameter increments, including locations near zero. -/
theorem grid_increment_covariance_perturbation (a b B : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → ∀ h h' k k' : Ioo (0 : ℝ) 1,
      (h : ℝ) ∈ Icc a b → (h' : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b → (k' : ℝ) ∈ Icc a b →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → s + 1 / n ∈ Icc (0 : ℝ) 1 →
      t ∈ Icc (0 : ℝ) 1 → t + 1 / n ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n s → halfMeshPoint n (s + 1 / n) →
      halfMeshPoint n t → halfMeshPoint n (t + 1 / n) →
      |(h' : ℝ) - h| ≤ B / n → |(k' : ℝ) - k| ≤ B / n →
      |⟪normalizedVaryingIncrement h h' s (1 / n), normalizedVaryingIncrement k k' t (1 / n)⟫ -
        ⟪normalizedFrozenIncrement h s (1 / n), normalizedFrozenIncrement k t (1 / n)⟫| ≤
      C * (1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := by
  obtain ⟨K, hK, hmix⟩ := grid_mixed_covariance_bound a b ha hb hab
  obtain ⟨D, hD, hrem⟩ := normalizedVaryingIncrement_uniform_remainder a b ha hb hab
  refine ⟨2 * K * B * Real.exp B + (D * B) ^ 2, by positivity, ?_⟩
  intro n hn h h' k k' hh hh' hk hk' s t hs hs' ht ht' hsm hsm' htm htm' hhs hks
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let U := normalizedFrozenIncrement h s (1 / n)
  let V := normalizedFrozenIncrement k t (1 / n)
  let E := normalizedVaryingIncrement h h' s (1 / n) - U
  let F := normalizedVaryingIncrement k k' t (1 / n) - V
  let L := 1 + Real.log (2 * (n : ℝ))
  let R := (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)
  have hL : 1 ≤ L := by dsimp [L]; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith); linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hstep (x : ℝ) : |x + 1 / n - x| ≤ 1 / (n : ℝ) := by rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
  have hEF : |⟪U, F⟫| ≤ K * B * Real.exp B * L * R := by
    dsimp [U, F, V, L, R]
    rw [normalizedFrozenIncrement_grid h s n hn, normalizedVaryingIncrement_grid_remainder k k' t n hn]
    exact hmix n hn h k k' hh hk hk' (s + 1 / n) s (t + 1 / n) B hs' hs ht' hsm' hsm htm'
      (hstep s) hB (by rwa [abs_sub_comm])
  have hEU : |⟪E, V⟫| ≤ K * B * Real.exp B * L * R := by
    rw [real_inner_comm]
    dsimp [E, U, V, L, R]
    rw [normalizedFrozenIncrement_grid k t n hn, normalizedVaryingIncrement_grid_remainder h h' s n hn]
    exact hmix n hn k h h' hk hh hh' (t + 1 / n) t (s + 1 / n) B ht' ht hs' htm' htm hsm'
      (hstep t) hB (by rwa [abs_sub_comm])
  have hnstep : (1 / (n : ℝ)) ≤ 1 := (div_le_one hn0).mpr hn1
  have hnorm (f g : Ioo (0 : ℝ) 1) (hf : (f : ℝ) ∈ Icc a b) (hg : (g : ℝ) ∈ Icc a b)
      (x : ℝ) (hx : x + 1 / n ∈ Icc (0 : ℝ) 1) (hfg : |(g : ℝ) - f| ≤ B / n) :
      ‖normalizedVaryingIncrement f g x (1 / n) - normalizedFrozenIncrement f x (1 / n)‖ ≤ D * B * (n : ℝ) ^ (b - 1) := by
    have he := hrem f g hf hg x (1 / n) B (by rw [abs_of_nonneg hx.1]; exact hx.2) (by positivity) hnstep hB (by simpa only [div_eq_mul_inv, one_mul] using hfg)
    rw [inverse_mesh_rpow n hn, show -(1 - b) = b - 1 by ring] at he
    exact he
  have hE := hnorm h h' hh hh' s hs' hhs
  have hF := hnorm k k' hk hk' t ht' hks
  have hprod : |⟪E, F⟫| ≤ (D * B) ^ 2 * L * R := by
    have hcs := (abs_real_inner_le_norm E F).trans (mul_le_mul hE hF (norm_nonneg _) (by positivity))
    have hid : (D * B * (n : ℝ) ^ (b - 1)) * (D * B * (n : ℝ) ^ (b - 1)) = (D * B) ^ 2 * (n : ℝ) ^ (2 * b - 2) := by
      calc
        _ = (D * B) ^ 2 * ((n : ℝ) ^ (b - 1) * (n : ℝ) ^ (b - 1)) := by ring
        _ = _ := by rw [← Real.rpow_add hn0]; congr 2; ring
    rw [hid] at hcs
    have hpr : (n : ℝ) ^ (2 * b - 2) ≤ R := by dsimp [R]; linarith [Real.rpow_nonneg hn0.le (-1)]
    apply hcs.trans
    have he' : (n : ℝ) ^ (2 * b - 2) ≤ L * R := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) hR]
    have := mul_le_mul_of_nonneg_left he' (sq_nonneg (D * B))
    simpa only [mul_assoc] using this
  have hid : ⟪normalizedVaryingIncrement h h' s (1 / n), normalizedVaryingIncrement k k' t (1 / n)⟫ - ⟪U, V⟫ =
      ⟪U, F⟫ + ⟪E, V⟫ + ⟪E, F⟫ := by
    dsimp [E, F]
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    _ ≤ |⟪U, F⟫| + |⟪E, V⟫| + |⟪E, F⟫| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K * B * Real.exp B * L * R + K * B * Real.exp B * L * R + (D * B) ^ 2 * L * R := add_le_add (add_le_add hEF hEU) hprod
    _ = _ := by dsimp [L, R]; ring

end Hurst
