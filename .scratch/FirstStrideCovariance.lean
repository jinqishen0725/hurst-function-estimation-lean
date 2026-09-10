import Hurst.FirstStrideMixed
import Hurst.GridCovariancePerturb

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

def meshFrozenFirstIncrement (n : ℕ) (h : Ioo (0:ℝ) 1) (s d : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (n:ℝ)^(h:ℝ) • (harmonizableFeature h (s+d/n)-harmonizableFeature h s)

def meshVaryingFirstIncrement (n : ℕ) (h k : Ioo (0:ℝ) 1) (s d : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (n:ℝ)^(h:ℝ) • (harmonizableFeature k (s+d/n)-harmonizableFeature h s)

theorem meshVaryingFirstIncrement_remainder (n : ℕ) (h k : Ioo (0:ℝ) 1) (s d : ℝ) :
    meshVaryingFirstIncrement n h k s d - meshFrozenFirstIncrement n h s d =
      (n:ℝ)^(h:ℝ) • (harmonizableFeature k (s+d/n)-harmonizableFeature h (s+d/n)) := by
  unfold meshVaryingFirstIncrement meshFrozenFirstIncrement
  module

/-- Uniform covariance perturbation of actual varying-parameter increments, including locations near zero. -/
theorem grid_stride_covariance_perturbation (a b B d : ℝ) (hd : 0 ≤ d)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → ∀ h h' k k' : Ioo (0 : ℝ) 1,
      (h : ℝ) ∈ Icc a b → (h' : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b → (k' : ℝ) ∈ Icc a b →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → s + d / n ∈ Icc (0 : ℝ) 1 →
      t ∈ Icc (0 : ℝ) 1 → t + d / n ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n s → halfMeshPoint n (s + d / n) →
      halfMeshPoint n t → halfMeshPoint n (t + d / n) →
      |(h' : ℝ) - h| ≤ B / n → |(k' : ℝ) - k| ≤ B / n →
      |⟪meshVaryingFirstIncrement n h h' s d, meshVaryingFirstIncrement n k k' t d⟫ -
        ⟪meshFrozenFirstIncrement n h s d, meshFrozenFirstIncrement n k t d⟫| ≤
      C * (1 + Real.log (2 * (n : ℝ))) * ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := by
  obtain ⟨K, hK, hmix⟩ := grid_stride_mixed_covariance_bound a b d hd ha hb hab
  obtain ⟨D, hD, hrem⟩ := harmonizableFeature_uniform_parameter_lipschitz a b ha hb hab
  refine ⟨2 * K * B * Real.exp B + (D * B) ^ 2, by positivity, ?_⟩
  intro n hn h h' k k' hh hh' hk hk' s t hs hs' ht ht' hsm hsm' htm htm' hhs hks
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let U := meshFrozenFirstIncrement n h s d
  let V := meshFrozenFirstIncrement n k t d
  let E := meshVaryingFirstIncrement n h h' s d - U
  let F := meshVaryingFirstIncrement n k k' t d - V
  let L := 1 + Real.log (2 * (n : ℝ))
  let R := (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)
  have hL : 1 ≤ L := by dsimp [L]; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith); linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hstep (x : ℝ) : |x + d / n - x| ≤ d / (n : ℝ) := by rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
  have hEF : |⟪U, F⟫| ≤ K * B * Real.exp B * L * R := by
    dsimp [U, F, V, L, R]
    rw [meshFrozenFirstIncrement, meshVaryingFirstIncrement_remainder]
    exact hmix n hn h k k' hh hk hk' (s + d / n) s (t + d / n) B hs' hs ht' hsm' hsm htm'
      (hstep s) hB (by rwa [abs_sub_comm])
  have hEU : |⟪E, V⟫| ≤ K * B * Real.exp B * L * R := by
    rw [real_inner_comm]
    dsimp [E, U, V, L, R]
    rw [meshFrozenFirstIncrement, meshVaryingFirstIncrement_remainder]
    exact hmix n hn k h h' hk hh hh' (t + d / n) t (s + d / n) B ht' ht hs' htm' htm hsm'
      (hstep t) hB (by rwa [abs_sub_comm])
  have hnorm (f g : Ioo (0 : ℝ) 1) (hf : (f : ℝ) ∈ Icc a b) (hg : (g : ℝ) ∈ Icc a b)
      (x : ℝ) (hx : x + d / n ∈ Icc (0 : ℝ) 1) (hfg : |(g : ℝ) - f| ≤ B / n) :
      ‖meshVaryingFirstIncrement n f g x d - meshFrozenFirstIncrement n f x d‖ ≤ D * B * (n : ℝ) ^ (b - 1) := by
    rw [meshVaryingFirstIncrement_remainder, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    have hparam := (hrem g f hg hf (x+d/n) (by rw [abs_of_nonneg hx.1]; exact hx.2)).trans
      (mul_le_mul_of_nonneg_left hfg hD)
    calc
      _ ≤ (n:ℝ)^(f:ℝ) * (D*(B/n)) := mul_le_mul_of_nonneg_left hparam (by positivity)
      _ ≤ (n:ℝ)^b * (D*(B/n)) := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 hf.2) (by positivity)
      _ = D*B*(n:ℝ)^(b-1) := by rw [Real.rpow_sub hn0, Real.rpow_one]; ring
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
  have hid : ⟪meshVaryingFirstIncrement n h h' s d, meshVaryingFirstIncrement n k k' t d⟫ - ⟪U, V⟫ =
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
