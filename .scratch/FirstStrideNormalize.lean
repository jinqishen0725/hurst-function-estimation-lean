import Hurst.FirstStrideCovariance
import Hurst.GridCorrelationDecay

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem stride_normalization_factor (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 < d) (h : ℝ) :
    (d/(n:ℝ))^(-h) = d^(-h)*(n:ℝ)^h := by
  rw [Real.div_rpow hd.le (by positivity), Real.rpow_neg (by positivity : 0 ≤ (n:ℝ))]
  simp [div_eq_mul_inv]

theorem normalizedFrozenIncrement_stride (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 < d)
    (h : Ioo (0:ℝ) 1) (s : ℝ) :
    normalizedFrozenIncrement h s (d/n) = d^(-(h:ℝ)) • meshFrozenFirstIncrement n h s d := by
  unfold normalizedFrozenIncrement meshFrozenFirstIncrement
  rw [stride_normalization_factor n hn d hd, mul_smul]

theorem normalizedVaryingIncrement_stride (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 < d)
    (h k : Ioo (0:ℝ) 1) (s : ℝ) :
    normalizedVaryingIncrement h k s (d/n) = d^(-(h:ℝ)) • meshVaryingFirstIncrement n h k s d := by
  unfold normalizedVaryingIncrement meshVaryingFirstIncrement
  rw [stride_normalization_factor n hn d hd, mul_smul]

theorem normalized_stride_covariance_perturbation (a b B d : ℝ) (hd : 1 ≤ d)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n → ∀ h h' k k' : Ioo (0 : ℝ) 1,
      (h : ℝ) ∈ Icc a b → (h' : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b → (k' : ℝ) ∈ Icc a b →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → s + d / n ∈ Icc (0 : ℝ) 1 →
      t ∈ Icc (0 : ℝ) 1 → t + d / n ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n s → halfMeshPoint n (s + d / n) →
      halfMeshPoint n t → halfMeshPoint n (t + d / n) →
      |(h' : ℝ) - h| ≤ B / n → |(k' : ℝ) - k| ≤ B / n →
      |⟪normalizedVaryingIncrement h h' s (d/n), normalizedVaryingIncrement k k' t (d/n)⟫ -
        ⟪normalizedFrozenIncrement h s (d/n), normalizedFrozenIncrement k t (d/n)⟫| ≤
        gridCovarianceError b C n := by
  obtain ⟨C,hC,hcov⟩ := grid_stride_covariance_perturbation a b B d (by linarith) ha hb hab hB
  refine ⟨C,hC,?_⟩
  intro n hn h h' k k' hh hh' hk hk' s t hs hs' ht ht' hsm hsm' htm htm' hhs hks
  have hp := hcov n hn h h' k k' hh hh' hk hk' s t hs hs' ht ht' hsm hsm' htm htm' hhs hks
  have hd0 : 0 < d := by linarith
  let r := d^(-(h:ℝ))*d^(-(k:ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    have h1 := Real.rpow_le_one_of_one_le_of_nonpos hd (neg_nonpos.mpr h.property.1.le)
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos hd (neg_nonpos.mpr k.property.1.le)
    exact (mul_le_mul h1 h2 (by positivity) (by norm_num)).trans_eq (by ring)
  rw [normalizedVaryingIncrement_stride n hn d hd0, normalizedVaryingIncrement_stride n hn d hd0,
    normalizedFrozenIncrement_stride n hn d hd0, normalizedFrozenIncrement_stride n hn d hd0,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right]
  have hid : d^(-(h:ℝ))*(d^(-(k:ℝ))*⟪meshVaryingFirstIncrement n h h' s d, meshVaryingFirstIncrement n k k' t d⟫)-
      d^(-(h:ℝ))*(d^(-(k:ℝ))*⟪meshFrozenFirstIncrement n h s d, meshFrozenFirstIncrement n k t d⟫) =
      r*(⟪meshVaryingFirstIncrement n h h' s d, meshVaryingFirstIncrement n k k' t d⟫-⟪meshFrozenFirstIncrement n h s d, meshFrozenFirstIncrement n k t d⟫) := by dsimp [r]; ring
  rw [hid, abs_mul, abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left hp hr).trans (by
    change r*gridCovarianceError b C n ≤ gridCovarianceError b C n
    apply mul_le_of_le_one_left _ hr1
    unfold gridCovarianceError
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have := Real.log_nonneg (show (1:ℝ) ≤ 2*n by linarith)
    positivity)

end Hurst
