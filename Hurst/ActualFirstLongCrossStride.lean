import Hurst.FirstStrideGrid
import Hurst.FirstStrideMixed

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- Covariance perturbation for two first increments whose integer strides may
be different.  This is the rectangular counterpart of
`grid_stride_covariance_perturbation`. -/
theorem grid_cross_stride_covariance_perturbation
    (a b Bd Be d e : ℝ) (hd : 0 ≤ d) (he : 0 ≤ e)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hBd : 0 ≤ Bd) (hBe : 0 ≤ Be) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n →
      ∀ h h' k k' : Ioo (0 : ℝ) 1,
      (h : ℝ) ∈ Icc a b → (h' : ℝ) ∈ Icc a b →
      (k : ℝ) ∈ Icc a b → (k' : ℝ) ∈ Icc a b →
      ∀ s t : ℝ,
      s ∈ Icc (0 : ℝ) 1 → s + d / n ∈ Icc (0 : ℝ) 1 →
      t ∈ Icc (0 : ℝ) 1 → t + e / n ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n s → halfMeshPoint n (s + d / n) →
      halfMeshPoint n t → halfMeshPoint n (t + e / n) →
      |(h' : ℝ) - h| ≤ Bd / n → |(k' : ℝ) - k| ≤ Be / n →
      |⟪meshVaryingFirstIncrement n h h' s d,
          meshVaryingFirstIncrement n k k' t e⟫ -
        ⟪meshFrozenFirstIncrement n h s d,
          meshFrozenFirstIncrement n k t e⟫| ≤
        C * (1 + Real.log (2 * (n : ℝ))) *
          ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) := by
  obtain ⟨Kd, hKd, hmixd⟩ :=
    grid_stride_mixed_covariance_bound a b d hd ha hb hab
  obtain ⟨Ke, hKe, hmixe⟩ :=
    grid_stride_mixed_covariance_bound a b e he ha hb hab
  obtain ⟨D, hD, hrem⟩ :=
    harmonizableFeature_uniform_parameter_lipschitz a b ha hb hab
  refine ⟨Kd * Be * Real.exp Be + Ke * Bd * Real.exp Bd + D ^ 2 * Bd * Be,
    by positivity, ?_⟩
  intro n hn h h' k k' hh hh' hk hk' s t hs hs' ht ht'
    hsm hsm' htm htm' hhs hks
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let U := meshFrozenFirstIncrement n h s d
  let V := meshFrozenFirstIncrement n k t e
  let E := meshVaryingFirstIncrement n h h' s d - U
  let F := meshVaryingFirstIncrement n k k' t e - V
  let L := 1 + Real.log (2 * (n : ℝ))
  let R := (n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)
  have hL : 1 ≤ L := by
    dsimp [L]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hstepd (x : ℝ) : |x + d / n - x| ≤ d / (n : ℝ) := by
    rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
  have hstepe (x : ℝ) : |x + e / n - x| ≤ e / (n : ℝ) := by
    rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
  have hUF : |⟪U, F⟫| ≤ Kd * Be * Real.exp Be * L * R := by
    dsimp [U, F, V, L, R]
    rw [meshFrozenFirstIncrement, meshVaryingFirstIncrement_remainder]
    exact hmixd n hn h k k' hh hk hk' (s + d / n) s (t + e / n)
      Be hs' hs ht' hsm' hsm htm' (hstepd s) hBe
      (by rwa [abs_sub_comm])
  have hEV : |⟪E, V⟫| ≤ Ke * Bd * Real.exp Bd * L * R := by
    rw [real_inner_comm]
    dsimp [E, U, V, L, R]
    rw [meshFrozenFirstIncrement, meshVaryingFirstIncrement_remainder]
    exact hmixe n hn k h h' hk hh hh' (t + e / n) t (s + d / n)
      Bd ht' ht hs' htm' htm hsm' (hstepe t) hBd
      (by rwa [abs_sub_comm])
  have hnorm (f g : Ioo (0 : ℝ) 1)
      (hf : (f : ℝ) ∈ Icc a b) (hg : (g : ℝ) ∈ Icc a b)
      (x q B : ℝ) (hq : 0 ≤ q) (hx : x + q / n ∈ Icc (0 : ℝ) 1)
      (hB : 0 ≤ B) (hfg : |(g : ℝ) - f| ≤ B / n) :
      ‖meshVaryingFirstIncrement n f g x q -
          meshFrozenFirstIncrement n f x q‖ ≤
        D * B * (n : ℝ) ^ (b - 1) := by
    rw [meshVaryingFirstIncrement_remainder, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    have hparam := (hrem g f hg hf (x + q / n)
      (by rw [abs_of_nonneg hx.1]; exact hx.2)).trans
      (mul_le_mul_of_nonneg_left hfg hD)
    calc
      _ ≤ (n : ℝ) ^ (f : ℝ) * (D * (B / n)) :=
        mul_le_mul_of_nonneg_left hparam (Real.rpow_nonneg hn0.le _)
      _ ≤ (n : ℝ) ^ b * (D * (B / n)) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hn1 hf.2) (by positivity)
      _ = D * B * (n : ℝ) ^ (b - 1) := by
        rw [Real.rpow_sub hn0, Real.rpow_one]
        field_simp
        <;> ring
  have hE := hnorm h h' hh hh' s d Bd hd hs' hBd hhs
  have hF := hnorm k k' hk hk' t e Be he ht' hBe hks
  have hEF : |⟪E, F⟫| ≤ D ^ 2 * Bd * Be * L * R := by
    have hcs := (abs_real_inner_le_norm E F).trans
      (mul_le_mul hE hF (norm_nonneg _) (by positivity))
    have hid :
        (D * Bd * (n : ℝ) ^ (b - 1)) *
            (D * Be * (n : ℝ) ^ (b - 1)) =
          D ^ 2 * Bd * Be * (n : ℝ) ^ (2 * b - 2) := by
      calc
        _ = D ^ 2 * Bd * Be *
            ((n : ℝ) ^ (b - 1) * (n : ℝ) ^ (b - 1)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hn0]
          congr 2
          ring
    rw [hid] at hcs
    have hp : (n : ℝ) ^ (2 * b - 2) ≤ R := by
      dsimp [R]
      linarith [Real.rpow_nonneg hn0.le (-1)]
    have hp' : (n : ℝ) ^ (2 * b - 2) ≤ L * R := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) hR]
    exact hcs.trans (by
      have := mul_le_mul_of_nonneg_left hp'
        (by positivity : 0 ≤ D ^ 2 * Bd * Be)
      simpa only [mul_assoc] using this)
  have hid :
      ⟪meshVaryingFirstIncrement n h h' s d,
          meshVaryingFirstIncrement n k k' t e⟫ - ⟪U, V⟫ =
        ⟪U, F⟫ + ⟪E, V⟫ + ⟪E, F⟫ := by
    dsimp [E, F]
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    _ ≤ |⟪U, F⟫| + |⟪E, V⟫| + |⟪E, F⟫| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Kd * Be * Real.exp Be * L * R +
          Ke * Bd * Real.exp Bd * L * R + D ^ 2 * Bd * Be * L * R :=
      add_le_add (add_le_add hUF hEV) hEF
    _ = _ := by dsimp [L, R]; ring

/-- Normalized version of `grid_cross_stride_covariance_perturbation`.
The assumption that both strides are at least one makes the two normalization
factors contractions. -/
theorem normalized_cross_stride_covariance_perturbation
    (a b Bd Be d e : ℝ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hBd : 0 ≤ Bd) (hBe : 0 ≤ Be) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n →
      ∀ h h' k k' : Ioo (0 : ℝ) 1,
      (h : ℝ) ∈ Icc a b → (h' : ℝ) ∈ Icc a b →
      (k : ℝ) ∈ Icc a b → (k' : ℝ) ∈ Icc a b →
      ∀ s t : ℝ,
      s ∈ Icc (0 : ℝ) 1 → s + d / n ∈ Icc (0 : ℝ) 1 →
      t ∈ Icc (0 : ℝ) 1 → t + e / n ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n s → halfMeshPoint n (s + d / n) →
      halfMeshPoint n t → halfMeshPoint n (t + e / n) →
      |(h' : ℝ) - h| ≤ Bd / n → |(k' : ℝ) - k| ≤ Be / n →
      |⟪normalizedVaryingIncrement h h' s (d / n),
          normalizedVaryingIncrement k k' t (e / n)⟫ -
        ⟪normalizedFrozenIncrement h s (d / n),
          normalizedFrozenIncrement k t (e / n)⟫| ≤
        gridCovarianceError b C n := by
  obtain ⟨C, hC, hcov⟩ := grid_cross_stride_covariance_perturbation
    a b Bd Be d e (by linarith) (by linarith) ha hb hab hBd hBe
  refine ⟨C, hC, ?_⟩
  intro n hn h h' k k' hh hh' hk hk' s t hs hs' ht ht'
    hsm hsm' htm htm' hhs hks
  have hraw := hcov n hn h h' k k' hh hh' hk hk' s t hs hs' ht ht'
    hsm hsm' htm htm' hhs hks
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have he0 : 0 < e := zero_lt_one.trans_le he
  let r := d ^ (-(h : ℝ)) * e ^ (-(k : ℝ))
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    have h1 := Real.rpow_le_one_of_one_le_of_nonpos hd
      (neg_nonpos.mpr h.property.1.le)
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos he
      (neg_nonpos.mpr k.property.1.le)
    exact (mul_le_mul h1 h2 (by positivity) (by norm_num)).trans_eq (by ring)
  rw [normalizedVaryingIncrement_stride n hn d hd0,
    normalizedVaryingIncrement_stride n hn e he0,
    normalizedFrozenIncrement_stride n hn d hd0,
    normalizedFrozenIncrement_stride n hn e he0,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right]
  have hid :
      d ^ (-(h : ℝ)) *
            (e ^ (-(k : ℝ)) *
              ⟪meshVaryingFirstIncrement n h h' s d,
                meshVaryingFirstIncrement n k k' t e⟫) -
          d ^ (-(h : ℝ)) *
            (e ^ (-(k : ℝ)) *
              ⟪meshFrozenFirstIncrement n h s d,
                meshFrozenFirstIncrement n k t e⟫) =
        r * (⟪meshVaryingFirstIncrement n h h' s d,
                meshVaryingFirstIncrement n k k' t e⟫ -
              ⟪meshFrozenFirstIncrement n h s d,
                meshFrozenFirstIncrement n k t e⟫) := by
    dsimp [r]
    ring
  rw [hid, abs_mul, abs_of_nonneg hr0]
  exact (mul_le_mul_of_nonneg_left hraw hr0).trans
    (mul_le_of_le_one_left
      (by
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast (show 1 ≤ n by omega)
        have hlog : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
          linarith
        exact mul_nonneg (mul_nonneg hC hlog)
          (add_nonneg (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg (by positivity) _)))
      hr1)

/-- Model-specific normalized covariance perturbation for two possibly
different integer strides. -/
theorem hurstHolder_cross_stride_first_covariance
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ∃ C ≥ 0, ∀ n : ℕ, 0 < n →
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) →
      ∀ i : Fin (n - d), ∀ j : Fin (n - e),
      |⟪gridStrideFirstActual n d (midpointSampleHurst f hf.1 n) i,
          gridStrideFirstActual n e (midpointSampleHurst f hf.1 n) j⟫ -
        ⟪normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n d i))
            (grid n i.val) ((d : ℝ) / n),
          normalizedFrozenIncrement
            (midpointSampleHurst f hf.1 n (strideFirstLeft n e j))
            (grid n j.val) ((e : ℝ) / n)⟫| ≤
        gridCovarianceError b C n := by
  obtain ⟨L, hL, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  let Bd : ℝ := L * (1 + M) * d
  let Be : ℝ := L * (1 + M) * e
  have hBd : 0 ≤ Bd := by dsimp [Bd]; positivity
  have hBe : 0 ≤ Be := by dsimp [Be]; positivity
  obtain ⟨C, hC, hcov⟩ := normalized_cross_stride_covariance_perturbation
    a b Bd Be d e (by exact_mod_cast hd) (by exact_mod_cast he)
      ha hb hab hBd hBe
  refine ⟨C, hC, ?_⟩
  intro n hn f hf hF i j
  let H := midpointSampleHurst f hf.1 n
  have hlocd : grid n i.val ∈ Icc (0 : ℝ) 1 ∧
      grid n i.val + (d : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
    have hl := grid_mem n i.val hn (strideFirstLeft n d i).isLt
    have hr := grid_mem n _ hn (strideFirstRight n d i).isLt
    rw [grid_stride_first_step] at hr
    exact ⟨⟨hl.1.le, hl.2.le⟩, ⟨hr.1.le, hr.2.le⟩⟩
  have hloce : grid n j.val ∈ Icc (0 : ℝ) 1 ∧
      grid n j.val + (e : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
    have hl := grid_mem n j.val hn (strideFirstLeft n e j).isLt
    have hr := grid_mem n _ hn (strideFirstRight n e j).isLt
    rw [grid_stride_first_step] at hr
    exact ⟨⟨hl.1.le, hl.2.le⟩, ⟨hr.1.le, hr.2.le⟩⟩
  have hstepd : |(H (strideFirstRight n d i) : ℝ) -
      H (strideFirstLeft n d i)| ≤ Bd / n := by
    have hl := grid_mem n _ hn (strideFirstLeft n d i).isLt
    have hr := grid_mem n _ hn (strideFirstRight n d i).isLt
    have h := hLip M hM f hf 0
      (by have := hurstHolder_floor_pos p hp; omega) _ hl _ hr
    simp only [iteratedDeriv_zero, grid_stride_first_step, strideFirstLeft,
      add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ (d : ℝ) / n)] at h
    change |f (grid n (strideFirstRight n d i).val) - f (grid n i.val)| ≤ _
    rw [grid_stride_first_step]
    exact h.trans_eq (by dsimp [Bd]; ring)
  have hstepe : |(H (strideFirstRight n e j) : ℝ) -
      H (strideFirstLeft n e j)| ≤ Be / n := by
    have hl := grid_mem n _ hn (strideFirstLeft n e j).isLt
    have hr := grid_mem n _ hn (strideFirstRight n e j).isLt
    have h := hLip M hM f hf 0
      (by have := hurstHolder_floor_pos p hp; omega) _ hl _ hr
    simp only [iteratedDeriv_zero, grid_stride_first_step, strideFirstLeft,
      add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ (e : ℝ) / n)] at h
    change |f (grid n (strideFirstRight n e j).val) - f (grid n j.val)| ≤ _
    rw [grid_stride_first_step]
    exact h.trans_eq (by dsimp [Be]; ring)
  exact hcov n hn
    (H (strideFirstLeft n d i)) (H (strideFirstRight n d i))
    (H (strideFirstLeft n e j)) (H (strideFirstRight n e j))
    (hF (grid_mem n _ hn (strideFirstLeft n d i).isLt))
    (hF (grid_mem n _ hn (strideFirstRight n d i).isLt))
    (hF (grid_mem n _ hn (strideFirstLeft n e j).isLt))
    (hF (grid_mem n _ hn (strideFirstRight n e j).isLt))
    (grid n i.val) (grid n j.val)
    hlocd.1 hlocd.2 hloce.1 hloce.2
    (halfMeshPoint_grid n _)
    (by rw [← grid_stride_first_step]; exact halfMeshPoint_grid n _)
    (halfMeshPoint_grid n _)
    (by rw [← grid_stride_first_step]; exact halfMeshPoint_grid n _)
    hstepd hstepe

end Hurst
