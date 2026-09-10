import Hurst.SpectralMajorant

/-! Actual frozen and varying-Hurst increments for the minimax covariance decomposition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace Hurst

def frozenIncrementFeature (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (Real.sqrt ℓ)⁻¹ • (harmonizableFeature h (s + ℓ) - harmonizableFeature h s)

def hurstVariationFeature (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (Real.sqrt ℓ)⁻¹ • (harmonizableFeature h s - harmonizableFeature k s)

def whitenedIncrementFeature (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (Real.sqrt ℓ)⁻¹ • (harmonizableFeature h (s + ℓ) - harmonizableFeature k s)

theorem whitenedIncrementFeature_decomposition (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) :
    whitenedIncrementFeature h k s ℓ = frozenIncrementFeature h s ℓ + hurstVariationFeature h k s ℓ := by
  unfold whitenedIncrementFeature frozenIncrementFeature hurstVariationFeature
  module

theorem frozenIncrementFeature_norm_sq (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (hl : 0 < ℓ) :
    ‖frozenIncrementFeature h s ℓ‖ ^ 2 = ℓ ^ (2 * (h : ℝ) - 1) := by
  rw [frozenIncrementFeature, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hl.le, harmonizableFeature_increment_norm_sq, add_sub_cancel_left, abs_of_pos hl,
    Real.rpow_sub hl, Real.rpow_one]
  ring

/-- The norm of the varying-Hurst column follows from the proved uniform spectral bound. -/
theorem hurstVariationFeature_uniform_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s ℓ B : ℝ, |s| ≤ 1 → 0 < ℓ → 0 ≤ B → |(h : ℝ) - k| ≤ B * ℓ →
        ‖hurstVariationFeature h k s ℓ‖ ≤ (C * B) * Real.sqrt ℓ := by
  obtain ⟨C, hC, hLip⟩ := harmonizableFeature_uniform_parameter_lipschitz a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro h k hh hk s ℓ B hs hl hB hhk
  rw [hurstVariationFeature, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt ℓ)⁻¹ * (C * |(h : ℝ) - k|) :=
      mul_le_mul_of_nonneg_left (hLip h k hh hk s hs) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ (Real.sqrt ℓ)⁻¹ * (C * (B * ℓ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhk hC)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (C * B) * Real.sqrt ℓ := by
      have he := Real.sq_sqrt hl.le
      have hn := (Real.sqrt_pos.mpr hl).ne'
      field_simp
      rw [he]
      ring

/-- Finite-dimensional Cauchy-Schwarz, without a factor depending on the number of columns. -/
theorem featureCombination_norm_le_of_energy_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : ι → E) (w : EuclideanSpace ℝ ι)
    (K : ℝ) (hK : 0 ≤ K) (henergy : ∑ i, ‖v i‖ ^ 2 ≤ K ^ 2) :
    ‖∑ i, w i • v i‖ ≤ K * ‖w‖ := by
  have hn : ‖∑ i, w i • v i‖ ≤ ∑ i, |w i| * ‖v i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le (s := Finset.univ) (f := fun i => w i • v i)
  have hs : 0 ≤ ∑ i, |w i| * ‖v i‖ := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |w i|) (fun i => ‖v i‖)
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq] at hc
  have he := mul_le_mul_of_nonneg_left henergy (sq_nonneg ‖w‖)
  have hkp : 0 ≤ K * ‖w‖ := mul_nonneg hK (norm_nonneg _)
  nlinarith [norm_nonneg (∑ i, w i • v i)]

/-- File 20's varying-Hurst operator estimate, with one constant for all sample sizes. -/
theorem hurstVariationFeature_uniform_operator_bound (a b : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ n : ℕ, ∀ h k : Fin n → Ioo (0 : ℝ) 1, ∀ s ℓ : Fin n → ℝ,
      ∀ B : ℝ, 0 ≤ B →
      (∀ i, (h i : ℝ) ∈ Icc a b) → (∀ i, (k i : ℝ) ∈ Icc a b) →
      (∀ i, |s i| ≤ 1) → (∀ i, 0 < ℓ i) → (∑ i, ℓ i) ≤ 1 →
      (∀ i, |(h i : ℝ) - k i| ≤ B * ℓ i) →
      ∀ w : EuclideanSpace ℝ (Fin n),
        ‖∑ i, w i • hurstVariationFeature (h i) (k i) (s i) (ℓ i)‖ ≤ (C * B) * ‖w‖ := by
  obtain ⟨C, hC, hcol⟩ := hurstVariationFeature_uniform_bound a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro n h k s ℓ B hB hh hk hs hl hsum hstep w
  apply featureCombination_norm_le_of_energy_bound _ w (C * B) (mul_nonneg hC hB)
  have hsq : ∀ i, ‖hurstVariationFeature (h i) (k i) (s i) (ℓ i)‖ ^ 2 ≤ (C * B) ^ 2 * ℓ i := by
    intro i
    have hn := hcol (h i) (k i) (hh i) (hk i) (s i) (ℓ i) B (hs i) (hl i) hB (hstep i)
    calc
      _ ≤ ((C * B) * Real.sqrt (ℓ i)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt (hl i).le]
  calc
    _ ≤ ∑ i, (C * B) ^ 2 * ℓ i := Finset.sum_le_sum fun i _ => hsq i
    _ = (C * B) ^ 2 * ∑ i, ℓ i := (Finset.mul_sum _ _ _).symm
    _ ≤ (C * B) ^ 2 := by nlinarith [sq_nonneg (C * B)]

/-- Exact covariance decomposition for the actual increment features. -/
theorem whitenedIncrementFeature_covariance_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h k : ι → Ioo (0 : ℝ) 1) (s ℓ : ι → ℝ) (i j : ι) :
    cov[fun x => x i, fun x => x j;
      featureGaussian (fun r => whitenedIncrementFeature (h r) (k r) (s r) (ℓ r))] =
      ⟪frozenIncrementFeature (h i) (s i) (ℓ i), frozenIncrementFeature (h j) (s j) (ℓ j)⟫ +
      ⟪frozenIncrementFeature (h i) (s i) (ℓ i), hurstVariationFeature (h j) (k j) (s j) (ℓ j)⟫ +
      ⟪hurstVariationFeature (h i) (k i) (s i) (ℓ i), frozenIncrementFeature (h j) (s j) (ℓ j)⟫ +
      ⟪hurstVariationFeature (h i) (k i) (s i) (ℓ i), hurstVariationFeature (h j) (k j) (s j) (ℓ j)⟫ := by
  rw [featureGaussian_covariance, whitenedIncrementFeature_decomposition, whitenedIncrementFeature_decomposition]
  simp only [inner_add_left, inner_add_right]
  ring

end Hurst
