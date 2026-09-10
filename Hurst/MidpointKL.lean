import Hurst.MidpointFrobenius
import Hurst.GaussianScale
import Mathlib.Order.LiminfLimsup

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology ENNReal
namespace Hurst

theorem midpoint_log_lower_bound (n : ℕ) (hn : 0 < n) :
    (1 / 2 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at he
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ 2 * n by linarith)
  norm_num at he
  linarith

/-- Actual finite-sample KL bound, with positive constants independent of n, H, and common scale.
This includes the small fixed Lipschitz constants needed at p=1. -/
theorem scaledHarmonizableGaussian_midpoint_klDiv_rate :
    ∃ c₀ > 0, ∃ b₀ > 0, ∃ C > 0, ∀ n : ℕ, 0 < n →
      ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ σ a B : ℝ,
      σ ≠ 0 → 0 ≤ a → 0 ≤ B →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) →
      (∀ i, i.val ≠ 0 → |(h i : ℝ) - h (previousGridIndex i)| ≤ B * midpointStep n i) →
      a * Real.log (2 * (n : ℝ)) ≤ c₀ → B ≤ b₀ →
      klDiv (scaledHarmonizableGaussian σ h (fun i => grid n i.val))
        (scaledHarmonizableGaussian σ (fun _ => brownianHurst) (fun i => grid n i.val)) ≤
        ENNReal.ofReal (C * ((n : ℝ) * a ^ 2 + B ^ 2) * Real.log (2 * (n : ℝ)) ^ 2) := by
  obtain ⟨C₀, hC₀, D, hD, hfloor⟩ := midpoint_whitened_gram_uniform_floor
  obtain ⟨F, hF, hfrob⟩ := midpoint_whitened_frobenius_rate
  let c₀ := min (1 / 8 : ℝ) (7 / (48 * (C₀ + 1)))
  let b₀ := min (1 : ℝ) (1 / (4 * (D + 1)))
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hb₀ : 0 < b₀ := by dsimp [b₀]; positivity
  refine ⟨c₀, hc₀, b₀, hb₀, 18 * F, by positivity, ?_⟩
  intro n hn h σ a B hσ ha hB hha hstep hsmall hBsmall
  have hL := midpoint_log_lower_bound n hn
  have hL0 : 0 ≤ Real.log (2 * (n : ℝ)) := by linarith
  have hL' : 1 + Real.log (2 * (n : ℝ)) ≤ 3 * Real.log (2 * (n : ℝ)) := by linarith
  have hc₁ : c₀ ≤ 1 / 8 := min_le_left _ _
  have hc₂ : c₀ * (48 * (C₀ + 1)) ≤ 7 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hb₁ : B ≤ 1 := hBsmall.trans (min_le_left _ _)
  have hb₂ : B * (4 * (D + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (hBsmall.trans (min_le_right _ _))
  have haquarter : a ≤ 1 / 4 := by
    have he := mul_le_mul_of_nonneg_left hL ha
    nlinarith
  have hh : ∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
    intro i
    have he := abs_le.mp (hha i)
    constructor <;> linarith [he.1, he.2]
  have hasmall : a * Real.log (2 * (n : ℝ)) ≤ 1 := hsmall.trans (hc₁.trans (by norm_num))
  have hCs : C₀ * a * (1 + Real.log (2 * (n : ℝ))) ≤ 7 / 16 := by
    have he := mul_le_mul_of_nonneg_left hL' ha
    have he' : a * (1 + Real.log (2 * (n : ℝ))) ≤ 3 * c₀ := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he' hC₀
    nlinarith
  have hDs : D * B ≤ 1 / 4 := by nlinarith
  obtain ⟨hpd, hev⟩ := hfloor n h a B hh ha hB hha hstep hasmall hCs hDs
  have hfr := hfrob n h a B hh ha hB hb₁ hha hstep hasmall
  have hKL := klDiv_multivariateGaussian_unit_frobenius_quarter _ hpd hev
  rw [scaledHarmonizableGaussian_midpoint_klDiv σ hσ n h]
  apply hKL.trans
  apply ENNReal.ofReal_le_ofReal
  have h1 := mul_le_mul_of_nonneg_left hfr (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := pow_le_pow_left₀ (show 0 ≤ 1 + Real.log (2 * (n : ℝ)) by linarith) hL' 2
  have hm := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ 2 * F * ((n : ℝ) * a ^ 2 + B ^ 2) by positivity)
  nlinarith

def midpointSampleHurst (H : ℝ → ℝ) (hH : MapsTo H (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1))
    (n : ℕ) (i : Fin n) : Ioo (0 : ℝ) 1 :=
  ⟨H (grid n i.val), hH (grid_mem n i.val (Nat.zero_lt_of_lt i.isLt) i.isLt)⟩

/-- The paper's derivative hypothesis implies the discrete condition used in the matrix proof. -/
theorem midpointSampleHurst_step_bound (H dH : ℝ → ℝ)
    (hH : MapsTo H (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1)) (B : ℝ)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt H (dH t) t)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, |dH t| ≤ B) (n : ℕ) (i : Fin n) (hi : i.val ≠ 0) :
    |(midpointSampleHurst H hH n i : ℝ) - midpointSampleHurst H hH n (previousGridIndex i)| ≤
      B * midpointStep n i := by
  have hn := Nat.zero_lt_of_lt i.isLt
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
    (fun t ht => show ‖dH t‖ ≤ B from by simpa only [Real.norm_eq_abs] using hbound t ht)
    (convex_Ioo (0 : ℝ) 1)
    (grid_mem n (previousGridIndex i).val hn (previousGridIndex i).isLt) (grid_mem n i.val hn i.isLt)
  have he : grid n i.val - grid n (previousGridIndex i).val = midpointStep n i := by
    rw [midpoint_grid_eq_left_add_step]
    simp only [midpointLeft, if_neg hi, add_sub_cancel_left]
  simpa only [Real.norm_eq_abs, he, abs_of_pos (midpointStep_pos n i), midpointSampleHurst] using hm

/-- Theorem 20.1 for the original continuous-parameter observation model under uniform derivative bounds. -/
theorem scaledHarmonizableGaussian_function_klDiv_rate :
    ∃ c₀ > 0, ∃ b₀ > 0, ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ H dH : ℝ → ℝ,
      ∀ hH : MapsTo H (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1), ∀ σ a B : ℝ,
      σ ≠ 0 → 0 ≤ a → 0 ≤ B →
      (∀ t ∈ Ioo (0 : ℝ) 1, |H t - 1 / 2| ≤ a) →
      (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt H (dH t) t) →
      (∀ t ∈ Ioo (0 : ℝ) 1, |dH t| ≤ B) →
      a * Real.log (2 * (n : ℝ)) ≤ c₀ → B ≤ b₀ →
      klDiv (scaledHarmonizableGaussian σ (midpointSampleHurst H hH n) (fun i => grid n i.val))
        (scaledHarmonizableGaussian σ (fun _ => brownianHurst) (fun i => grid n i.val)) ≤
        ENNReal.ofReal (C * ((n : ℝ) * a ^ 2 + B ^ 2) * Real.log (2 * (n : ℝ)) ^ 2) := by
  obtain ⟨c₀, hc₀, b₀, hb₀, C, hC, hc⟩ := scaledHarmonizableGaussian_midpoint_klDiv_rate
  refine ⟨c₀, hc₀, b₀, hb₀, C, hC, ?_⟩
  intro n hn H dH hH σ a B hσ ha hB hha hderiv hbound hsmall hBsmall
  apply hc n hn (midpointSampleHurst H hH n) σ a B hσ ha hB
  · intro i
    exact hha (grid n i.val) (grid_mem n i.val hn i.isLt)
  · exact fun i hi => midpointSampleHurst_step_bound H dH hH B hderiv hbound n i hi
  · exact hsmall
  · exact hBsmall

/-- Eventual uniform KL control needs no assumption that B log n tends to zero. -/
theorem scaledHarmonizableGaussian_midpoint_klDiv_eventually :
    ∃ C > 0, ∀ h : (n : ℕ) → Fin n → Ioo (0 : ℝ) 1, ∀ σ a B : ℕ → ℝ,
      (∀ n, σ n ≠ 0) → (∀ n, 0 ≤ a n) → (∀ n, 0 ≤ B n) →
      (∀ n i, |(h n i : ℝ) - 1 / 2| ≤ a n) →
      (∀ n i, i.val ≠ 0 → |(h n i : ℝ) - h n (previousGridIndex i)| ≤ B n * midpointStep n i) →
      Tendsto (fun n => a n * Real.log (2 * (n : ℝ))) atTop (𝓝 0) → Tendsto B atTop (𝓝 0) →
      ∀ᶠ n in atTop,
      klDiv (scaledHarmonizableGaussian (σ n) (h n) (fun i => grid n i.val))
        (scaledHarmonizableGaussian (σ n) (fun _ => brownianHurst) (fun i => grid n i.val)) ≤
        ENNReal.ofReal (C * ((n : ℝ) * (a n) ^ 2 + (B n) ^ 2) * Real.log (2 * (n : ℝ)) ^ 2) := by
  obtain ⟨c₀, hc₀, b₀, hb₀, C, hC, hc⟩ := scaledHarmonizableGaussian_midpoint_klDiv_rate
  refine ⟨C, hC, ?_⟩
  intro h σ a B hσ ha hB hha hstep halim hBlim
  have hea : ∀ᶠ n in atTop, a n * Real.log (2 * (n : ℝ)) < c₀ := halim.eventually (gt_mem_nhds hc₀)
  have heb : ∀ᶠ n in atTop, B n < b₀ := hBlim.eventually (gt_mem_nhds hb₀)
  filter_upwards [hea, heb, eventually_ge_atTop (1 : ℕ)] with n hnA hnB hn
  exact hc n (by omega) (h n) (σ n) (a n) (B n) (hσ n) (ha n) (hB n) (hha n) (hstep n) hnA.le hnB.le

theorem log_two_mul_le_twice_log (n : ℕ) (hn : 2 ≤ n) :
    Real.log (2 * (n : ℝ)) ≤ 2 * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  rw [Real.log_mul (by norm_num) hnR.ne']
  linarith

theorem kl_smallness_of_paper_condition (a B : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hB : ∀ n, 0 ≤ B n)
    (hlim : Tendsto (fun n => (a n + B n) * Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n => a n * Real.log (2 * (n : ℝ))) atTop (𝓝 0) ∧ Tendsto B atTop (𝓝 0) := by
  have hdom : ∀ᶠ n in atTop,
      0 ≤ a n * Real.log (2 * (n : ℝ)) ∧
      a n * Real.log (2 * (n : ℝ)) ≤ 2 * ((a n + B n) * Real.log n) ∧
      B n ≤ 2 * ((a n + B n) * Real.log n) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hlog2 := midpoint_log_lower_bound 1 (by omega)
    norm_num only [Nat.cast_one, mul_one] at hlog2
    have hlogn : (1 / 2 : ℝ) ≤ Real.log n := hlog2.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
    have hnlog := midpoint_log_lower_bound n (by omega)
    have hcmp := log_two_mul_le_twice_log n hn
    refine ⟨mul_nonneg (ha n) (by linarith), ?_, ?_⟩
    · have he := mul_le_mul_of_nonneg_left hcmp (ha n)
      have hb := mul_nonneg (hB n) (show 0 ≤ Real.log n by linarith)
      nlinarith
    · have he := mul_le_mul_of_nonneg_left hlogn (hB n)
      have hb := mul_nonneg (ha n) (show 0 ≤ Real.log n by linarith)
      nlinarith
  have hz : Tendsto (fun n => 2 * ((a n + B n) * Real.log n)) atTop (𝓝 0) := by
    simpa using hlim.const_mul 2
  exact ⟨squeeze_zero' (hdom.mono (fun n hn => hn.1)) (hdom.mono (fun n hn => hn.2.1)) hz,
    squeeze_zero' (Eventually.of_forall hB) (hdom.mono (fun n hn => hn.2.2)) hz⟩

/-- Proposition 8.1's original smallness condition now implies the actual log(n)^2 KL rate. -/
theorem scaledHarmonizableGaussian_klDiv_proposition_8_1 :
    ∃ C > 0, ∀ h : (n : ℕ) → Fin n → Ioo (0 : ℝ) 1, ∀ σ a B : ℕ → ℝ,
      (∀ n, σ n ≠ 0) → (∀ n, 0 ≤ a n) → (∀ n, 0 ≤ B n) →
      (∀ n i, |(h n i : ℝ) - 1 / 2| ≤ a n) →
      (∀ n i, i.val ≠ 0 → |(h n i : ℝ) - h n (previousGridIndex i)| ≤ B n * midpointStep n i) →
      Tendsto (fun n => (a n + B n) * Real.log n) atTop (𝓝 0) →
      ∀ᶠ n in atTop,
      klDiv (scaledHarmonizableGaussian (σ n) (h n) (fun i => grid n i.val))
        (scaledHarmonizableGaussian (σ n) (fun _ => brownianHurst) (fun i => grid n i.val)) ≤
        ENNReal.ofReal (C * ((n : ℝ) * (a n) ^ 2 + (B n) ^ 2) * Real.log n ^ 2) := by
  obtain ⟨C, hC, hc⟩ := scaledHarmonizableGaussian_midpoint_klDiv_eventually
  refine ⟨4 * C, by positivity, ?_⟩
  intro h σ a B hσ ha hB hha hstep hlim
  obtain ⟨halim, hBlim⟩ := kl_smallness_of_paper_condition a B ha hB hlim
  have he := hc h σ a B hσ ha hB hha hstep halim hBlim
  filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  have hl := log_two_mul_le_twice_log n hn2
  have hL0 : 0 ≤ Real.log (2 * (n : ℝ)) := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
    (midpoint_log_lower_bound n (by omega))
  have hp := pow_le_pow_left₀ hL0 hl 2
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ C * ((n : ℝ) * (a n) ^ 2 + (B n) ^ 2) by positivity)
  exact hm.trans_eq (by ring)

theorem kl_limsup_bound_of_eventually (d : ℕ → ℝ≥0∞) (s : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ n, 0 ≤ s n) (hd : ∀ᶠ n in atTop, d n ≤ ENNReal.ofReal (C * s n)) :
    Filter.limsup (fun n => (d n).toReal / s n) atTop ≤ C := by
  apply Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop
    (fun n => div_nonneg ENNReal.toReal_nonneg (hs n)))
  filter_upwards [hd] with n hn
  by_cases hz : s n = 0
  · simpa only [hz, div_zero] using hC
  · have hp : 0 < s n := lt_of_le_of_ne (hs n) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (hs n)) hn

/-- The original Proposition 8.1 limsup statement for actual midpoint observations.
The Hurst functions and their derivatives may vary with n. -/
theorem proposition_8_1_function_limsup :
    ∃ C > 0, ∀ H dH : ℕ → ℝ → ℝ,
      ∀ hH : ∀ n, MapsTo (H n) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1), ∀ σ a B : ℕ → ℝ,
      (∀ n, σ n ≠ 0) → (∀ n, 0 ≤ a n) → (∀ n, 0 ≤ B n) →
      (∀ n t, t ∈ Ioo (0 : ℝ) 1 → |H n t - 1 / 2| ≤ a n) →
      (∀ n t, t ∈ Ioo (0 : ℝ) 1 → HasDerivAt (H n) (dH n t) t) →
      (∀ n t, t ∈ Ioo (0 : ℝ) 1 → |dH n t| ≤ B n) →
      Tendsto (fun n => (a n + B n) * Real.log n) atTop (𝓝 0) →
      Filter.limsup (fun n =>
        (klDiv (scaledHarmonizableGaussian (σ n) (midpointSampleHurst (H n) (hH n) n) (fun i => grid n i.val))
          (scaledHarmonizableGaussian (σ n) (fun _ => brownianHurst) (fun i => grid n i.val))).toReal /
          (((n : ℝ) * (a n) ^ 2 + (B n) ^ 2) * Real.log n ^ 2)) atTop ≤ C := by
  obtain ⟨C, hC, hc⟩ := scaledHarmonizableGaussian_klDiv_proposition_8_1
  refine ⟨C, hC, ?_⟩
  intro H dH hH σ a B hσ ha hB hha hderiv hbound hlim
  let h := fun n => midpointSampleHurst (H n) (hH n) n
  have he := hc h σ a B hσ ha hB
    (fun n i => hha n (grid n i.val) (grid_mem n i.val (Nat.zero_lt_of_lt i.isLt) i.isLt))
    (fun n i hi => midpointSampleHurst_step_bound (H n) (dH n) (hH n) (B n)
      (hderiv n) (hbound n) n i hi) hlim
  apply kl_limsup_bound_of_eventually _ _ C hC.le (fun n => by positivity)
  simpa only [mul_assoc, h] using he

end Hurst
