import Hurst.VaryingIncrement
import Hurst.HolderRegularity

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators ENNReal Topology
namespace Hurst

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def observationDifferenceWeights (i j : ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun k => (if k = j then 1 else 0) - (if k = i then 1 else 0))

theorem observationDifferenceWeights_inner (i j : ι) (x : EuclideanSpace ℝ ι) :
    ⟪observationDifferenceWeights i j, x⟫ = x j - x i := by
  simp [observationDifferenceWeights, PiLp.inner_apply, mul_sub, Finset.sum_sub_distrib]

theorem observationDifferenceWeights_feature (v : ι → E) (i j : ι) :
    (∑ k, observationDifferenceWeights i j k • v k) = v j - v i := by
  simp [observationDifferenceWeights, sub_smul, Finset.sum_sub_distrib]

theorem featureGaussian_difference_log_mean (v : ι → E) (i j : ι) (hv : v j - v i ≠ 0) :
    (∫ x, Real.log ((x j - x i) ^ 2) ∂featureGaussian v) =
      Real.log (‖v j - v i‖ ^ 2) + gaussianLogSquareMean := by
  have hfeat : ∑ k, observationDifferenceWeights i j k • v k ≠ 0 := by
    simpa only [observationDifferenceWeights_feature] using hv
  simpa only [observationDifferenceWeights_inner, observationDifferenceWeights_feature] using
    featureGaussian_expected_log_square v (observationDifferenceWeights i j) hfeat

theorem featureGaussian_difference_log_moments (v : ι → E) (i j : ι) (hv : v j - v i ≠ 0) (r : ℕ) :
    Integrable (fun x => (Real.log ((x j - x i) ^ 2)) ^ r) (featureGaussian v) := by
  have hfeat : ∑ k, observationDifferenceWeights i j k • v k ≠ 0 := by
    simpa only [observationDifferenceWeights_feature] using hv
  simpa only [observationDifferenceWeights_inner] using
    featureGaussian_integrable_log_square_pow v (observationDifferenceWeights i j) hfeat r

theorem harmonizableGaussian_difference_log_mean_eq_pair
    (H : ι → Ioo (0 : ℝ) 1) (T : ι → ℝ) (i j : ι) (ℓ : ℝ)
    (hT : T j = T i + ℓ)
    (hv : harmonizableFeature (H j) (T j) - harmonizableFeature (H i) (T i) ≠ 0) :
    (∫ x, Real.log ((x j - x i) ^ 2) ∂harmonizableGaussian H T) =
      ∫ x, Real.log ((x 1 - x 0) ^ 2) ∂varyingPair (H i) (H j) (T i) ℓ := by
  rw [harmonizableGaussian, featureGaussian_difference_log_mean _ i j hv]
  have hpair : varyingPairFeatures (H i) (H j) (T i) ℓ 1 - varyingPairFeatures (H i) (H j) (T i) ℓ 0 ≠ 0 := by
    simpa only [varyingPairFeatures, Matrix.cons_val_zero, Matrix.cons_val_one, hT] using hv
  rw [varyingPair, featureGaussian_difference_log_mean _ 0 1 hpair]
  simp only [varyingPairFeatures, Matrix.cons_val_zero, Matrix.cons_val_one, hT]

/-- The two-point bound applies to increments of the full joint observation law. -/
theorem harmonizableGaussian_difference_log_mean_bound (a b : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ H : ι → Ioo (0 : ℝ) 1, ∀ T : ι → ℝ, ∀ i j : ι,
      (H i : ℝ) ∈ Icc a b → (H j : ℝ) ∈ Icc a b → ∀ ℓ B : ℝ,
      T j = T i + ℓ → |T j| ≤ 1 → 0 < ℓ → ℓ ≤ 1 → 0 ≤ B → |(H j : ℝ) - H i| ≤ B * ℓ →
      C * B * ℓ ^ (1 - b) ≤ 1 / 2 →
      |(∫ x, Real.log ((x j - x i) ^ 2) ∂harmonizableGaussian H T) -
        (2 * (H i : ℝ) * Real.log ℓ + gaussianLogSquareMean)| ≤ 10 * C * B * ℓ ^ (1 - b) := by
  obtain ⟨C, hC, hrem⟩ := normalizedVaryingIncrement_uniform_remainder a b ha hb hab
  refine ⟨C, hC, ?_⟩
  intro H T i j hi hj ℓ B hT ht hℓ hℓ1 hB hH hsmall
  have hs : |T i + ℓ| ≤ 1 := by rwa [← hT]
  have hr := hrem (H i) (H j) hi hj (T i) ℓ B hs hℓ hℓ1 hB hH
  have hlow := norm_square_lower_from_unit _ _ _ (normalizedFrozenIncrement_norm (H i) (T i) ℓ hℓ) hr hsmall
  have hv : normalizedVaryingIncrement (H i) (H j) (T i) ℓ ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hlow
    norm_num at hlow
  have hdiff : harmonizableFeature (H j) (T j) - harmonizableFeature (H i) (T i) ≠ 0 := by
    rw [hT, varyingIncrement_normalized_identity _ _ _ _ hℓ]
    exact smul_ne_zero (Real.rpow_pos_of_pos hℓ _).ne' hv
  rw [harmonizableGaussian_difference_log_mean_eq_pair H T i j ℓ hT hdiff]
  simpa only [mul_assoc] using varyingPair_log_mean_from_remainder (H i) (H j) (T i) ℓ
    (C * B * ℓ ^ (1 - b)) hℓ (by positivity) hsmall hr

def firstDiffLeft (n : ℕ) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩

def firstDiffRight (n : ℕ) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

theorem grid_firstDifference_step (n : ℕ) (i : Fin (n - 1)) :
    grid n (firstDiffRight n i).val = grid n (firstDiffLeft n i).val + 1 / (n : ℝ) := by
  simp only [grid, firstDiffRight, firstDiffLeft, Nat.cast_add, Nat.cast_one]
  ring

/-- Uniform log-mean error on every valid first difference, from the original Holder class. -/
theorem hurstHolder_grid_firstDifference_log_mean (p a b : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) →
      ∀ n : ℕ, 0 < n → C * (1 + M) * (n : ℝ) ^ (b - 1) ≤ 1 / 2 →
      ∀ i : Fin (n - 1),
      |(∫ x, Real.log ((x (firstDiffRight n i) - x (firstDiffLeft n i)) ^ 2)
          ∂harmonizableGaussian (midpointSampleHurst f hf.1 n) (fun j => grid n j.val)) -
        (-2 * f (grid n i.val) * Real.log n + gaussianLogSquareMean)| ≤
          10 * C * (1 + M) * (n : ℝ) ^ (b - 1) := by
  obtain ⟨D, hD, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  obtain ⟨K', hK', hrem⟩ := normalizedVaryingIncrement_uniform_remainder a b ha hb hab
  let C := K' * D
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M hM f hf hF n hn hsmall i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let H := midpointSampleHurst f hf.1 n
  let T : Fin n → ℝ := fun j => grid n j.val
  let l := firstDiffLeft n i
  let r := firstDiffRight n i
  have hl := grid_mem n l.val hn l.isLt
  have hr := grid_mem n r.val hn r.isLt
  have hstep : T r = T l + 1 / (n : ℝ) := grid_firstDifference_step n i
  have hdist : |T r - T l| = 1 / (n : ℝ) := by rw [hstep, add_sub_cancel_left, abs_of_pos (by positivity)]
  have hparam : |(H r : ℝ) - H l| ≤ (D * (1 + M)) * (1 / (n : ℝ)) := by
    have h := hLip M hM f hf 0 (by have := hurstHolder_floor_pos p hp; omega) (T l) hl (T r) hr
    simpa only [iteratedDeriv_zero, hdist, H, T, midpointSampleHurst] using h
  have hpow : (1 / (n : ℝ)) ^ (1 - b) = (n : ℝ) ^ (b - 1) := by
    rw [one_div, Real.inv_rpow hnR.le, ← Real.rpow_neg hnR.le]
    congr 1
    ring
  have hts : |T l + 1 / (n : ℝ)| ≤ 1 := by
    rw [← hstep, abs_of_pos hr.1]
    exact hr.2.le
  have hrem1 := hrem (H l) (H r) (hF _ hl) (hF _ hr) (T l) (1 / (n : ℝ)) (D * (1 + M))
    hts (by positivity) ((div_le_one hnR).mpr hn1) (by positivity) hparam
  have hsmall' : K' * (D * (1 + M)) * (1 / (n : ℝ)) ^ (1 - b) ≤ 1 / 2 := by
    rw [hpow]
    simpa only [C, mul_assoc] using hsmall
  have hlow := norm_square_lower_from_unit _ _ _
    (normalizedFrozenIncrement_norm (H l) (T l) (1 / (n : ℝ)) (by positivity)) hrem1 hsmall'
  have hv : normalizedVaryingIncrement (H l) (H r) (T l) (1 / (n : ℝ)) ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hlow
    norm_num at hlow
  have hdiff : harmonizableFeature (H r) (T r) - harmonizableFeature (H l) (T l) ≠ 0 := by
    rw [hstep, varyingIncrement_normalized_identity _ _ _ _ (by positivity)]
    exact smul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' hv
  have hm := varyingPair_log_mean_from_remainder (H l) (H r) (T l) (1 / (n : ℝ))
    (K' * (D * (1 + M)) * (1 / (n : ℝ)) ^ (1 - b)) (by positivity) (by positivity) hsmall' hrem1
  rw [← harmonizableGaussian_difference_log_mean_eq_pair H T l r _ hstep hdiff, hpow,
    Real.log_div one_ne_zero hnR.ne', Real.log_one, zero_sub] at hm
  convert hm using 1 <;> simp only [H, T, l, r, midpointSampleHurst, firstDiffLeft, C] <;> ring_nf

theorem hurstHolder_grid_firstDifference_log_mean_eventually (p a b : ℝ) (hp : 1 ≤ p)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
      ∀ f : ℝ → ℝ, ∀ hf : f ∈ hurstHolderClass p M,
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ Icc a b) → ∀ i : Fin (n - 1),
      |(∫ x, Real.log ((x (firstDiffRight n i) - x (firstDiffLeft n i)) ^ 2)
          ∂harmonizableGaussian (midpointSampleHurst f hf.1 n) (fun j => grid n j.val)) -
        (-2 * f (grid n i.val) * Real.log n + gaussianLogSquareMean)| ≤
          10 * C * (1 + M) * (n : ℝ) ^ (b - 1) := by
  obtain ⟨C, hC, hmean⟩ := hurstHolder_grid_firstDifference_log_mean p a b hp ha hb hab
  refine ⟨C, hC, ?_⟩
  intro M hM
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - 1)) atTop (𝓝 0) := by
    convert! (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - b)).comp tendsto_natCast_atTop_atTop using 1
    congr 1
    funext n
    congr 1
    ring
  have ht' : Tendsto (fun n : ℕ => C * (1 + M) * (n : ℝ) ^ (b - 1)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (C * (1 + M))
  filter_upwards [ht'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (0 : ℕ)] with n hsmall hn
  intro f hf hF i
  exact hmean M hM f hf hF n hn hsmall.le i

end Hurst
