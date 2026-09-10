import Hurst.MixedPower
import Hurst.CovarianceParameter

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

theorem nonnegative_base_power_parameter_hasDerivAt (x h k : ℝ) (hx : 0 ≤ x) (hp : 0 < h + k) :
    HasDerivAt (fun v => x ^ (h + v)) (x ^ (h + k) * Real.log x) k := by
  rcases eq_or_lt_of_le hx with he | hx
  · subst x
    have hv : ∀ᶠ v in 𝓝 k, 0 < h + v :=
      (continuous_const.add continuous_id).continuousAt.eventually (lt_mem_nhds hp)
    have he : (fun v : ℝ => (0 : ℝ) ^ (h + v)) =ᶠ[𝓝 k] (fun _ => 0) := by
      filter_upwards [hv] with v hv
      exact Real.zero_rpow hv.ne'
    simpa only [Real.log_zero, mul_zero] using (hasDerivAt_const k (0 : ℝ)).congr_of_eventuallyEq he
  · have hd := ((hasDerivAt_id k).const_add h).const_rpow hx
    convert! hd using 1
    simp only [id_eq, mul_one]
    ring

def kernelIncrement (h k u v t : ℝ) : ℝ :=
  harmonizableCovCoeff h k *
    (u ^ (h + k) - v ^ (h + k) - (|u - t| ^ (h + k) - |v - t| ^ (h + k)))

def kernelIncrementSlope (h k u v t : ℝ) : ℝ :=
  harmonizableCovCoeffSlope h k *
    (u ^ (h + k) - v ^ (h + k) - (|u - t| ^ (h + k) - |v - t| ^ (h + k))) +
  harmonizableCovCoeff h k *
    (u ^ (h + k) * Real.log u - v ^ (h + k) * Real.log v -
      (|u - t| ^ (h + k) * Real.log |u - t| - |v - t| ^ (h + k) * Real.log |v - t|))

theorem harmonizableFeature_increment_cross_inner (h k : Ioo (0 : ℝ) 1) (u v t : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ⟪harmonizableFeature h u - harmonizableFeature h v, harmonizableFeature k t⟫ =
      kernelIncrement h k u v t := by
  simp only [inner_sub_left, harmonizableFeature_inner_formula, abs_of_nonneg hu,
    abs_of_nonneg hv, kernelIncrement, harmonizableCovCoeff]
  ring

theorem kernelIncrement_hasDerivAt (h k u v t : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1)
    (hk : k ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    HasDerivAt (fun z => kernelIncrement h z u v t) (kernelIncrementSlope h k u v t) k := by
  have hp : 0 < h + k := by linarith [hh.1, hk.1]
  have hdu := nonnegative_base_power_parameter_hasDerivAt u h k hu hp
  have hdv := nonnegative_base_power_parameter_hasDerivAt v h k hv hp
  have hdut := nonnegative_base_power_parameter_hasDerivAt |u - t| h k (abs_nonneg _) hp
  have hdvt := nonnegative_base_power_parameter_hasDerivAt |v - t| h k (abs_nonneg _) hp
  convert! (harmonizableCovCoeff_hasDerivAt h k hh hk).mul ((hdu.sub hdv).sub (hdut.sub hdvt)) using 1

/-- Both distances stay in the unit interval, and the distance map is 1-Lipschitz. -/
theorem unit_distance_pair (u v t : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |u - t| ∈ Icc (0 : ℝ) 1 ∧ |v - t| ∈ Icc (0 : ℝ) 1 ∧
      |(|u - t|) - (|v - t|)| ≤ |u - v| := by
  refine ⟨⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hu.1, ht.2], by linarith [hu.2, ht.1]⟩⟩,
    ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hv.1, ht.2], by linarith [hv.2, ht.1]⟩⟩, ?_⟩
  simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (u - t) (v - t)

/-- Uniform mixed time/parameter control retains the actual time step. -/
theorem kernelIncrementSlope_mesh_bound (n : ℕ) (hn : 0 < n) (h k a u v t τ C : ℝ)
    (hh : h ∈ Icc (1 / 4 : ℝ) (3 / 4)) (hk : k ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (ha : 0 ≤ a) (hha : |h - 1 / 2| ≤ a) (hka : |k - 1 / 2| ≤ a)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hum : halfMeshPoint n u) (hvm : halfMeshPoint n v) (htm : halfMeshPoint n t)
    (hτ : 0 ≤ τ) (huv : |u - v| ≤ τ) (hC : 0 ≤ C)
    (hcoef : |harmonizableCovCoeff h k| ≤ C) (hcoef' : |harmonizableCovCoeffSlope h k| ≤ C)
    (hsmall : a * Real.log (2 * (n : ℝ)) ≤ 1) :
    |kernelIncrementSlope h k u v t| ≤ (6 * C * Real.exp 2) * (1 + Real.log (2 * (n : ℝ))) * τ := by
  have hp0 : 0 < h + k := by linarith [hh.1, hk.1]
  have hp2 : h + k ≤ 2 := by linarith [hh.2, hk.2]
  have hp := hurst_sum_deviation h k a hha hka
  have hpair := mesh_power_pair_bounds n hn (h + k) a u v ha hp0 hp2 hp hu hv
    (halfMeshPoint_separated n hn u hum) (halfMeshPoint_separated n hn v hvm) hsmall
  obtain ⟨hut, hvt, hdist⟩ := unit_distance_pair u v t hu hv ht
  have hpair' := mesh_power_pair_bounds n hn (h + k) a |u - t| |v - t| ha hp0 hp2 hp hut hvt
    (halfMeshPoint_separated n hn _ (halfMeshPoint_abs_sub n u t hum htm))
    (halfMeshPoint_separated n hn _ (halfMeshPoint_abs_sub n v t hvm htm)) hsmall
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
  have he0 : 0 ≤ 2 * Real.exp 2 := by positivity
  have he1 : 0 ≤ Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ))) := by positivity
  have hb1 := hpair.1.trans (mul_le_mul_of_nonneg_left huv he0)
  have hb2 := hpair'.1.trans (mul_le_mul_of_nonneg_left (hdist.trans huv) he0)
  have hb3 := hpair.2.trans (mul_le_mul_of_nonneg_left huv he1)
  have hb4 := hpair'.2.trans (mul_le_mul_of_nonneg_left (hdist.trans huv) he1)
  have hbracket : |u ^ (h + k) - v ^ (h + k) - (|u - t| ^ (h + k) - |v - t| ^ (h + k))| ≤
      4 * Real.exp 2 * τ := by
    have he := abs_sub (u ^ (h + k) - v ^ (h + k)) (|u - t| ^ (h + k) - |v - t| ^ (h + k))
    linarith
  have hlogbracket : |u ^ (h + k) * Real.log u - v ^ (h + k) * Real.log v -
      (|u - t| ^ (h + k) * Real.log |u - t| - |v - t| ^ (h + k) * Real.log |v - t|)| ≤
      2 * Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ))) * τ := by
    have he := abs_sub (u ^ (h + k) * Real.log u - v ^ (h + k) * Real.log v)
      (|u - t| ^ (h + k) * Real.log |u - t| - |v - t| ^ (h + k) * Real.log |v - t|)
    linarith
  have hm1 := mul_le_mul hcoef' hbracket (abs_nonneg _) hC
  have hm2 := mul_le_mul hcoef hlogbracket (abs_nonneg _) hC
  unfold kernelIncrementSlope
  calc
    _ ≤ _ := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ C * (4 * Real.exp 2 * τ) + C * (2 * Real.exp 2 * (1 + 2 * Real.log (2 * (n : ℝ))) * τ) := add_le_add hm1 hm2
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC (Real.exp_pos 2).le) hL) hτ]

/-- A single constant controls the mixed kernel for all meshes and parameter pairs in the compact range. -/
theorem kernelIncrement_mesh_parameter_bound :
    ∃ K ≥ 0, ∀ n : ℕ, 0 < n → ∀ h k l a u v t τ : ℝ,
      h ∈ Icc (1 / 4 : ℝ) (3 / 4) → k ∈ Icc (1 / 4 : ℝ) (3 / 4) →
      l ∈ Icc (1 / 4 : ℝ) (3 / 4) → 0 ≤ a →
      |h - 1 / 2| ≤ a → |k - 1 / 2| ≤ a → |l - 1 / 2| ≤ a →
      u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n u → halfMeshPoint n v → halfMeshPoint n t →
      0 ≤ τ → |u - v| ≤ τ → a * Real.log (2 * (n : ℝ)) ≤ 1 →
      |kernelIncrement h k u v t - kernelIncrement h l u v t| ≤
        K * (1 + Real.log (2 * (n : ℝ))) * τ * |k - l| := by
  obtain ⟨C, hC, hc⟩ := harmonizableCovCoeff_uniform_derivative_control (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨6 * C * Real.exp 2, by positivity, ?_⟩
  intro n hn h k l a u v t τ hh hk hl ha hha hka hla hu hv ht hum hvm htm hτ huv hsmall
  let S := Icc (1 / 4 : ℝ) (3 / 4) ∩ Icc (1 / 2 - a) (1 / 2 + a)
  have hh0 : h ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hS : ∀ z ∈ S, z ∈ Ioo (0 : ℝ) 1 ∧ |z - 1 / 2| ≤ a := by
    intro z hz
    refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, abs_le.mpr ?_⟩
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hkS : k ∈ S := by
    refine ⟨hk, ?_⟩
    have he := abs_le.mp hka
    constructor <;> linarith [he.1, he.2]
  have hlS : l ∈ S := by
    refine ⟨hl, ?_⟩
    have he := abs_le.mp hla
    constructor <;> linarith [he.1, he.2]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (kernelIncrement_hasDerivAt h z u v t hh0 (hS z hz).1 hu.1 hv.1).hasDerivWithinAt)
    (fun z hz => show ‖kernelIncrementSlope h z u v t‖ ≤
        (6 * C * Real.exp 2) * (1 + Real.log (2 * (n : ℝ))) * τ from by
      rw [Real.norm_eq_abs]
      exact kernelIncrementSlope_mesh_bound n hn h z a u v t τ C hh hz.1 ha hha (hS z hz).2
        hu hv ht hum hvm htm hτ huv hC (hc h z hh hz.1).1 (hc h z hh hz.1).2 hsmall)
    ((convex_Icc (1 / 4 : ℝ) (3 / 4)).inter (convex_Icc (1 / 2 - a) (1 / 2 + a))) hlS hkS
  simpa only [Real.norm_eq_abs] using hm

theorem frozen_variation_cross_inner (h k l : Ioo (0 : ℝ) 1) (u v t ℓ m : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hstep : u = v + ℓ) :
    ⟪frozenIncrementFeature h v ℓ, hurstVariationFeature k l t m⟫ =
      ((Real.sqrt ℓ)⁻¹ * (Real.sqrt m)⁻¹) *
        (kernelIncrement h k u v t - kernelIncrement h l u v t) := by
  rw [frozenIncrementFeature, hurstVariationFeature, ← hstep,
    real_inner_smul_left, real_inner_smul_right, inner_sub_right,
    harmonizableFeature_increment_cross_inner h k u v t hu hv,
    harmonizableFeature_increment_cross_inner h l u v t hu hv]
  ring

theorem midpoint_inverse_sqrt_product_bound (n : ℕ) (i j : Fin n) :
    (Real.sqrt (midpointStep n i))⁻¹ * (Real.sqrt (midpointStep n j))⁻¹ ≤ 2 * (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hp : 1 / (2 * (n : ℝ)) ≤ Real.sqrt (midpointStep n i) * Real.sqrt (midpointStep n j) := by
    calc
      _ = Real.sqrt (1 / (2 * (n : ℝ))) * Real.sqrt (1 / (2 * (n : ℝ))) := by
        rw [← sq, Real.sq_sqrt (by positivity)]
      _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt (midpointStep_ge_half n i))
        (Real.sqrt_le_sqrt (midpointStep_ge_half n j)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← mul_inv_rev]
  have he := one_div_le_one_div_of_le (by positivity : 0 < 1 / (2 * (n : ℝ))) hp
  simpa only [one_div, inv_inv, mul_comm] using he

/-- The actual mixed matrix has the needed 1/n entry bound; no independence premise is used. -/
theorem midpoint_mixed_uniform_bound :
    ∃ K ≥ 0, ∀ n : ℕ, ∀ h : Fin n → Ioo (0 : ℝ) 1, ∀ a B : ℝ,
      (∀ i, (h i : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4)) → 0 ≤ a → 0 ≤ B →
      (∀ i, |(h i : ℝ) - 1 / 2| ≤ a) →
      (∀ i, i.val ≠ 0 → |(h i : ℝ) - h (previousGridIndex i)| ≤ B * midpointStep n i) →
      a * Real.log (2 * (n : ℝ)) ≤ 1 → ∀ i j,
      |⟪frozenIncrementFeature (h i) (midpointLeft n i) (midpointStep n i),
        hurstVariationFeature (h j) (previousGridHurst h j) (midpointLeft n j) (midpointStep n j)⟫| ≤
        K * B * (1 + Real.log (2 * (n : ℝ))) / n := by
  obtain ⟨K, hK, hk⟩ := kernelIncrement_mesh_parameter_bound
  refine ⟨2 * K, by positivity, ?_⟩
  intro n h a B hh ha hB hha hstep hsmall i j
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
  have hprev : (previousGridHurst h j : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
      |(previousGridHurst h j : ℝ) - 1 / 2| ≤ a := by
    unfold previousGridHurst
    split_ifs <;> exact ⟨hh _, hha _⟩
  have hdiff : |(h j : ℝ) - previousGridHurst h j| ≤ B / n := by
    by_cases hj : j.val = 0
    · simp only [previousGridHurst, if_pos hj, sub_self, abs_zero]
      positivity
    · simp only [previousGridHurst, if_neg hj]
      exact (hstep j hj).trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (midpointStep_le n j) hB)
  have hright := grid_mem n i.val hn i.isLt
  have hleft := midpointLeft_bounds n i
  have hjleft := midpointLeft_bounds n j
  have hdist : |grid n i.val - midpointLeft n i| ≤ 1 / (n : ℝ) := by
    rw [midpoint_grid_eq_left_add_step, add_sub_cancel_left,
      abs_of_pos (midpointStep_pos n i)]
    exact midpointStep_le n i
  have hkernel := hk n hn (h i) (h j) (previousGridHurst h j) a (grid n i.val)
    (midpointLeft n i) (midpointLeft n j) (1 / n) (hh i) (hh j) hprev.1 ha (hha i) (hha j) hprev.2
    ⟨hright.1.le, hright.2.le⟩ ⟨hleft.1, hleft.2.le⟩ ⟨hjleft.1, hjleft.2.le⟩
    (halfMeshPoint_grid n i.val) (halfMeshPoint_midpointLeft n i) (halfMeshPoint_midpointLeft n j)
    (by positivity) hdist hsmall
  have hk' := hkernel.trans (mul_le_mul_of_nonneg_left hdiff
    (show 0 ≤ K * (1 + Real.log (2 * (n : ℝ))) * (1 / n) by positivity))
  rw [frozen_variation_cross_inner (h i) (h j) (previousGridHurst h j)
    (grid n i.val) (midpointLeft n i) (midpointLeft n j) (midpointStep n i) (midpointStep n j)
    hright.1.le hleft.1 (midpoint_grid_eq_left_add_step n i), abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (midpointStep n i))⁻¹ * (Real.sqrt (midpointStep n j))⁻¹)]
  have hm := mul_le_mul (midpoint_inverse_sqrt_product_bound n i j) hk' (abs_nonneg _) (by positivity)
  exact hm.trans_eq (by field_simp)

end Hurst
