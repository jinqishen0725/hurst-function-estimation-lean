import Hurst.MeshPowerGeneral
import Hurst.MixedKernel

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

/-- Uniform mixed time/parameter control retains the actual time step. -/
theorem kernelIncrementSlope_mesh_bound_general (n : ℕ) (hn : 0 < n) (h k u v t τ C : ℝ)
    (hh : h ∈ Ioo (0 : ℝ) 1) (hk : k ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hum : halfMeshPoint n u) (hvm : halfMeshPoint n v) (htm : halfMeshPoint n t)
    (hτ : 0 ≤ τ) (huv : |u - v| ≤ τ) (hC : 0 ≤ C)
    (hcoef : |harmonizableCovCoeff h k| ≤ C) (hcoef' : |harmonizableCovCoeffSlope h k| ≤ C)
    :
    |kernelIncrementSlope h k u v t| ≤ (6 * C * meshPowerEnvelope n (h + k)) * (1 + Real.log (2 * (n : ℝ))) * τ := by
  have hE := meshPowerEnvelope_nonneg n (h + k)
  have hp0 : 0 < h + k := by linarith [hh.1, hk.1]
  have hp2 : h + k ≤ 2 := by linarith [hh.2, hk.2]
  have hpair := mesh_power_pair_bounds_general n hn (h + k) u v hp0 hp2 hu hv
    (halfMeshPoint_separated n hn u hum) (halfMeshPoint_separated n hn v hvm)
  obtain ⟨hut, hvt, hdist⟩ := unit_distance_pair u v t hu hv ht
  have hpair' := mesh_power_pair_bounds_general n hn (h + k) |u - t| |v - t| hp0 hp2 hut hvt
    (halfMeshPoint_separated n hn _ (halfMeshPoint_abs_sub n u t hum htm))
    (halfMeshPoint_separated n hn _ (halfMeshPoint_abs_sub n v t hvm htm))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
  have he0 : 0 ≤ 2 * meshPowerEnvelope n (h + k) := by positivity
  have he1 : 0 ≤ meshPowerEnvelope n (h + k) * (1 + 2 * Real.log (2 * (n : ℝ))) := by positivity
  have hb1 := hpair.1.trans (mul_le_mul_of_nonneg_left huv he0)
  have hb2 := hpair'.1.trans (mul_le_mul_of_nonneg_left (hdist.trans huv) he0)
  have hb3 := hpair.2.trans (mul_le_mul_of_nonneg_left huv he1)
  have hb4 := hpair'.2.trans (mul_le_mul_of_nonneg_left (hdist.trans huv) he1)
  have hbracket : |u ^ (h + k) - v ^ (h + k) - (|u - t| ^ (h + k) - |v - t| ^ (h + k))| ≤
      4 * meshPowerEnvelope n (h + k) * τ := by
    have he := abs_sub (u ^ (h + k) - v ^ (h + k)) (|u - t| ^ (h + k) - |v - t| ^ (h + k))
    linarith
  have hlogbracket : |u ^ (h + k) * Real.log u - v ^ (h + k) * Real.log v -
      (|u - t| ^ (h + k) * Real.log |u - t| - |v - t| ^ (h + k) * Real.log |v - t|)| ≤
      2 * meshPowerEnvelope n (h + k) * (1 + 2 * Real.log (2 * (n : ℝ))) * τ := by
    have he := abs_sub (u ^ (h + k) * Real.log u - v ^ (h + k) * Real.log v)
      (|u - t| ^ (h + k) * Real.log |u - t| - |v - t| ^ (h + k) * Real.log |v - t|)
    linarith
  have hm1 := mul_le_mul hcoef' hbracket (abs_nonneg _) hC
  have hm2 := mul_le_mul hcoef hlogbracket (abs_nonneg _) hC
  unfold kernelIncrementSlope
  calc
    _ ≤ _ := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ C * (4 * meshPowerEnvelope n (h + k) * τ) + C * (2 * meshPowerEnvelope n (h + k) * (1 + 2 * Real.log (2 * (n : ℝ))) * τ) := add_le_add hm1 hm2
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC hE) hL) hτ]


theorem meshPowerEnvelope_antitone (n : ℕ) (hn : 0 < n) {p q : ℝ} (hpq : p ≤ q) :
    meshPowerEnvelope n q ≤ meshPowerEnvelope n p := by
  unfold meshPowerEnvelope
  apply add_le_add_right
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- The exponent-dependent mesh factor is retained throughout the parameter segment. -/
theorem kernelIncrement_mesh_parameter_bound_general (lo hi : ℝ)
    (hlo : 0 < lo) (hhi : hi < 1) (hlh : lo ≤ hi) :
    ∃ K ≥ 0, ∀ n : ℕ, 0 < n → ∀ h k l u v t τ : ℝ,
      h ∈ Icc lo hi → k ∈ Icc lo hi → l ∈ Icc lo hi →
      u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n u → halfMeshPoint n v → halfMeshPoint n t →
      0 ≤ τ → |u - v| ≤ τ →
      |kernelIncrement h k u v t - kernelIncrement h l u v t| ≤
        K * meshPowerEnvelope n (h + min k l) * (1 + Real.log (2 * (n : ℝ))) * τ * |k - l| := by
  obtain ⟨C, hC, hc⟩ := harmonizableCovCoeff_uniform_derivative_control lo hi hlo hhi hlh
  refine ⟨6 * C, by positivity, ?_⟩
  intro n hn h k l u v t τ hh hk hl hu hv ht hum hvm htm hτ huv
  have hh0 : h ∈ Ioo (0 : ℝ) 1 := ⟨hlo.trans_le hh.1, hh.2.trans_lt hhi⟩
  have hsub : uIcc l k ⊆ Icc lo hi := uIcc_subset_Icc hl hk
  have hz0 : ∀ z ∈ uIcc l k, z ∈ Ioo (0 : ℝ) 1 := fun z hz =>
    ⟨hlo.trans_le (hsub hz).1, (hsub hz).2.trans_lt hhi⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    linarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (kernelIncrement_hasDerivAt h z u v t hh0 (hz0 z hz) hu.1 hv.1).hasDerivWithinAt)
    (fun z hz => show ‖kernelIncrementSlope h z u v t‖ ≤
        (6 * C * meshPowerEnvelope n (h + min k l)) * (1 + Real.log (2 * (n : ℝ))) * τ from by
      rw [Real.norm_eq_abs]
      apply (kernelIncrementSlope_mesh_bound_general n hn h z u v t τ C hh0 (hz0 z hz)
        hu hv ht hum hvm htm hτ huv hC (hc h z hh (hsub hz)).1 (hc h z hh (hsub hz)).2).trans
      apply mul_le_mul_of_nonneg_right _ hτ
      apply mul_le_mul_of_nonneg_right _ hL
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply meshPowerEnvelope_antitone n hn
      have hz' : min k l ≤ z := by simpa only [uIcc, min_comm] using hz.1
      linarith)
    (convex_uIcc l k) (left_mem_uIcc) (right_mem_uIcc)
  simpa only [Real.norm_eq_abs] using hm

end Hurst
