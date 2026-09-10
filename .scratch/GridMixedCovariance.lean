import Hurst.MixedKernelGeneral
import Hurst.MeshRescaling

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

/-- Actual mixed frozen/parameter-variation covariance, uniform over the full observation mesh. -/
theorem grid_mixed_covariance_bound (lo hi : ℝ)
    (hlo : 0 < lo) (hhi : hi < 1) (hlh : lo ≤ hi) :
    ∃ K ≥ 0, ∀ n : ℕ, 0 < n → ∀ h k l : Ioo (0 : ℝ) 1,
      (h : ℝ) ∈ Icc lo hi → (k : ℝ) ∈ Icc lo hi → (l : ℝ) ∈ Icc lo hi →
      ∀ u v t B : ℝ, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      halfMeshPoint n u → halfMeshPoint n v → halfMeshPoint n t →
      |u - v| ≤ 1 / n → 0 ≤ B → |(k : ℝ) - l| ≤ B / n →
      |⟪((n : ℝ) ^ (h : ℝ)) • (harmonizableFeature h u - harmonizableFeature h v),
        ((n : ℝ) ^ (k : ℝ)) • (harmonizableFeature l t - harmonizableFeature k t)⟫| ≤
        K * B * Real.exp B * (1 + Real.log (2 * (n : ℝ))) *
          ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * hi - 2)) := by
  obtain ⟨K, hK, hbound⟩ := kernelIncrement_mesh_parameter_bound_general lo hi hlo hhi hlh
  refine ⟨2 * K, by positivity, ?_⟩
  intro n hn h k l hh hk hl u v t B hu hv ht hum hvm htm huv hB hkl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith)
    linarith
  have he := hbound n hn h l k u v t (1 / n) hh hl hk hu hv ht hum hvm htm (by positivity) huv
  rw [abs_sub_comm (l : ℝ) (k : ℝ), min_comm (l : ℝ) (k : ℝ)] at he
  have hp := normalized_mesh_envelope_bound n hn h k l hi B h.property.1 k.property.1 l.property.1 hh.2 hk.2 hB hkl
  rw [real_inner_smul_left, real_inner_smul_right, inner_sub_right,
    harmonizableFeature_increment_cross_inner h l u v t hu.1 hv.1,
    harmonizableFeature_increment_cross_inner h k u v t hu.1 hv.1,
    abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _), abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
  have hcoeff : 0 ≤ K * meshPowerEnvelope n ((h : ℝ) + min (k : ℝ) l) *
      (1 + Real.log (2 * (n : ℝ))) * (1 / n) := by
    have := meshPowerEnvelope_nonneg n ((h : ℝ) + min (k : ℝ) l)
    positivity
  calc
    _ ≤ (n : ℝ) ^ (h : ℝ) * ((n : ℝ) ^ (k : ℝ) *
        (K * meshPowerEnvelope n ((h : ℝ) + min (k : ℝ) l) * (1 + Real.log (2 * (n : ℝ))) * (1 / n) * (B / n))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
      exact he.trans (mul_le_mul_of_nonneg_left hkl hcoeff)
    _ = K * B * (1 + Real.log (2 * (n : ℝ))) *
        ((n : ℝ) ^ ((h : ℝ) + k - 2) * meshPowerEnvelope n ((h : ℝ) + min (k : ℝ) l)) := by
      rw [Real.rpow_sub hn0, Real.rpow_add hn0, Real.rpow_two]
      ring
    _ ≤ K * B * (1 + Real.log (2 * (n : ℝ))) *
        (2 * Real.exp B * ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * hi - 2))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end Hurst
