import Hurst.SpectralSmooth
import Hurst.HolderTaylor

noncomputable section
open Set
namespace Hurst

theorem smooth_differentiable_iteratedDeriv (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo (0 : ℝ) 1)) (k : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (iteratedDeriv k f) x := by
  have hd0 := hf.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast (show (k : ℕ∞) < ⊤ from WithTop.coe_lt_top k)) isOpen_Ioo.uniqueDiffOn
  have hd : DifferentiableOn ℝ (iteratedDeriv k f) (Ioo (0 : ℝ) 1) := by
    apply hd0.congr
    intro u hu
    exact (iteratedDerivWithin_of_isOpen (n := k) isOpen_Ioo hu).symm
  exact hd.differentiableAt (isOpen_Ioo.mem_nhds hx)

/-- Compact-uniform first-order Taylor remainder for a smooth scalar parameter function. -/
theorem smooth_uniform_quadratic_remainder (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo (0 : ℝ) 1)) (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h k : ℝ, h ∈ Icc a b → k ∈ Icc a b →
      |f k - f h - (k - h) * deriv f h| ≤ C * |k - h| ^ 2 := by
  obtain ⟨C, hC, hc⟩ := smooth_uniform_iteratedDeriv_bound f hf a b ha hb 2
  refine ⟨C / 2, by positivity, ?_⟩
  intro h k hh hk
  by_cases heq : h = k
  · subst k
    simp
  obtain ⟨z, hz, he⟩ := interval_taylor_lagrange f 1 (fun k _ x hx => smooth_differentiable_iteratedDeriv f hf k x hx)
    h k ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩ ⟨ha.trans_le hk.1, hk.2.trans_lt hb⟩ heq
  simp only [Fin.sum_univ_succ] at he
  norm_num [iteratedDeriv_zero, iteratedDeriv_one] at he
  have hzab : z ∈ Icc a b := (uIcc_subset_Icc hh hk) ⟨hz.1.le, hz.2.le⟩
  have hcoeff := hc z hzab
  have hR : f k - f h - (k - h) * deriv f h = iteratedDeriv 2 f z * (k - h) ^ 2 / 2 := by linarith
  rw [hR, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (k - h)), abs_of_pos (by norm_num : (0 : ℝ) < 2), sq_abs]
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (k - h))
  nlinarith

theorem harmonizableNormalizer_quadratic_remainder (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 0, ∀ h k : ℝ, h ∈ Icc a b → k ∈ Icc a b →
      |harmonizableNormalizer k - harmonizableNormalizer h - (k - h) * harmonizableNormalizerSlope h| ≤ C * |k - h| ^ 2 := by
  obtain ⟨C, hC, hc⟩ := smooth_uniform_quadratic_remainder harmonizableNormalizer harmonizableNormalizer_smooth a b ha hb
  refine ⟨C, hC, ?_⟩
  intro h k hh hk
  have hd := (harmonizableNormalizer_hasDerivAt h (ha.trans_le hh.1) (hh.2.trans_lt hb)).deriv
  simpa only [hd] using hc h k hh hk

end Hurst
