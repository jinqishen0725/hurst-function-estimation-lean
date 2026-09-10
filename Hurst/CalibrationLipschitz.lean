import Hurst.LogCorrectionSmooth
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set
namespace Hurst

theorem q2LogCorrection_lipschitz_closed (u : ℝ) (hu : u<1) :
    ∃ K≥0,∀ x∈Icc (0:ℝ) u,∀ y∈Icc (0:ℝ) u,|q2LogCorrection x-q2LogCorrection y|≤K*|x-y| := by
  have hp : ContDiff ℝ 1 (fun h : ℝ => (2:ℝ)^(2*h)) :=
    contDiff_const.rpow (contDiff_const.mul contDiff_id) (by intro h; norm_num)
  have hc : ContDiffOn ℝ 1 q2LogCorrection (Icc (0:ℝ) u) :=
    (contDiff_const.sub hp).contDiffOn.log (fun h hh => (calibrationTwo_positive_inside h (hh.2.trans_lt hu)).ne')
  obtain ⟨K,hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨K,K.coe_nonneg,?_⟩
  intro x hx y hy
  simpa only [Real.dist_eq] using hK.dist_le_mul x hx y hy

end Hurst
