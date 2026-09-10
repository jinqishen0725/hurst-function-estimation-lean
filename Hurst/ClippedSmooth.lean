import Hurst.SmoothJetBounds
import Hurst.Corrections

noncomputable section
open Set MeasureTheory
namespace Hurst

theorem smooth_clipped_error (phi : ℝ → ℝ) (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1))
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 1, ∀ x H : ℝ, H ∈ Icc a b → |phi (clip a b x)-phi H| ≤ C*|x-H| := by
  obtain ⟨C, hC, hjet⟩ := smooth_uniform_jet_control phi hphi 0 a b ha hb
  refine ⟨C, hC, ?_⟩
  intro x H hH
  have he := (hjet 0 (by omega)).2 (clip a b x) (clip_mem a b x (hH.1.trans hH.2)) H hH
  simp only [iteratedDeriv_zero] at he
  have hh := clip_error a b x H hH
  have he' : |phi (clip a b x)-phi H| ≤ C*|clip a b x-H| := by
    simpa only [abs_sub_comm] using he
  exact he'.trans (mul_le_mul_of_nonneg_left hh (by linarith))

end Hurst
