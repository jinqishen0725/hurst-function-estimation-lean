import Hurst.SpatialRisk

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Hurst

theorem continuousHurstDecision_edist_le_bound (s : {s : ℝ // 1 ≤ s})
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (C : ℝ)
    (hfg : ∀ t ∈ Ioo (0 : ℝ) 1, |f t - g t| ≤ C) :
    edist (continuousHurstDecision s f hf) (continuousHurstDecision s g hg) ≤ ENNReal.ofReal C := by
  rw [hurstDecision_edist]
  have he := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal s.val) (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := f - g) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hfg t ht)
  simpa only [continuousHurstDecision, measure_univ, ENNReal.one_rpow, one_mul] using he

/-- Uniform Lipschitz continuity of curves implies continuity in the full Ls decision space. -/
theorem continuousHurstDecision_map_lipschitz {Z : Type*} [PseudoMetricSpace Z]
    (s : {s : ℝ // 1 ≤ s}) (F : Z → ℝ → ℝ) (hF : ∀ z, Continuous (F z))
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ z w t, t ∈ Ioo (0 : ℝ) 1 → |F z t - F w t| ≤ L * dist z w) :
    LipschitzWith (Real.toNNReal L) (fun z => continuousHurstDecision s (F z) (hF z)) := by
  intro z w
  have he := continuousHurstDecision_edist_le_bound s (F z) (F w) (hF z) (hF w) (L * dist z w) (hLip z w)
  rw [ENNReal.ofReal_mul hL] at he
  simpa only [edist_dist, ENNReal.ofReal] using he

end Hurst
