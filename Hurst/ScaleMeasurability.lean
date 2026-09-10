import Hurst.ScaleAverage
import Hurst.SmoothJetBounds
import Hurst.SpatialRisk

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem q2Pilot_measurable (r n : ℕ) (δ t : ℝ) : Measurable (q2Pilot r n δ t) := by
  unfold q2Pilot twoScalePilot gaussianLogStatistic
  fun_prop

theorem q2LogScaleEstimator_measurable (a b : ℝ) (r n m : ℕ) (δ : ℝ) :
    Measurable (q2LogScaleEstimator a b r n m δ) := by
  unfold q2LogScaleEstimator q2LinearScale linearScaleCombination gaussianLogStatistic
  have hp : ∀ j : Fin m, Measurable (q2Pilot r n δ (grid m j.val)) := fun j => q2Pilot_measurable _ _ _ _
  have hphi : Measurable q2LogCorrection := by unfold q2LogCorrection; fun_prop
  have hclip := (clip_continuous a b).measurable
  fun_prop

theorem q2LogScaleEstimator_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r n m : ℕ) (δ a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) (v : Fin n → E)
    (h₁ : ∀ i, ∑ j, commonStrideCoefficients n 1 4 (by norm_num) i j • v j ≠ 0)
    (h₂ : ∀ i, ∑ j, commonStrideCoefficients n 2 4 (by norm_num) i j • v j ≠ 0) :
    MemLp (q2LogScaleEstimator a b r n m δ) 2 (featureGaussian v) := by
  have hG₁ := gaussianLogStatistic_memLp_two v (averagedLocalWeights r n 4 m δ) _ h₁
  have hG₂ := gaussianLogStatistic_memLp_two v (averagedLocalWeights r n 4 m δ) _ h₂
  have hlin : MemLp (q2LinearScale r n m δ) 2 (featureGaussian v) :=
    (hG₁.const_mul _).add (hG₂.const_mul _)
  obtain ⟨C, hC, hbound⟩ := smooth_uniform_jet_control q2LogCorrection q2LogCorrection_smooth 0 a b ha hb
  have hc : ∀ j : Fin m, MemLp (fun x => q2LogCorrection (clip a b (q2Pilot r n δ (grid m j.val) x))) 2 (featureGaussian v) := by
    intro j
    have hphi : Measurable q2LogCorrection := by unfold q2LogCorrection; fun_prop
    have hclip := (clip_continuous a b).measurable
    apply MemLp.of_bound (hphi.comp (hclip.comp (q2Pilot_measurable r n δ (grid m j.val)))).aestronglyMeasurable C
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, iteratedDeriv_zero, Function.comp_apply] using (hbound 0 (by omega)).1 _ (clip_mem a b _ hab)
  have havg : MemLp (fun x => (∑ j : Fin m, q2LogCorrection (clip a b (q2Pilot r n δ (grid m j.val) x)))) 2 (featureGaussian v) :=
    memLp_finsetSum _ (fun j _ => hc j)
  have he := (hlin.sub (havg.mul_const (m:ℝ)⁻¹)).sub (memLp_const gaussianLogSquareMean)
  change MemLp (fun x => q2LinearScale r n m δ x-(∑ j : Fin m, q2LogCorrection (clip a b (q2Pilot r n δ (grid m j.val) x)))/(m:ℝ)-gaussianLogSquareMean) 2 (featureGaussian v)
  simp only [div_eq_mul_inv]
  exact he

end Hurst
