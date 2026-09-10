import Hurst.FirstUnknownEstimator
import Hurst.CalibratedDecision

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem q1UnknownSpatialEstimator_decision_measurable
    (s : {s : ℝ // 1 ≤ s}) (r n m : ℕ) (hn : 1 < n) (δ D : ℝ) (hD : 0 ≤ D)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, IsUnit (localDesignGram r n 1 δ t).det)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, ∑ i, |localPolynomialWeights r n 1 δ t i| ≤ D) :
    Measurable (fun x => continuousHurstDecision s (q1UnknownSpatialEstimator r n m δ x)
      (q1UnknownSpatialEstimator_continuous r n m hn δ hdet x)) := by
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  let w : ℝ → Option (Fin (n-1)) → ℝ := fun t o => match o with
    | none => -1
    | some i => localPolynomialWeights r n 1 δ (clip 0 1 t) i
  have hwc : ∀ o, Continuous (fun t => w t o) := by
    intro o
    cases o with
    | none => exact continuous_const
    | some i => exact localWeights_clamped_continuous r n δ hdet i
  have hwb : ∀ t ∈ Ioo (0:ℝ) 1, ∑ o, |w t o| ≤ D+1 := by
    intro t ht
    rw [Fintype.sum_option]
    have he := hw (clip 0 1 t) (clip_mem 0 1 t (by norm_num))
    dsimp [w]
    norm_num only [abs_neg, abs_one]
    linarith
  have hi := boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n)
    (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _)
  have hd := calibrated_decision_measurable s w hwc _ _ hi (D+1) (by positivity) hwb
  let z : EuclideanSpace ℝ (Fin n) → Option (Fin (n-1)) → ℝ := fun x o => match o with
    | none => q1LogScaleEstimator r n m δ x
    | some i => Real.log (⟪gridDifferenceCoefficients n i, x⟫^2)
  have hz : Measurable z := by
    apply measurable_pi_lambda
    intro o
    cases o with
    | none => exact q1LogScaleEstimator_measurable r n m δ
    | some i => dsimp [z]; fun_prop
  have he := hd.comp hz
  convert he using 1
  funext x
  congr 1
  funext t
  simp only [continuousHurstDecision, q1UnknownSpatialEstimator, q1UnknownLocalEstimator, smooth, Fintype.sum_option, w, z]
  congr 1
  unfold gaussianLogStatistic
  ring

end Hurst
