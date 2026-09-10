import Hurst.UnknownEstimator
import Hurst.CalibratedDecision

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem q2UnknownSpatialEstimator_decision_measurable
    (s : {s : ℝ // 1 ≤ s}) (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (r n m : ℕ) (hn : 1 < n) (δ D : ℝ) (hD : 0 ≤ D)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, IsUnit (localDesignGram r n 2 δ t).det)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, ∑ i, |localPolynomialWeights r n 2 δ t i| ≤ D) :
    Measurable (fun x => continuousHurstDecision s (q2UnknownSpatialEstimator a b r n m δ x)
      (q2UnknownSpatialEstimator_continuous a b hb0 hb1 r n m hn δ hdet x)) := by
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  let w : ℝ → Option (Fin (n-2)) → ℝ := fun t o => match o with
    | none => -1
    | some i => localPolynomialWeights r n 2 δ (clip 0 1 t) i
  have hwc : ∀ o, Continuous (fun t => w t o) := by
    intro o
    cases o with
    | none => exact continuous_const
    | some i => exact secondLocalWeights_clamped_continuous r n δ hdet i
  have hwb : ∀ t ∈ Ioo (0:ℝ) 1, ∑ o, |w t o| ≤ D+1 := by
    intro t ht
    rw [Fintype.sum_option]
    have he := hw (clip 0 1 t) (clip_mem 0 1 t (by norm_num))
    dsimp [w]
    norm_num only [abs_neg, abs_one]
    linarith
  have hi := boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 b (2*Real.log n)
    (by positivity) hb0 (calibrationTwo_continuousOn _ _ b hb1) (calibrationTwo_strongDecrease _ _ b hb1)
  have hd := calibrated_decision_measurable s w hwc _ _ hi (D+1) (by positivity) hwb
  let z : EuclideanSpace ℝ (Fin n) → Option (Fin (n-2)) → ℝ := fun x o => match o with
    | none => q2LogScaleEstimator a b r n m δ x
    | some i => Real.log (⟪gridSecondCoefficients n i, x⟫^2)
  have hz : Measurable z := by
    apply measurable_pi_lambda
    intro o
    cases o with
    | none => exact q2LogScaleEstimator_measurable a b r n m δ
    | some i => dsimp [z]; fun_prop
  have he := hd.comp hz
  convert he using 1
  funext x
  congr 1
  funext t
  simp only [continuousHurstDecision, q2UnknownSpatialEstimator, q2UnknownLocalEstimator, smooth, Fintype.sum_option, w, z]
  congr 1
  unfold gaussianLogStatistic
  ring

end Hurst
