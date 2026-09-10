import Hurst.CalibratedDecision
import Hurst.SecondSpatial

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem q1SpatialEstimator_decision_measurable
    (s : {s : ℝ // 1 ≤ s}) (r n : ℕ) (hn : 1 < n) (δ D : ℝ) (hD : 0 ≤ D)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 1 δ t).det)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, |localPolynomialWeights r n 1 δ t i| ≤ D) :
    Measurable (fun x => continuousHurstDecision s (q1SpatialEstimator r n δ x)
      (q1SpatialEstimator_continuous r n hn δ hdet x)) := by
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hi := boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1
    (2 * Real.log n) (by positivity) (by norm_num)
    (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _)
  have hm := calibrated_decision_measurable s
    (fun t => localPolynomialWeights r n 1 δ (clip 0 1 t))
    (localWeights_clamped_continuous r n δ hdet) _ _ hi D hD
    (fun t _ => hw _ (clip_mem 0 1 t (by norm_num)))
  have hz : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      fun i => Real.log (⟪gridDifferenceCoefficients n i, x⟫ ^ 2)) := by
    fun_prop
  exact hm.comp hz

theorem q2SpatialEstimator_decision_measurable
    (s : {s : ℝ // 1 ≤ s}) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (r n : ℕ) (hn : 1 < n) (δ D : ℝ) (hD : 0 ≤ D)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 2 δ t).det)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, |localPolynomialWeights r n 2 δ t i| ≤ D) :
    Measurable (fun x => continuousHurstDecision s (q2SpatialEstimator u r n δ x)
      (q2SpatialEstimator_continuous u hu0 hu1 r n hn δ hdet x)) := by
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hi := boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u
    (2 * Real.log n) (by positivity) hu0
    (calibrationTwo_continuousOn _ _ u hu1) (calibrationTwo_strongDecrease _ _ u hu1)
  have hm := calibrated_decision_measurable s
    (fun t => localPolynomialWeights r n 2 δ (clip 0 1 t))
    (secondLocalWeights_clamped_continuous r n δ hdet) _ _ hi D hD
    (fun t _ => hw _ (clip_mem 0 1 t (by norm_num)))
  have hz : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      fun i => Real.log (⟪gridSecondCoefficients n i, x⟫ ^ 2)) := by
    fun_prop
  exact hm.comp hz

end Hurst
