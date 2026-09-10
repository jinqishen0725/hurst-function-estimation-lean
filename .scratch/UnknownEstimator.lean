import Hurst.SecondSpatial
import Hurst.ScaleMeasurability

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

def q2UnknownLocalEstimator (a b : ℝ) (r n m : ℕ) (δ t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  boundedInverse (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 b
    (gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x-
      q2LogScaleEstimator a b r n m δ x)

def q2UnknownSpatialEstimator (a b : ℝ) (r n m : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  q2UnknownLocalEstimator a b r n m δ (clip 0 1 t) x

theorem q2UnknownSpatialEstimator_agrees (a b : ℝ) (r n m : ℕ) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    q2UnknownSpatialEstimator a b r n m δ x t = q2UnknownLocalEstimator a b r n m δ t x := by
  rw [q2UnknownSpatialEstimator, clip_identity 0 1 t ht]

theorem q2UnknownSpatialEstimator_mem (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (r n m : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    q2UnknownSpatialEstimator a b r n m δ x t ∈ Icc (0:ℝ) b :=
  (boundedInverse_spec _ 0 b _ hb0 (calibrationTwo_continuousOn _ _ b hb1)).1

theorem q2UnknownSpatialEstimator_joint_measurable (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (r n m : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, IsUnit (localDesignGram r n 2 δ t).det) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => q2UnknownSpatialEstimator a b r n m δ z.1 z.2) := by
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hi := (boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 b (2*Real.log n)
    (by positivity) hb0 (calibrationTwo_continuousOn _ _ b hb1) (calibrationTwo_strongDecrease _ _ b hb1)).continuous.measurable
  have hw : ∀ i, Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => localPolynomialWeights r n 2 δ (clip 0 1 z.2) i) :=
    fun i => (secondLocalWeights_clamped_continuous r n δ hdet i).measurable.comp measurable_snd
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => q2LogScaleEstimator a b r n m δ z.1) :=
    (q2LogScaleEstimator_measurable a b r n m δ).comp measurable_fst
  unfold q2UnknownSpatialEstimator q2UnknownLocalEstimator gaussianLogStatistic
  exact hi.comp ((Finset.measurable_sum _ (fun i _ => (hw i).mul (by fun_prop))).sub hS)

theorem q2UnknownSpatialEstimator_continuous (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (r n m : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, IsUnit (localDesignGram r n 2 δ t).det) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (q2UnknownSpatialEstimator a b r n m δ x) := by
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hi := (boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 b (2*Real.log n)
    (by positivity) hb0 (calibrationTwo_continuousOn _ _ b hb1) (calibrationTwo_strongDecrease _ _ b hb1)).continuous
  unfold q2UnknownSpatialEstimator q2UnknownLocalEstimator gaussianLogStatistic
  exact hi.comp ((continuous_finsetSum _ (fun i _ => (secondLocalWeights_clamped_continuous r n δ hdet i).mul continuous_const)).sub continuous_const)

end Hurst
