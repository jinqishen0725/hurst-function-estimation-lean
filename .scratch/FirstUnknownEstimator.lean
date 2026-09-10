import Hurst.SecondSpatial
import Hurst.FirstScale

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace Hurst

def q1UnknownLocalEstimator (r n m : ℕ) (δ t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  boundedInverse (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1
    (gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x-
      q1LogScaleEstimator r n m δ x)

def q1UnknownSpatialEstimator (r n m : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  q1UnknownLocalEstimator r n m δ (clip 0 1 t) x

theorem q1UnknownSpatialEstimator_agrees (r n m : ℕ) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    q1UnknownSpatialEstimator r n m δ x t = q1UnknownLocalEstimator r n m δ t x := by
  rw [q1UnknownSpatialEstimator, clip_identity 0 1 t ht]

theorem q1UnknownSpatialEstimator_mem (r n m : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    q1UnknownSpatialEstimator r n m δ x t ∈ Icc (0:ℝ) 1 :=
  (boundedInverse_spec _ 0 1 _ (by norm_num) (calibrationOne_continuous _ _).continuousOn).1

theorem q1UnknownSpatialEstimator_joint_measurable (r n m : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, IsUnit (localDesignGram r n 1 δ t).det) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => q1UnknownSpatialEstimator r n m δ z.1 z.2) := by
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n)
    (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _)).continuous.measurable
  have hw : ∀ i, Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => localPolynomialWeights r n 1 δ (clip 0 1 z.2) i) :=
    fun i => (localWeights_clamped_continuous r n δ hdet i).measurable.comp measurable_snd
  have hS : Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => q1LogScaleEstimator r n m δ z.1) :=
    (q1LogScaleEstimator_measurable r n m δ).comp measurable_fst
  unfold q1UnknownSpatialEstimator q1UnknownLocalEstimator gaussianLogStatistic
  exact hi.comp ((Finset.measurable_sum _ (fun i _ => (hw i).mul (by fun_prop))).sub hS)

theorem q1UnknownSpatialEstimator_continuous (r n m : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, IsUnit (localDesignGram r n 1 δ t).det) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (q1UnknownSpatialEstimator r n m δ x) := by
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n)
    (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _)).continuous
  unfold q1UnknownSpatialEstimator q1UnknownLocalEstimator gaussianLogStatistic
  exact hi.comp ((continuous_finsetSum _ (fun i _ => (localWeights_clamped_continuous r n δ hdet i).mul continuous_const)).sub continuous_const)

end Hurst
