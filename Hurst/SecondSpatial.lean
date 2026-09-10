import Hurst.HolderSecondMSE
import Hurst.SpatialRisk

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

theorem secondLocalWeights_clamped_continuous (r n : ℕ) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 2 δ t).det) (i : Fin (n - 2)) :
    Continuous (fun t => localPolynomialWeights r n 2 δ (clip 0 1 t) i) := by
  have hc : ContinuousOn (fun t => localPolynomialWeights r n 2 δ t i) (Icc (0 : ℝ) 1) :=
    fun t ht => (localPolynomialWeights_continuousAt r n 2 δ t (hdet t ht) i).continuousWithinAt
  exact hc.comp_continuous (clip_continuous 0 1) (fun t => clip_mem 0 1 t (by norm_num))

def q2SpatialEstimator (u : ℝ) (r n : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  q2LocalEstimator u r n δ (clip 0 1 t) x

theorem q2SpatialEstimator_agrees (u : ℝ) (r n : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : q2SpatialEstimator u r n δ x t = q2LocalEstimator u r n δ t x := by
  rw [q2SpatialEstimator, clip_identity 0 1 t ht]

theorem q2SpatialEstimator_mem (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (r n : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    q2SpatialEstimator u r n δ x t ∈ Icc (0 : ℝ) u :=
  (boundedInverse_spec _ 0 u _ hu0 (calibrationTwo_continuousOn _ _ u hu1)).1

theorem q2SpatialEstimator_joint_measurable (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (r n : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 2 δ t).det) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => q2SpatialEstimator u r n δ z.1 z.2) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hi := (boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (2 * Real.log n)
    (by positivity) hu0 (calibrationTwo_continuousOn _ _ u hu1) (calibrationTwo_strongDecrease _ _ u hu1)).continuous.measurable
  have hw : ∀ i, Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => localPolynomialWeights r n 2 δ (clip 0 1 z.2) i) :=
    fun i => (secondLocalWeights_clamped_continuous r n δ hdet i).measurable.comp measurable_snd
  unfold q2SpatialEstimator q2LocalEstimator gaussianLogStatistic
  exact hi.comp (Finset.measurable_sum _ (fun i _ => (hw i).mul (by fun_prop)))

theorem q2SpatialEstimator_continuous (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (r n : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 2 δ t).det) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (q2SpatialEstimator u r n δ x) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hL := Real.log_pos hnR
  have hi := (boundedInverse_lipschitz (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (2 * Real.log n)
    (by positivity) hu0 (calibrationTwo_continuousOn _ _ u hu1) (calibrationTwo_strongDecrease _ _ u hu1)).continuous
  unfold q2SpatialEstimator q2LocalEstimator gaussianLogStatistic
  exact hi.comp (continuous_finsetSum _ (fun i _ => (secondLocalWeights_clamped_continuous r n δ hdet i).mul continuous_const))

end Hurst
