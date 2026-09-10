import Hurst.HolderGridMSE
import Hurst.LossGeometry
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace Hurst

instance unitInterval_isProbability : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩

theorem clip_continuous (a b : ℝ) : Continuous (clip a b) := by unfold clip; fun_prop

theorem localWeights_clamped_continuous (r n : ℕ) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 1 δ t).det) (i : Fin (n - 1)) :
    Continuous (fun t => localPolynomialWeights r n 1 δ (clip 0 1 t) i) := by
  have hc : ContinuousOn (fun t => localPolynomialWeights r n 1 δ t i) (Icc (0 : ℝ) 1) :=
    fun t ht => (localPolynomialWeights_continuousAt r n 1 δ t (hdet t ht) i).continuousWithinAt
  exact hc.comp_continuous (clip_continuous 0 1) (fun t => clip_mem 0 1 t (by norm_num))

def q1SpatialEstimator (r n : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  q1LocalEstimator r n δ (clip 0 1 t) x

theorem q1SpatialEstimator_agrees (r n : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : q1SpatialEstimator r n δ x t = q1LocalEstimator r n δ t x := by
  rw [q1SpatialEstimator, clip_identity 0 1 t ht]

theorem q1SpatialEstimator_mem (r n : ℕ) (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    q1SpatialEstimator r n δ x t ∈ Icc (0 : ℝ) 1 :=
  (boundedInverse_spec _ 0 1 _ (by norm_num) (calibrationOne_continuous _ _).continuousOn).1

theorem q1SpatialEstimator_joint_measurable (r n : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 1 δ t).det) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => q1SpatialEstimator r n δ z.1 z.2) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2 * Real.log n)
    (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _)).continuous.measurable
  have hw : ∀ i, Measurable (fun z : EuclideanSpace ℝ (Fin n) × ℝ => localPolynomialWeights r n 1 δ (clip 0 1 z.2) i) :=
    fun i => (localWeights_clamped_continuous r n δ hdet i).measurable.comp measurable_snd
  unfold q1SpatialEstimator q1LocalEstimator gaussianLogStatistic
  exact hi.comp (Finset.measurable_sum _ (fun i _ => (hw i).mul (by fun_prop)))

theorem q1SpatialEstimator_continuous (r n : ℕ) (hn : 1 < n) (δ : ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (localDesignGram r n 1 δ t).det) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (q1SpatialEstimator r n δ x) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hL := Real.log_pos hnR
  have hi := (boundedInverse_lipschitz (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2 * Real.log n)
    (by positivity) (by norm_num) (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _)).continuous
  unfold q1SpatialEstimator q1LocalEstimator gaussianLogStatistic
  exact hi.comp (continuous_finsetSum _ (fun i _ => (localWeights_clamped_continuous r n δ hdet i).mul continuous_const))

/-- Bounded jointly measurable estimators allow a verified Fubini step from pointwise to integrated MSE. -/
theorem integrated_mse_of_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → ℝ → ℝ) (g : ℝ → ℝ) (C : ℝ)
    (hF : Measurable (fun z : Ω × ℝ => F z.1 z.2)) (hg : Measurable g)
    (hFb : ∀ x t, F x t ∈ Icc (0 : ℝ) 1) (hgb : ∀ t, g t ∈ Icc (0 : ℝ) 1)
    (hrisk : ∀ t ∈ Ioo (0 : ℝ) 1, (∫ x, (F x t - g t) ^ 2 ∂P) ≤ C) :
    (∫ x, (∫ t in Ioo (0 : ℝ) 1, (F x t - g t) ^ 2) ∂P) ≤ C := by
  have hmeas : Measurable (fun z : Ω × ℝ => (F z.1 z.2 - g z.2) ^ 2) := (hF.sub (hg.comp measurable_snd)).pow_const 2
  have hi : Integrable (fun z : Ω × ℝ => (F z.1 z.2 - g z.2) ^ 2) (P.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hx := hFb z.1 z.2
    have ht := hgb z.2
    have hdiff : |F z.1 z.2 - g z.2| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, ht.2], by linarith [hx.2, ht.1]⟩
    have he := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    simpa only [sq_abs, one_pow] using he
  rw [integral_integral_swap hi]
  have h := integral_mono_ae hi.integral_prod_right (integrable_const C) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hrisk t ht)
  simpa using h

end Hurst
