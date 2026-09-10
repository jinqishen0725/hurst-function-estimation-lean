import Hurst.InverseMoment
import Hurst.FirstUnknownEstimator
import Hurst.UnknownEstimator

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst

theorem q1_known_spatial_risk_of_raw_moments (r n : ℕ) (δ : ℝ) (hn : 1<n) 
    (P : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure P]
    (s e : ℝ) (hs : 2≤s) (he : 0≤e) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : MapsTo g (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
    (hdet : ∀ t∈Icc (0:ℝ) 1,IsUnit (localDesignGram r n 1 δ t).det)
    (hraw : ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x) (ENNReal.ofReal s) P ∧
      (∫ x,|(gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x)-calibrationOne (Real.log n) gaussianLogSquareMean (g t)|^s ∂P)≤(2*Real.log n*e)^s) :
    (∫ x,(unitLpLoss s (q1SpatialEstimator r n δ x) g)^2 ∂P)≤e^2 := by
  let F := q1SpatialEstimator r n δ
  let g' := fun t => g (clip 0 1 t)
  have hgc : Continuous g' := hg.comp (clip_continuous 0 1)
  have hF := q1SpatialEstimator_joint_measurable r n hn δ hdet
  have hFc := fun x => q1SpatialEstimator_continuous r n hn δ hdet x
  have hFb : ∀ x t,F x t∈Icc (0:ℝ) 1 := by
    intro x t
    have hh := q1SpatialEstimator_mem r n δ x t
    exact hh
  have hgb' : ∀ t,g' t∈Icc (0:ℝ) 1 := by
    intro t
    have hh := hgb (clip_mem 0 1 t (by norm_num))
    exact hh
  have hpoint : ∀ t∈Ioo (0:ℝ) 1,(∫ x,|F x t-g' t|^s ∂P)≤e^s := by
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hh := boundedInverse_moment_rate P (fun x => gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x)
      (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n) (g t) s e
      (by positivity) (by linarith) he (by norm_num)
      (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _) (hgb ht') (hraw t ht).1 (hraw t ht).2
    dsimp only [F,g']
    simp only [q1SpatialEstimator_agrees r n δ _ t ht',clip_identity 0 1 t ht']
    exact hh
  have h := unitLpRisk_rate_of_uniform_moment P s hs e he F g' hF hgc hFc hFb hgb' hpoint
  have hid (x : EuclideanSpace ℝ (Fin n)) : unitLpLoss s (F x) g'=unitLpLoss s (F x) g := by
    unfold unitLpLoss
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [g']
    rw [clip_identity 0 1 t ⟨ht.1.le,ht.2.le⟩]
  simp_rw [hid] at h
  exact h

theorem q1_unknown_spatial_risk_of_raw_moments (r n m : ℕ) (δ : ℝ) (hn : 1<n) 
    (P : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure P]
    (s e : ℝ) (hs : 2≤s) (he : 0≤e) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : MapsTo g (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
    (hdet : ∀ t∈Icc (0:ℝ) 1,IsUnit (localDesignGram r n 1 δ t).det)
    (hraw : ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x-q1LogScaleEstimator r n m δ x) (ENNReal.ofReal s) P ∧
      (∫ x,|(gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x-q1LogScaleEstimator r n m δ x)-calibrationOne (Real.log n) gaussianLogSquareMean (g t)|^s ∂P)≤(2*Real.log n*e)^s) :
    (∫ x,(unitLpLoss s (q1UnknownSpatialEstimator r n m δ x) g)^2 ∂P)≤e^2 := by
  let F := q1UnknownSpatialEstimator r n m δ
  let g' := fun t => g (clip 0 1 t)
  have hgc : Continuous g' := hg.comp (clip_continuous 0 1)
  have hF := q1UnknownSpatialEstimator_joint_measurable r n m hn δ hdet
  have hFc := fun x => q1UnknownSpatialEstimator_continuous r n m hn δ hdet x
  have hFb : ∀ x t,F x t∈Icc (0:ℝ) 1 := by
    intro x t
    have hh := q1UnknownSpatialEstimator_mem r n m δ x t
    exact hh
  have hgb' : ∀ t,g' t∈Icc (0:ℝ) 1 := by
    intro t
    have hh := hgb (clip_mem 0 1 t (by norm_num))
    exact hh
  have hpoint : ∀ t∈Ioo (0:ℝ) 1,(∫ x,|F x t-g' t|^s ∂P)≤e^s := by
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hh := boundedInverse_moment_rate P (fun x => gaussianLogStatistic (localPolynomialWeights r n 1 δ t) (gridDifferenceCoefficients n) x-q1LogScaleEstimator r n m δ x)
      (calibrationOne (Real.log n) gaussianLogSquareMean) 0 1 (2*Real.log n) (g t) s e
      (by positivity) (by linarith) he (by norm_num)
      (calibrationOne_continuous _ _).continuousOn (calibrationOne_strongDecrease _ _ _ _) (hgb ht') (hraw t ht).1 (hraw t ht).2
    dsimp only [F,g']
    simp only [q1UnknownSpatialEstimator_agrees r n m δ _ t ht',clip_identity 0 1 t ht']
    exact hh
  have h := unitLpRisk_rate_of_uniform_moment P s hs e he F g' hF hgc hFc hFb hgb' hpoint
  have hid (x : EuclideanSpace ℝ (Fin n)) : unitLpLoss s (F x) g'=unitLpLoss s (F x) g := by
    unfold unitLpLoss
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [g']
    rw [clip_identity 0 1 t ⟨ht.1.le,ht.2.le⟩]
  simp_rw [hid] at h
  exact h

theorem q2_known_spatial_risk_of_raw_moments (r n : ℕ) (δ : ℝ) (hn : 1<n) (u : ℝ) (hu0 : 0≤u) (hu1 : u<1)
    (P : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure P]
    (s e : ℝ) (hs : 2≤s) (he : 0≤e) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : MapsTo g (Icc (0:ℝ) 1) (Icc (0:ℝ) u))
    (hdet : ∀ t∈Icc (0:ℝ) 1,IsUnit (localDesignGram r n 2 δ t).det)
    (hraw : ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x) (ENNReal.ofReal s) P ∧
      (∫ x,|(gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x)-calibrationTwo (Real.log n) gaussianLogSquareMean (g t)|^s ∂P)≤(2*Real.log n*e)^s) :
    (∫ x,(unitLpLoss s (q2SpatialEstimator u r n δ x) g)^2 ∂P)≤e^2 := by
  let F := q2SpatialEstimator u r n δ
  let g' := fun t => g (clip 0 1 t)
  have hgc : Continuous g' := hg.comp (clip_continuous 0 1)
  have hF := q2SpatialEstimator_joint_measurable u hu0 hu1 r n hn δ hdet
  have hFc := fun x => q2SpatialEstimator_continuous u hu0 hu1 r n hn δ hdet x
  have hFb : ∀ x t,F x t∈Icc (0:ℝ) 1 := by
    intro x t
    have hh := q2SpatialEstimator_mem u hu0 hu1 r n δ x t
    exact ⟨hh.1,hh.2.trans hu1.le⟩
  have hgb' : ∀ t,g' t∈Icc (0:ℝ) 1 := by
    intro t
    have hh := hgb (clip_mem 0 1 t (by norm_num))
    exact ⟨hh.1,hh.2.trans hu1.le⟩
  have hpoint : ∀ t∈Ioo (0:ℝ) 1,(∫ x,|F x t-g' t|^s ∂P)≤e^s := by
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hh := boundedInverse_moment_rate P (fun x => gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x)
      (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (2*Real.log n) (g t) s e
      (by positivity) (by linarith) he hu0
      (calibrationTwo_continuousOn _ _ u hu1) (calibrationTwo_strongDecrease _ _ u hu1) (hgb ht') (hraw t ht).1 (hraw t ht).2
    dsimp only [F,g']
    simp only [q2SpatialEstimator_agrees u r n δ _ t ht',clip_identity 0 1 t ht']
    exact hh
  have h := unitLpRisk_rate_of_uniform_moment P s hs e he F g' hF hgc hFc hFb hgb' hpoint
  have hid (x : EuclideanSpace ℝ (Fin n)) : unitLpLoss s (F x) g'=unitLpLoss s (F x) g := by
    unfold unitLpLoss
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [g']
    rw [clip_identity 0 1 t ⟨ht.1.le,ht.2.le⟩]
  simp_rw [hid] at h
  exact h

theorem q2_unknown_spatial_risk_of_raw_moments (r n m : ℕ) (δ : ℝ) (hn : 1<n) (a u : ℝ) (hu0 : 0≤u) (hu1 : u<1)
    (P : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure P]
    (s e : ℝ) (hs : 2≤s) (he : 0≤e) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : MapsTo g (Icc (0:ℝ) 1) (Icc (0:ℝ) u))
    (hdet : ∀ t∈Icc (0:ℝ) 1,IsUnit (localDesignGram r n 2 δ t).det)
    (hraw : ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x-q2LogScaleEstimator a u r n m δ x) (ENNReal.ofReal s) P ∧
      (∫ x,|(gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x-q2LogScaleEstimator a u r n m δ x)-calibrationTwo (Real.log n) gaussianLogSquareMean (g t)|^s ∂P)≤(2*Real.log n*e)^s) :
    (∫ x,(unitLpLoss s (q2UnknownSpatialEstimator a u r n m δ x) g)^2 ∂P)≤e^2 := by
  let F := q2UnknownSpatialEstimator a u r n m δ
  let g' := fun t => g (clip 0 1 t)
  have hgc : Continuous g' := hg.comp (clip_continuous 0 1)
  have hF := q2UnknownSpatialEstimator_joint_measurable a u hu0 hu1 r n m hn δ hdet
  have hFc := fun x => q2UnknownSpatialEstimator_continuous a u hu0 hu1 r n m hn δ hdet x
  have hFb : ∀ x t,F x t∈Icc (0:ℝ) 1 := by
    intro x t
    have hh := q2UnknownSpatialEstimator_mem a u hu0 hu1 r n m δ x t
    exact ⟨hh.1,hh.2.trans hu1.le⟩
  have hgb' : ∀ t,g' t∈Icc (0:ℝ) 1 := by
    intro t
    have hh := hgb (clip_mem 0 1 t (by norm_num))
    exact ⟨hh.1,hh.2.trans hu1.le⟩
  have hpoint : ∀ t∈Ioo (0:ℝ) 1,(∫ x,|F x t-g' t|^s ∂P)≤e^s := by
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hh := boundedInverse_moment_rate P (fun x => gaussianLogStatistic (localPolynomialWeights r n 2 δ t) (gridSecondCoefficients n) x-q2LogScaleEstimator a u r n m δ x)
      (calibrationTwo (Real.log n) gaussianLogSquareMean) 0 u (2*Real.log n) (g t) s e
      (by positivity) (by linarith) he hu0
      (calibrationTwo_continuousOn _ _ u hu1) (calibrationTwo_strongDecrease _ _ u hu1) (hgb ht') (hraw t ht).1 (hraw t ht).2
    dsimp only [F,g']
    simp only [q2UnknownSpatialEstimator_agrees a u r n m δ _ t ht',clip_identity 0 1 t ht']
    exact hh
  have h := unitLpRisk_rate_of_uniform_moment P s hs e he F g' hF hgc hFc hFb hgb' hpoint
  have hid (x : EuclideanSpace ℝ (Fin n)) : unitLpLoss s (F x) g'=unitLpLoss s (F x) g := by
    unfold unitLpLoss
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [g']
    rw [clip_identity 0 1 t ⟨ht.1.le,ht.2.le⟩]
  simp_rw [hid] at h
  exact h

end Hurst
