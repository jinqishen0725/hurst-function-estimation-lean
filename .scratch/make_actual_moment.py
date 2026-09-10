from pathlib import Path
s='''import Hurst.InverseMoment
import Hurst.FirstUnknownEstimator
import Hurst.UnknownEstimator

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Hurst
'''
for q in [1,2]:
 for unknown in [False,True]:
  nm=f'q{q}'+('_unknown' if unknown else '_known')
  spatial=f'q{q}'+('UnknownSpatialEstimator' if unknown else 'SpatialEstimator')
  prefix=('a u ' if unknown else 'u ') if q==2 else ''
  margs='m ' if unknown else ''
  args=f'{prefix}r n {margs}δ'
  measargs=(f'{prefix}hu0 hu1 ' if q==2 else '')+f'r n {margs}hn δ hdet'
  memargs=(f'{prefix}hu0 hu1 ' if q==2 else '')+f'r n {margs}δ'
  extra='(a u : ℝ) (hu0 : 0≤u) (hu1 : u<1)' if q==2 and unknown else '(u : ℝ) (hu0 : 0≤u) (hu1 : u<1)' if q==2 else ''
  coeff='gridDifferenceCoefficients n' if q==1 else 'gridSecondCoefficients n'
  raw=f'gaussianLogStatistic (localPolynomialWeights r n {q} δ t) ({coeff}) x'
  if unknown:raw+=f'-q{q}LogScaleEstimator '+('a u ' if q==2 else '')+'r n m δ x'
  cal='calibrationOne' if q==1 else 'calibrationTwo'
  hi='(calibrationOne_continuous _ _).continuousOn' if q==1 else '(calibrationTwo_continuousOn _ _ u hu1)'
  hdec='(calibrationOne_strongDecrease _ _ _ _)' if q==1 else '(calibrationTwo_strongDecrease _ _ u hu1)'
  up='1' if q==1 else 'u'
  s+=f'''
theorem {nm}_spatial_risk_of_raw_moments (r n {'m ' if unknown else ''}: ℕ) (δ : ℝ) (hn : 1<n) {extra}
    (P : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure P]
    (s e : ℝ) (hs : 2≤s) (he : 0≤e) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : MapsTo g (Icc (0:ℝ) 1) (Icc (0:ℝ) {up}))
    (hdet : ∀ t∈Icc (0:ℝ) 1,IsUnit (localDesignGram r n {q} δ t).det)
    (hraw : ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => {raw}) (ENNReal.ofReal s) P ∧
      (∫ x,|({raw})-{cal} (Real.log n) gaussianLogSquareMean (g t)|^s ∂P)≤(2*Real.log n*e)^s) :
    (∫ x,(unitLpLoss s ({spatial} {args} x) g)^2 ∂P)≤e^2 := by
  let F := {spatial} {args}
  let g' := fun t => g (clip 0 1 t)
  have hgc : Continuous g' := hg.comp (clip_continuous 0 1)
  have hF := {spatial}_joint_measurable {measargs}
  have hFc := fun x => {spatial}_continuous {measargs} x
  have hFb : ∀ x t,F x t∈Icc (0:ℝ) 1 := by
    intro x t
    have hh := {spatial}_mem {memargs} x t
    {'exact hh' if q==1 else 'exact ⟨hh.1,hh.2.trans hu1.le⟩'}
  have hgb' : ∀ t,g' t∈Icc (0:ℝ) 1 := by
    intro t
    have hh := hgb (clip_mem 0 1 t (by norm_num))
    {'exact hh' if q==1 else 'exact ⟨hh.1,hh.2.trans hu1.le⟩'}
  have hpoint : ∀ t∈Ioo (0:ℝ) 1,(∫ x,|F x t-g' t|^s ∂P)≤e^s := by
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hL : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hh := boundedInverse_moment_rate P (fun x => {raw})
      ({cal} (Real.log n) gaussianLogSquareMean) 0 {up} (2*Real.log n) (g t) s e
      (by positivity) (by linarith) he {'(by norm_num)' if q==1 else 'hu0'}
      {hi} {hdec} (hgb ht') (hraw t ht).1 (hraw t ht).2
    dsimp only [F,g']
    simp only [{spatial}_agrees {args} _ t ht',clip_identity 0 1 t ht']
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
'''
s+='\nend Hurst\n';Path('.scratch/ActualMomentRisk.lean').write_text(s)
