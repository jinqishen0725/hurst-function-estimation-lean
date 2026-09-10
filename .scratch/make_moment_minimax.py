from pathlib import Path
s='''import Hurst.ActualMomentRisk
import Hurst.FirstUnknownMinimax
import Hurst.UnknownMinimaxUpper

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Hurst
'''
# The two model contracts describe pre-inversion log statistics, not estimator risk.
for q in [1,2]:
 coeff='gridDifferenceCoefficients n' if q==1 else 'gridSecondCoefficients n'
 raw=f'gaussianLogStatistic (localPolynomialWeights (Nat.ceil p-1) n {q} (optimalLocalBandwidth p n) t) ({coeff}) x-q{q}LogScaleEstimator '+('a b ' if q==2 else '')+'(Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) x'
 cal='calibrationOne' if q==1 else 'calibrationTwo'
 s+=f'''
def Q{q}RawMomentBound (p a b M s : ℝ) : Prop :=
  ∃ C>0,∃ N : ℕ,4≤N ∧ ∀ f : ℝ → ℝ,∀ hf : f∈hurstHolderClass p M,
    MapsTo f (Ioo (0:ℝ) 1) (Icc a b) →
    ∃ g : ℝ → ℝ,Continuous g ∧ EqOn f g (Ioo (0:ℝ) 1) ∧ MapsTo g (Icc (0:ℝ) 1) (Icc a b) ∧
    ∀ σ : ℝ,σ≠0 → ∀ n : ℕ,N≤n → ∀ t∈Ioo (0:ℝ) 1,
      MemLp (fun x => {raw}) (ENNReal.ofReal s)
        (scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val)) ∧
      (∫ x,|({raw})-{cal} (Real.log n) gaussianLogSquareMean (g t)|^s
        ∂scaledHarmonizableGaussian σ (midpointSampleHurst f hf.1 n) (fun i => grid n i.val))≤
        (2*Real.log n*(C*lowerBoundRate p n))^s
'''
base=Path('Hurst/MinimaxUpperTransfer.lean').read_text();z=base[base.index('theorem continuous_decision_squared_risk'):base.index('\nend Hurst')]
z=z.replace('continuous_decision_squared_risk','continuous_decision_squared_risk_allfinite').replace(' (hs2 : s.val ≤ 2)','')
s+='\n'+z+'\n'
for q in [1,2]:
 path='Hurst/FirstUnknownMinimax.lean' if q==1 else 'Hurst/UnknownMinimaxUpper.lean'
 b=Path(path).read_text();b=b[b.index(f'theorem unknownScale_q{q}_minimax_upper'):b.index('\nend Hurst')]
 b=b.replace(f'unknownScale_q{q}_minimax_upper',f'unknownScale_q{q}_minimax_upper_of_raw_moments',1)
 b=b.replace('(hM : 0 ≤ M) :','(hM : 0 ≤ M) (s : {s : ℝ // 1≤s}) (hs : 2≤s.val)\n    (hraw : Q'+str(q)+'RawMomentBound p a b M s.val) :',1)
 b=b.replace('∃ C > 0, ∃ N : ℕ, '+('2' if q==1 else '4')+' ≤ N ∧\n    ∀ s : {s : ℝ // 1 ≤ s}, s.val ≤ 2 → ∀ n : ℕ, N ≤ n →','∃ C > 0, ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n →')
 b=b.replace(f'obtain ⟨C, hC, N, hN, hrisk⟩ := hurstHolder_q{q}_unknown_Lp_risk p a b M hp ha hb hab hM','obtain ⟨C, hC, N, hN, hrisk⟩ := hraw')
 b=b.replace('refine ⟨C, hC, max N K,','refine ⟨C^2, sq_pos_of_pos hC, max N K,')
 b=b.replace('intro s hs n hn','intro n hn')
 b=b.replace('continuous_decision_squared_risk\n','continuous_decision_squared_risk_allfinite\n').replace('s hs hp1','s hp1')
 if q==1:b=b.replace('F hFc hFm hFb hgb','F hFc hFm hFb (fun t ht => ⟨ha.le.trans (hgb ht).1,(hgb ht).2.trans hb.le.trans (by norm_num : (3/4:ℝ)≤1)⟩)')
 # Use literal range proof avoiding trans precedence.
 if q==1:b=b.replace('(hgb ht).2.trans hb.le.trans (by norm_num : (3/4:ℝ)≤1)','(hgb ht).2.trans (by linarith : b≤1)')
 old='  exact ENNReal.ofReal_le_ofReal (hgRisk σ hσ s.val ⟨s.property, hs⟩ n ((le_max_left N K).trans hn))'
 args=f'(Nat.ceil p-1) n (scaleAverageResolution p n) (optimalLocalBandwidth p n) hn1 '+('a b hb0 hb ' if q==2 else '')
 rangeproof='(fun t ht => ⟨ha.le.trans (hgb ht).1,(hgb ht).2.trans (by linarith : b≤1)⟩)' if q==1 else '(fun t ht => ⟨ha.le.trans (hgb ht).1,(hgb ht).2⟩)'
 new=f'''  have hrate : 0≤lowerBoundRate p n := by unfold lowerBoundRate; positivity
  have hh := q{q}_unknown_spatial_risk_of_raw_moments {args}
    (scaledHarmonizableGaussian σ (midpointSampleHurst H.val.value H.val.property.1 n) (fun i => grid n i.val))
    s.val (C*lowerBoundRate p n) hs (mul_nonneg hC.le hrate) g hg {rangeproof}
    hdet (hgRisk σ hσ n ((le_max_left N K).trans hn))
  apply ENNReal.ofReal_le_ofReal
  convert hh using 1 <;> first | rfl | ring'''
 assert old in b
 b=b.replace(old,new)
 s+='\n'+b+'\n'
s+='\nend Hurst\n';Path('.scratch/ConditionalMomentMinimax.lean').write_text(s)
