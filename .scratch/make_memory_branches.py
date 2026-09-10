from pathlib import Path
# Preserve the exact primitive support hypotheses; fix the normalization and limiting law.
src=Path('Hurst/ActualMemoryMainline.lean').read_text()
start=src.index('theorem hurstHolder_q1_conditional_memory_mainline')
end=src.index(' := by',start)
sig=src[start:end]
out='''import Hurst.ActualMemoryMainline
import Hurst.EquivalentKernel

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst

def firstCriticalNormalization (n : ℕ) (δ : ℝ) : ℝ := Real.sqrt ((n:ℝ)*δ/Real.log ((n:ℝ)*δ))
def firstLongNormalization (h : ℝ) (n : ℕ) (δ : ℝ) : ℝ := ((n:ℝ)*δ)^(2-2*h)
def firstCriticalVariance (r : ℕ) : ℝ := (9/16)*(∫ z in Icc (-1:ℝ) 1,(equivalentKernel r z)^2)
'''
for branch in ['critical','long']:
 t=sig.replace('conditional_memory_mainline','conditional_'+branch+'_mainline')
 t=t.replace('(δ₁ δ₂ A R : ℕ → ℝ)', '(δ₁ δ₂ R : ℕ → ℝ)')
 t=t.replace('(hA : ∀ᶠ n in atTop,0≤A n)', '(hcrit : f t=3/4)' if branch=='critical' else '(hlong : 3/4<f t) (hδ : ∀ᶠ n in atTop,0≤δ₂ n)')
 if branch=='critical':
  t=t.replace("{Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Z : Ω' → ℝ) (β : ℝ)", '')
  t=t.replace(' P\'',' (gaussianReal 0 1)').replace('atTop Z','atTop (fun z : ℝ => Real.sqrt (firstCriticalVariance r)*z)')
  t=t.replace('-Z z-β','-(Real.sqrt (firstCriticalVariance r)*z)')
  norm='firstCriticalNormalization n (δ₂ n)'
 else:
  t=t.replace('(Z : Ω\' → ℝ) (β : ℝ)', '(Q : Ω\' → ℝ)')
  t=t.replace('atTop Z','atTop Q').replace('-Z z-β','-Q z')
  norm='firstLongNormalization (f t) n (δ₂ n)'
 t=t.replace('A n','('+norm+')').replace('𝓝 β','𝓝 0')
 t=t.replace('fun n =>','fun (n : ℕ) =>').replace('fun n x =>','fun (n : ℕ) x =>')
 out+='\n'+t+' := by\n'
 if branch=='long':out+='''  have hA : ∀ᶠ n in atTop,0≤firstLongNormalization (f t) n (δ₂ n) := by
    filter_upwards [hδ] with n hn
    exact Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) hn) _
'''
 hA='(Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _))' if branch=='critical' else 'hA'
 limit="(gaussianReal 0 1) (fun z : ℝ => Real.sqrt (firstCriticalVariance r)*z)" if branch=='critical' else "P' Q"
 out+=f'''  have hh := hurstHolder_q1_conditional_memory_mainline p a b M r hp ha hb hab hM f hf hF t ht
    δ₁ δ₂ (fun (n : ℕ) => {norm}) R m {hA} {limit} 0 hrows htail hquad hmean hQ hscale
  simpa only [sub_zero] using hh
'''
out+='\nend Hurst\n';Path('.scratch/ActualMemoryBranches.lean').write_text(out)
