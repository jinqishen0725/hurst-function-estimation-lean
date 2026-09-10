from pathlib import Path
src=Path('Hurst/ActualShortMainline.lean').read_text()
out='''import Hurst.ActualShortMainline
import Hurst.AllScaleDistributionTransfer
import Hurst.KnownScaleDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst
'''
for q in [1,2]:
 start=src.index(f'theorem hurstHolder_q{q}_conditional_short_mainline');end=src.index(' := by',start)
 sig=src[start:end];cut=sig.rindex(' :\n');head=sig[:cut];result=sig[cut:]
 head=head.replace('conditional_short_mainline','conditional_all_scale_short_mainline').replace('(V : ℝ)', '(σ : ℝ) (hσ : σ≠0) (V : ℝ)')
 result=result.replace('featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))','featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)')
 pos=result.index(' ∧');part=result[:pos].replace(' t x-f t',' t (σ⁻¹ • x)-f t');result=part+result[pos:]
 out+='\n'+head+result+' := by\n'
 extras='u hr hu hbu' if q==2 else ''
 out+=f'''  have hh := hurstHolder_q{q}_conditional_short_mainline a b M r {extras} ha hb hab hM f hf hF hfc t ht {'htu' if q==2 else ''} V Vk hV hpoly {'hscale' if q==2 else ''}
'''
 if q==2:out+='  have hu0 : 0≤u := by linarith\n'
 coeff='gridDifferenceCoefficients n' if q==1 else 'gridSecondCoefficients n'
 out+=f'''  refine ⟨?_,?_⟩
  · apply featureGaussian_known_scale_distribution (gaussianReal 0 1)
      (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n)) _ _ _ σ hσ hh.1
    intro n
    exact normalized_q{q}_inverse_measurable n {'u hu0 hu' if q==2 else ''}
      (gaussianLogStatistic (localPolynomialWeights r n {q} (optimalLocalBandwidth ((r:ℝ)+1) n) t) ({coeff}))
      (by unfold gaussianLogStatistic; fun_prop) _ (f t)
  · exact hurstHolder_q{q}_unknown_scale_distribution_transfer ((r:ℝ)+1) a b M r {'(a/2) u hu0 hu' if q==2 else ''}
      ({'by exact_mod_cast (show 2≤r+1 by omega)' if q==2 else 'by linarith [Nat.cast_nonneg (α:=ℝ) r]'}) ha ({'hb' if q==2 else 'by linarith'}) hab hM
      f hf hF t ⟨ht.1.le,ht.2.le⟩
      (fun n : ℕ => Real.sqrt ((n:ℝ)*optimalLocalBandwidth ((r:ℝ)+1) n)) σ hσ (gaussianReal 0 1) _ hh.2
'''
out+='\nend Hurst\n';Path('.scratch/AllScaleShortMainline.lean').write_text(out)
