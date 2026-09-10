from pathlib import Path
out='''import Hurst.ActualPilotCLT
import Hurst.ActualPilotMemory
import Hurst.PilotScaleDistribution

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Hurst
'''
for q,kind in [(1,'CLT'),(2,'CLT'),(1,'memory_limit')]:
 path='Hurst/ActualPilotCLT.lean' if kind=='CLT' else 'Hurst/ActualPilotMemory.lean'
 src=Path(path).read_text();start=src.index(f'theorem hurstHolder_q{q}_conditional_pilot_{kind}');end=src.index(' := by',start);sig=src[start:end];cut=sig.rindex(' :\n')
 head=sig[:cut].replace(f'conditional_pilot_{kind}',f'conditional_all_scale_pilot_{kind}').replace('(t : ℝ)', '(σ : ℝ) (hσ : σ≠0) (t : ℝ)')
 res=sig[cut:].replace('featureGaussian (gridObservationFeatures n (midpointSampleHurst f hf.1 n))','featureGaussian (fun i => σ • gridObservationFeatures n (midpointSampleHurst f hf.1 n) i)')
 out+='\n'+head+res+' := by\n'
 args='δ A R C V Vk hV hrow hweight hpoly' if kind=='CLT' else "δ A P' Z htail hquad"
 out+=f'''  have hunit := hurstHolder_q{q}_conditional_pilot_{kind} p a b M r hp ha hb hab hM f hf hF t {args}
  obtain ⟨C₁,_,h₁⟩ := hurstHolder_common_{'first_stride' if q==1 else 'stride'}_log_mean p a b M 1 {2*q} hp ha hb hab hM (by norm_num) (by norm_num)
  obtain ⟨C₂,_,h₂⟩ := hurstHolder_common_{'first_stride' if q==1 else 'stride'}_log_mean p a b M 2 {2*q} hp ha hb hab hM (by norm_num) (by norm_num)
  exact featureGaussian_pilot_scale_distribution {'(gaussianReal 0 1)' if kind=='CLT' else "P'"}
    (fun n => Fin (n-{2*q})) (fun n => gridObservationFeatures n (midpointSampleHurst f hf.1 n))
    (fun n => localPolynomialWeights r n {2*q} (δ n) t)
    (fun n => {'commonFirstStrideCoefficients' if q==1 else 'commonStrideCoefficients'} n 1 {2*q} (by norm_num))
    (fun n => {'commonFirstStrideCoefficients' if q==1 else 'commonStrideCoefficients'} n 2 {2*q} (by norm_num)) A _ σ hσ
    (h₁.mono (fun n hn i => (hn f hf hF i).1)) (h₂.mono (fun n hn i => (hn f hf hF i).1)) hunit
'''
out+='\nend Hurst\n';Path('.scratch/AllScalePilotMainline.lean').write_text(out)
