from pathlib import Path
import json,re,hashlib

mods='InteriorKernelMoments InteriorDesignLimit PointwiseTaylor LocalTaylorLeading LocalLeadingLimit EquivalentKernel CalibratedBiasLimit GaussianMeanApproximation ActualMeanResidual MeanLimitTransfer GridBiasRemainderLimit ActualMeanLeading OptimalBiasBandwidth OptimalMeanLeading ClippedLinearization ExpectedLinearization CalibrationLipschitz ExpectedInverseLimit BiasVarianceScale OptimalLogVariance SecondEstimatorBias FirstEstimatorBias OptimalNormalization InverseL1Linearization KnownScaleEstimatorBias'.split()
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='Known nonzero scale, fixed interior t, integer p=r+1 and C^p regularity: actual equivalent-kernel bias and optimal-bandwidth expected q1/q2 estimator bias complete, with strict interior clipping for q2. Pointwise and L1 inverse linearization use second moments only. Correlated-array CLT, actual variance limits, high moments/s>2, critical/long-memory limits, unknown-scale fine bias and broader bandwidth/noninteger fine-bias scopes remain.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['02','11','13'],remaining=remaining))
assert len(ns)==54,len(ns)
j['date']='2026-09-09';j['latest_batch']=25;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=25]+[dict(batch=25,new_mathematical_declarations=len(ns),declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
assert count==1054,count
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
risk='已知及未知共同非零常尺度、1≤s≤2的q=1,p≥1,b<3/4及q=2,p≥2,b<1全域平方Ls风险和匹配minimax已完成；匹配下界要求值域包含1/2邻域。'
fine='固定内部位置、整数p=r+1、额外C^p正则性及精确最优带宽下，已知非零尺度的实际q=1/q=2估计器期望偏差首项已完成；q=2要求真H(t)严格低于截断上界u<1。'
limits='有限多项式相关阵列CLT、实际方差极限、高阶矩及s>2风险、临界/长记忆极限、未知尺度精细偏差/分布及更广带宽和非整数精细偏差范围仍缺。'
u['3.1']['remaining']='本原定理含p=1及固定值域子类概率下界已完成。'+risk+'所有有限s>2的匹配上界尚待高阶矩形式化。'
u['3.2']['remaining']=risk+fine+limits
for key in ['3.3','3.4','8.5']:
 u[key]['remaining']='实际统一Hermite截断及测试函数控制已完成。'+fine+limits
u['3.5']['remaining']=fine+'真实Gaussian模型、实际局部权重、对数矩、均值和非线性截断反演已接通。'+limits
u['8.3']['remaining']='q=1、q=2实际全网格均值修正已完成，最优带宽下的内部C^p精细均值亦已接通。其他rho/记忆分支及原文更广范围仍需形式化。'
u['8.4']['remaining']='一维固定光滑正核的全域O(δ^p)偏差及复合正则性已完成；固定内部位置、整数p与C^p条件下，实际设计矩阵/逆矩阵极限、等价核积分与精确偏差首项已完成。一般维度/核及非整数精细偏差等原文剩余范围尚未完成。'
u['S.3.3']['remaining']=risk+'实际q=1短记忆和q=2行和、方差、最优带宽MSE及统一Hermite截断已完成。'+limits
for key in ['S.5.1','S.5.2']:
 u[key]['remaining']=risk+'未知尺度pilot、实际空间平均、尺度消去及最终H回代均已接通上述风险范围；未知尺度精细偏差/极限分布及原文其他范围仍缺。'
evidence={
 '8.4':['localDesignGram_tendsto','localDesignGram_inverse_tendsto','localPolynomialWeights_moment_tendsto','localPolynomial_bias_leading_tendsto','equivalentKernel_integral_moment'],
 '3.2':['hurstHolder_second_log_mean_leading_optimal','hurstHolder_stride_first_log_mean_leading_optimal'],
 '8.3':['hurstHolder_second_log_mean_leading','hurstHolder_stride_first_log_mean_leading'],
 '3.4':['hurstHolder_q1_expected_bias_leading','hurstHolder_q2_expected_bias_leading','boundedInverse_L1_linearization'],
 '3.5':['hurstHolder_q1_known_scale_expected_bias_leading','hurstHolder_q2_known_scale_expected_bias_leading','boundedInverse_expected_leading','optimalLocalBandwidth_fluctuation_balance'],
}
for key,names in evidence.items():
 u[key]['evidence_add']=list(dict.fromkeys(u[key].get('evidence_add',[])+names))
 u[key]['repair_status']=u[key].get('repair_status','')+' 第二十五阶段补齐内部C^p偏差首项及实际已知尺度估计器期望偏差；明确最优带宽与截断内部条件，不据此宣称CLT完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
p=Path('summary.md');s=p.read_text().replace('第二十四阶段新增37条数学定理，累计1000条数学定理及3条编号检查。','第二十五阶段新增54条数学定理，累计1054条数学定理及3条编号检查。')
s=s.replace('| 最新完成部分 | 对应结果 | 尚缺 |\n|---|---|---|','| 最新完成部分 | 对应结果 | 尚缺 |\n|---|---|---|\n| 实际等价核积分与内部C^p偏差首项 | 8.4、文件02 | 一般核/维度及非整数精细偏差范围 |\n| 最优带宽、已知非零尺度下实际q=1/q=2估计器期望偏差首项 | 3.4/3.5的偏差部分、文件11/13 | 要求整数p、C^p及严格内部截断；实际CLT和未知尺度精细偏差仍缺 |')
s=s.replace('s>2、多指标高阶矩界、精细偏差、有限多项式CLT和实际极限分布仍未完成。详见','第二十五阶段已完成固定内部位置、整数p=r+1且H额外为C^p时，精确最优带宽下已知非零尺度的实际估计器期望偏差首项；q=2要求H(t)<u<1。证明从实际等价核与均值/方差进入截断反演，只使用二阶矩。s>2、高阶矩、有限多项式CLT、实际方差与分布极限、未知尺度精细偏差及更广带宽/非整数范围仍未完成。详见[第二十五阶段](lean_batch25.md)、')
p.write_text(s)
p=Path('mainline_status.md');s=p.read_text().replace('首项积分极限仍缺','内部C^p整数阶的首项积分极限已由第二十五阶段补齐')
s=s.replace('| 短/临界/长记忆极限 |','| 实际估计器期望偏差首项 | 已完成所列已知尺度范围 | KnownScaleEstimatorBias：固定内部t、整数p=r+1、额外C^p、精确最优带宽；q=1要求b<3/4，q=2要求p≥2且H(t)<u<1；未知尺度与其他精细范围仍缺 |\n| 短/临界/长记忆极限 |')
s=s.replace('实际算子/混沌极限及精细偏差','实际方差与算子/混沌极限；未知尺度及其他范围精细偏差仍缺').replace('最新阶段说明见[第二十四阶段](lean_batch24.md)','最新阶段说明见[第二十五阶段](lean_batch25.md)');p.write_text(s)
for name in ['README.md','lean_roadmap.md','lean_reuse.md']:
 p=Path(name);p.write_text(p.read_text()+'\n[第二十五阶段](lean_batch25.md)从mathlib Taylor/矩阵连续性及已验证项目均值方差证明实际等价核和期望偏差首项；适用整数p、额外C^p、固定内部位置与精确最优带宽，q=2真H严格处于截断区间内部。截断反演余项仅需二阶矩。已知非零尺度已接通；CLT、高阶矩及未知尺度精细偏差仍缺。\n')
p=Path('verification/lean_reuse_inventory.json');j=json.loads(p.read_text());j['date']='2026-09-09';j['fine_bias_integration']=dict(source='Local mathlib v4.31.0 Taylor/Peano, matrix inverse continuity, Lipschitz and moment inequalities; independent clipping proof',modules=['Hurst.'+m for m in mods],completed=remaining.split(' Correlated-array')[0],remaining='Correlated-array'+remaining.split(' Correlated-array')[1]);p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
print('batch25',len(ns),'total mathematical',count)
