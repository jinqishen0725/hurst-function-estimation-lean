from pathlib import Path
import json,re,hashlib
mods='InverseL1Limit ScaledL1Probability FirstEstimatorLinearization SecondEstimatorLinearization InverseProbabilityLimit ActualEstimatorProbability KnownScaleLinearization TriangularL1Transfer'.split()
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='Actual q1/q2 optimal-bandwidth inverse remainder tends to zero in normalized L1 and probability under the batch25 interior C^p assumptions; arbitrary known nonzero scale has actual L1 conclusion. Varying-space L1 weak-limit transfer proved using mathlib bounded Lipschitz criterion, conditional on an existing input distribution limit. Actual correlated-array CLT and variance limits, high moments/s>2, critical/long-memory and unknown-scale fine limits remain.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['11','13'],remaining=remaining))
assert len(ns)==11,len(ns)
j['date']='2026-09-09';j['latest_batch']=26;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=26]+[dict(batch=26,new_mathematical_declarations=len(ns),declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
assert count==1065,count
p=Path('scripts/repair_updates.json');j=json.loads(p.read_text())
for key in ['3.3','3.4','3.5','8.5']:
 e=j[key]
 e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_q1_L1_linearization','hurstHolder_q2_L1_linearization','hurstHolder_q1_linearization_in_probability','hurstHolder_q2_linearization_in_probability','hurstHolder_q1_known_scale_L1_linearization','hurstHolder_q2_known_scale_L1_linearization','triangular_L1_distribution_transfer']))
 e['repair_status']=e.get('repair_status','')+' 第二十六阶段补齐上述内部C^p和最优带宽范围的真实估计器随机线性化：归一化L¹余项及尾概率趋零，任意已知非零尺度的L¹结论已接通；另证变化样本空间的条件分布极限传递。后者要求输入统计量已收敛，不证明实际CLT。'
 e['remaining']='随机反演余项的上述L¹/依概率范围已完成，实际相关对数统计量的CLT尚未证明。'+e['remaining']
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
p=Path('summary.md');s=p.read_text().replace('第二十五阶段新增54条数学定理，累计1054条数学定理及3条编号检查。','第二十六阶段新增11条数学定理，累计1065条数学定理及3条编号检查。')
s=s.replace('| 最新完成部分 | 对应结果 | 尚缺 |\n|---|---|---|','| 最新完成部分 | 对应结果 | 尚缺 |\n|---|---|---|\n| 实际截断反演的归一化L¹余项和尾概率趋零；变化样本空间的分布极限传递 | 3.3/3.4/3.5、文件11/13 | 沿用内部C^p/最优带宽条件；输入相关统计量的CLT仍缺，不能把条件传递定理当成CLT |')
s=s.replace('s>2、高阶矩、有限多项式CLT、实际方差与分布极限、未知尺度精细偏差及更广带宽/非整数范围仍未完成。详见','第二十六阶段补齐同范围的随机反演余项L¹与依概率收敛，及基于mathlib有界Lipschitz判据的变化样本空间分布极限传递。该传递定理以输入分布收敛为前提，实际CLT仍未证明。s>2、高阶矩、有限多项式CLT、实际方差与分布极限、未知尺度精细偏差及更广带宽/非整数范围仍未完成。详见[第二十六阶段](lean_batch26.md)、')
p.write_text(s)
p=Path('mainline_status.md');s=p.read_text().replace('| 短/临界/长记忆极限 |','| 实际截断反演随机线性化 | 已完成第二十五阶段所列范围 | ActualEstimatorProbability：归一化余项依概率趋零；KnownScaleLinearization：已知非零尺度L¹余项；TriangularL1Transfer：变化样本空间的条件弱极限传递，不是实际CLT |\n| 短/临界/长记忆极限 |').replace('最新阶段说明见[第二十五阶段](lean_batch25.md)','最新阶段说明见[第二十六阶段](lean_batch26.md)');p.write_text(s)
for name in ['README.md','lean_roadmap.md','lean_reuse.md']:
 p=Path(name);p.write_text(p.read_text()+'\n[第二十六阶段](lean_batch26.md)补齐实际已知尺度估计器的随机线性化和变化样本空间的L¹弱极限传递。复用本地mathlib有界Lipschitz判据；其现有独立同分布CLT不能直接用于本文相关阵列，实际CLT仍待证。\n')
p=Path('verification/lean_reuse_inventory.json');j=json.loads(p.read_text());j['triangular_L1_transfer']=dict(source='Local mathlib v4.31.0 ConvergenceInDistribution bounded Lipschitz criterion and Bochner Markov inequality',modules=['Hurst.'+m for m in mods],completed=remaining,restriction='The available mathlib CentralLimitTheorem requires iid input and is not used as a correlated-array CLT. The transfer theorem has explicit input convergence hypothesis.');p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
print('batch26',len(ns),'total mathematical',count)
