from pathlib import Path
import json,re,hashlib
mods='OracleScaleL1 OracleScaleBias OracleScaleDistribution ActualScaleIntegrability ScaledMomentLimit FirstScaleNegligible FirstUnknownConditionalBias SecondUnknownConditionalBias FirstUnknownFineBias ActualUnknownConditionalLimits FirstUnknownScaleTests FirstUnknownAllScaleBias'.split()
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='Written proof21 fills unknown-scale fine limits in explicit regimes. Actual q1 expected leading bias proved with no remaining statistical input, including any unknown nonzero common scale. Actual q2 expected bias is conditional on improved scale L1 error. Actual q1/q2 distribution transfer requires scale negligibility and the known-scale reference limit. Conditional mainline phase remains in progress; finite-polynomial CLT/variance, long-memory and all finite loss moment chains still need completion before the delayed input proofs.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['21'],remaining=remaining))
assert len(ns)==17,len(ns)
j['date']='2026-09-09';j['latest_batch']=27;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['phase']='Complete written proofs first, then explicit-premise Lean mainline, then discharge delayed inputs; 21 written proof files.'
j['batches']=[x for x in j['batches'] if x['batch']!=27]+[dict(batch=27,new_mathematical_declarations=len(ns),declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
assert count==1082,count
conditional={
 'date':'2026-09-09','workflow':'written -> conditional Lean -> discharge inputs',
 'written_status':'Proof21 completes explicitly stated unknown-scale fine-limit regimes; backlog unchanged.',
 'conditional_mainline_complete':False,'external_input_stage_started':False,
 'note':'These declarations are kernel-checked implications, not unconditional paper theorems. Axiom audit alone does not discharge hypotheses.',
 'results':[
  {'declaration':'Hurst.hurstHolder_q1_unknown_bias_of_scale_L1','status':'input_discharged','inputs':['normalized actual scale L1 error tends to zero'],'discharged_by':['Hurst.hurstHolder_q1_scale_L1_negligible'],'closed_theorem':'Hurst.hurstHolder_q1_unknown_scale_expected_bias_leading','scope':'integer p>=1, C^p, fixed interior t, literal optimal bandwidth, global H upper bound<3/4, any unknown nonzero scale'},
  {'declaration':'Hurst.hurstHolder_q2_unknown_bias_of_scale_L1','status':'conditional','inputs':['INT-SCALE: E|actual q2 log-scale estimator|/(log n * delta^p) -> 0 in the unit-scale experiment'],'written_proof':'direct_proofs/21_unknown_scale_fine_limits.md, sections 2 and 4','scope':'integer p>=2, C^p, fixed interior t, literal optimal bandwidth, 0<a<=H<=b<u<1, pilot clipped to [a/2,u]'},
  {'declaration':'Hurst.hurstHolder_q1_unknown_distribution_of_inputs','status':'conditional','inputs':['normalized actual scale L1 error tends to zero at A_n','known-scale actual estimator has the specified distribution limit'],'upstream':['INT-CLT','INT-VAR'],'scope':'actual q1 short-memory class; unit-scale experiment; arbitrary nonnegative eventual A_n subject to stated smallness'},
  {'declaration':'Hurst.hurstHolder_q2_unknown_distribution_of_inputs','status':'conditional','inputs':['INT-SCALE: normalized actual scale L1 error tends to zero at A_n','known-scale actual estimator has the specified distribution limit'],'upstream':['INT-CLT','INT-VAR'],'scope':'actual q2 class with interior pilot clipping; unit-scale experiment'}
 ],
 'not_yet_closed_conditionally':['Actual log-statistic CLT from finite-polynomial CLT and variance inputs','Critical and long-memory full statistical chains','All finite s>2 risk/minimax from EXT-MOM','Unknown-scale remaining regime and bandwidth instantiations'],
 'input_registry':'verification/dependency_plan.md'
}
Path('verification/conditional_results.json').write_text(json.dumps(conditional,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['4.3','3.4','3.5']:
 if key not in u:continue
 e=u[key]
 e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_q1_scale_L1_negligible','hurstHolder_q1_unknown_scale_expected_bias_leading','hurstHolder_q2_unknown_bias_of_scale_L1','hurstHolder_q1_unknown_distribution_of_inputs','hurstHolder_q2_unknown_distribution_of_inputs']))
 e['repair_status']=e.get('repair_status','')+' 第二十七阶段的文件21补出未知尺度精细极限的明确版本。Lean已无额外待证明输入地完成q=1、整数p、C^p、最优带宽及任意未知非零尺度的实际期望偏差首项；q=2偏差和实际分布极限传递为显式前提版本，见conditional_results.json，不能登记为完整原结果。'
 e['remaining']='当前顺序为书面补证→条件Lean→消除输入。q=1所列未知尺度期望首项已完成；q=2尺度小量仍是前提，实际相关CLT/方差、临界长记忆、高阶矩/s>2及其余范围仍缺。条件主线尚未全部接通。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
p=Path('summary.md');s=p.read_text().replace('第二十六阶段新增11条数学定理，累计1065条数学定理及3条编号检查。','第二十七阶段新增17条数学声明，累计1082条数学声明及3条编号检查；这些内核通过的声明包含明确前提的条件定理，不能按数量视为完整原结果。')
anchor='| 最新完成部分 | 对应结果 | 尚缺 |'
s=s.replace(anchor,'按最新安排，执行顺序为**先补齐书面证明，再完成显式前提的Lean主线，最后证明并消除这些输入**。[文件21](direct_proofs/21_unknown_scale_fine_limits.md)补齐未知尺度精细极限的明确版本。条件主线仍在接通中，当前前提与已消除项见[条件登记](verification/conditional_results.json)及[依赖表](verification/dependency_plan.md)。\n\n'+anchor)
s=s.replace('|---|---|---|\n| 实际截断反演', '|---|---|---|\n| q=1未知非零常尺度的实际期望偏差首项 | 文件21、4.3的相关精细部分 | 固定内部点、整数p、C^p及精确最优带宽；不代表全部原4.3完成 |\n| q=2未知尺度偏差、q=1/q=2实际分布极限传递的条件性Lean链 | 文件21 | q=2尺度L¹小量和已知尺度参考分布极限仍是显式前提 |\n| 实际截断反演',1)
s=s.replace('下文保留书面修复结论及范围。20份书面证明保持原样；','最新新增书面补证和条件性Lean见[第二十七阶段](lean_batch27.md)。原3.5明确要求整数p，非整数普遍首项不是该原定理的欠账。\n\n下文保留书面修复结论及范围。此前20份书面证明保持原样，另新增文件21；')
p.write_text(s)
p=Path('mainline_status.md');s=p.read_text().replace('范围沿用已有20份书面修复中的一维q=1/2和所列参数条件，backlog保持不变。','范围沿用一维q=1/2和所列参数条件，新增文件21补齐未知尺度精细结论；backlog保持不变。按最新安排，先书面补证，再完成显式前提的Lean主线，最后证明这些输入。条件主线仍未全部完成；前提单独登记于[条件表](verification/conditional_results.json)。')
s=s.replace('| 短/临界/长记忆极限 |','| 未知尺度精细期望偏差 | q=1所列范围已完成；q=2为条件版本 | FirstUnknownAllScaleBias：任意未知非零常尺度、整数p、C^p、内部点和精确最优带宽；SecondUnknownConditionalBias还需实际尺度L¹小量 |\n| 未知尺度分布极限传递 | 实际q=1/q=2条件版本已完成 | ActualUnknownConditionalLimits明确要求参考估计器的分布极限和尺度小量；输入尚未全部证明 |\n| 短/临界/长记忆极限 |').replace('最新阶段说明见[第二十六阶段](lean_batch26.md)','最新阶段说明见[第二十七阶段](lean_batch27.md)')
p.write_text(s)
for name in ['README.md','lean_roadmap.md','lean_reuse.md']:
 p=Path(name);p.write_text(p.read_text()+'\n[第二十七阶段](lean_batch27.md)按新顺序补出文件21并建立显式前提的Lean链；已消除q=1未知尺度期望首项的统计输入，q=2及分布传递仍见[条件登记](verification/conditional_results.json)。外部文献引理和内部待形式化引理分别列在[依赖表](verification/dependency_plan.md)。\n')
p=Path('direct_proofs/README.md');s=p.read_text();s=s.replace('## 最新：所有有限Lˢ与p=1端点已书面补齐','## 最新：未知尺度精细极限的书面补齐\n\n[文件21](21_unknown_scale_fine_limits.md)利用实际均值抵消、带权空间平均和二阶Taylor余项，证明更强的尺度L¹误差界，再给出短记忆最优带宽下未知尺度偏差首项/CLT，以及临界和长记忆的一组明确欠平滑带宽版本。新增关键尺度小量步骤只需二阶矩。当前共21份书面文件；此前20份保持原样。条件性Lean与已消除输入单独见[登记](../verification/conditional_results.json)。\n\n## 此前：所有有限Lˢ与p=1端点已书面补齐',1);p.write_text(s)
p=Path('verification/lean_reuse_inventory.json');j=json.loads(p.read_text());j['unknown_scale_L1_bridge']=dict(source='Existing project contraction, q1 sharper scale risk and mathlib second-moment inequalities; no new external theorem assumed for the closed q1 bias',modules=['Hurst.'+m for m in mods],completed=remaining,conditional_registry='verification/conditional_results.json');p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
print('batch27',len(ns),'total mathematical declarations',count)
