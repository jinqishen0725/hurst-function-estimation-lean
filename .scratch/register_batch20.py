from pathlib import Path
import json,re,hashlib
mods=['ClippedSmooth','FiniteAverageMSE','MergedLogVariance','ClippedSmoothRisk','CommonLogBias','LinearScale','AverageAlgebra','TransformMSE','ScaleAverage','ActualScaleVariance','ActualScaleBias','NonlinearScaleRisk','ScaleEquivariance','ScaleRiskTransfer','UnitScaleRisk','UnknownScaleRisk']
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['16','17','18','19'],remaining='Actual q=2 unknown common log-scale MSE complete for full-grid average and fixed-class clipping. Back-substitution, q=1 unknown scale, all high moments and distributional limits remain.'))
j['date']='2026-09-09';j['latest_batch']=20;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=20]+[dict(batch=20,new_mathematical_declarations=len(ns),declarations=ns,description='Actual q=2 full-grid averaged log-scale estimator, fixed-class clipping, linear bias and log-squared/n variance, nonlinear MSE without independence, exact scale equivariance, complete unknown nonzero common scale MSE with class-uniform constants.')]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['4.2','4.3','S.5.1','S.5.2']:
 if key not in u:continue
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_q2_linearScale_variance','hurstHolder_q2_nonlinearScale_mse','hurstHolder_q2_logScale_mse_unknown_scale']))
 e['repair_status']=e.get('repair_status','')+' 第二十阶段已证明q=2实际全域粗网格平均的对数尺度估计MSE，任意未知共同σ≠0，固定类[a,b]截断；线性方差O(log²n/n)、非线性项MSE、精确尺度等变性和全部统一常数均已核验。实现选择与原文不同，详见阶段说明。'
 e['remaining']='已完成q=2全域粗网格平均、固定类区间截断版本的实际未知尺度MSE；原文全部范围、精细偏差/极限分布、q=1未知尺度以及最终H回代风险仍需完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
Path('lean_batch20.md').write_text(f'''# 第二十阶段：完整实际q=2未知对数尺度MSE

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27，主线未完成。

范围：原Hölder类p≥2、固定0<a≤H≤b<1、任意共同σ≠0。pilot使用两尺度相同的n−4个有效基点；尺度估计使用全域粗中点平均，非线性log项的pilot输入截断到已知固定类区间[a,b]。这两个实现选择与原文的固定内部区域、原截断区间有差别，已明确记录；不声称估计器逐样本等同。

`MergedLogVariance`从真实合并权重推出各尺度平均对数统计量的O(1/n)方差。`ActualScaleVariance`对实际线性组合证明O(log²n/n)，所有相关项通过方差不等式保留。

`CommonLogBias`验证原函数及非线性校准项的高阶平滑偏差。`ActualScaleBias`将它与真实pilot均值结合后平均。`NonlinearScaleRisk`以光滑复合和投影误差控制非线性项，有限平均的平方矩界没有使用独立性。

`ScaleEquivariance`证明sHat(σX)=sHat(X)+log σ²几乎处处，以及任意实损失的精确积分转换。最终`hurstHolder_q2_logScale_mse_unknown_scale`证明：

E(sHat−log σ²)² ≤ C[(log n·δ^p)²+(log n·e_n)²+log²n/n+1/(nδ)]，

e_n=gridCovarianceError(1/2,1,n)=O(log n/n)。条件为n足够大、log n≥1、0<δ≤1/2、nδ≥N₀及粗网格mδ≥1。C,N,N₀在函数、σ、m及δ量词之前。

这是实际尺度估计的组合MSE，尚未将最终H回代风险、未知尺度Ls/minimax以及q=1对应版本改标完成。原4.2的全部范围与精细偏差/极限结论也没有被这个修正版替代。
''')
p=Path('summary.md');s=p.read_text();s=re.sub(r'第十九阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第二十阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s).replace('日期：2026-09-08。','日期：2026-09-09。').replace('最终尺度估计及回代、s>2和极限分布仍未完成。','第二十阶段已完成q=2全域粗网格平均、固定类区间截断版本的实际未知对数尺度MSE。最终H回代、q=1未知尺度、s>2和极限分布仍未完成。').replace('详见[第十九阶段]','详见[第二十阶段](lean_batch20.md)、[第十九阶段]');p.write_text(s)
p=Path('mainline_status.md');s=p.read_text().replace('q=2 pilot实际MSE已完成，整链未完成','q=2 pilot与对数尺度MSE已完成，回代整链未完成').replace('q=1 pilot、尺度估计随机风险、截断与回代仍缺','UnknownScaleRisk：全域粗平均及固定类截断的实际对数尺度MSE；q=1未知尺度、最终H回代仍缺').replace('最新阶段说明见[第十九阶段](lean_batch19.md)','最新阶段说明见[第二十阶段](lean_batch20.md)');p.write_text(s)
p=Path('README.md');p.write_text(p.read_text()+'\n[第二十阶段](lean_batch20.md)完成q=2实际未知对数尺度MSE；全域粗平均及固定类区间截断的实现选择已注明。最终H回代风险继续推进。\n')
p=Path('lean_roadmap.md');p.write_text(p.read_text()+'\n## 第二十阶段\n\nq=2实际未知对数尺度MSE已完成；下一步是最优带宽下的H回代、全域Ls和minimax封装。q=1未知尺度、高阶矩及极限仍缺。见[阶段说明](lean_batch20.md)。\n')
p=Path('proof_notes/unknown_scale_lean_progress.md');s=p.read_text().replace('最终组合MSE及未知尺度回代尚在检查','最终组合MSE已通过第二十阶段检查，未知尺度H回代仍在推进').replace('目标组合界（还应以最终通过的Lean定理为准）为','已证明的组合界为');p.write_text(s)
print(len(ns),count)
