from pathlib import Path
import json,re,hashlib
mods=['BackfitTransfer','ScaleBandwidth','ScaleMeasurability','OptimalScaleRisk','UnknownEstimator','UnitUnknownMSE','UnknownInvariance','UnknownDecision','UnknownMSE','UnknownLpRisk','UnknownExperiment','UnknownMinimaxUpper','UnknownMatchedMinimax']
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='q=2 unknown scale final H and matching squared Ls minimax complete for p>=2, 1<=s<=2 and fixed range spanning 1/2. q=1 unknown scale, all higher moments, and distributional limits remain.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['17','18','19'],remaining=remaining))
j['date']='2026-09-09';j['latest_batch']=21;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=21]+[dict(batch=21,new_mathematical_declarations=len(ns),declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['4.2','4.3']:
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_q2_unknown_Lp_risk','unknownScale_q2_minimax_matched']))
 e['repair_status']=e.get('repair_status','')+' 第二十一阶段补齐q=2实际未知尺度H回代、全域1≤s≤2平方Ls风险及未知σ作为干扰参数的匹配minimax；同一个可测决策核不依赖真实σ。'
 e['remaining']='q=2、p≥2、固定紧值域、1≤s≤2的修正版未知尺度风险与minimax已完成；q=1未知尺度、高阶矩、精细偏差和极限分布仍需完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
Path('lean_batch21.md').write_text(f'''# 第二十一阶段：实际q=2未知尺度H回代及minimax闭合

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。主线尚未完成，原编号结果仍为2/27完整。

`q2UnknownLocalEstimator`直接使用原n个观测的二阶差分对数统计量，减去实际估计的log σ²，再作截断反演。`BackfitTransfer`逐样本比较回代与已知尺度估计，使用相关误差平方和界，不需要数据独立或样本拆分。

已核验实际估计器的联合可测性、空间连续性、Ls决策可测性，以及精确的几乎处处尺度不变性。选取δ=(n log²n)^(-1/(2p+1))和粗平均点数m=ceil(1/δ)，得到全[0,1]点态MSE及全(0,1)平方Ls风险≤C(n log²n)^(-2p/(2p+1))，其中p≥2、固定0<a≤H≤b<1、1≤s≤2、任意未知共同σ≠0。常数及样本阈值在H和σ量词之前。

`UnknownHurstParameter`把σ正式纳入干扰参数。`unknownScale_q2_minimax_upper`构造同一个不依赖σ的可测决策核；不能用“每个已知σ各选一个估计器”替代这一点。`knownScale_minimax_le_unknown`通过固定σ子模型接入已证下界。最终`unknownScale_q2_minimax_matched`在固定0<a<1/2<b<1、M>0的同一函数类上，给出上述平方Ls minimax的匹配上下界；下界允许任意随机化可测估计器及无限损失。

实现沿用第二十阶段的全域粗平均与固定类[a,b]截断，已说明与原文的实现差别。这个范围的未知尺度最优性现已闭合，但q=1未知尺度、s>2、高阶矩、精细偏差和各种记忆区间的极限分布仍未完成。没有将原4.2/4.3的全部命题改标完成。
''')
p=Path('mainline_status.md');s=p.read_text().replace('q=2 pilot与对数尺度MSE已完成，回代整链未完成','q=2、p≥2、1≤s≤2未知尺度风险及minimax已完成').replace('UnknownScaleRisk：全域粗平均及固定类截断的实际对数尺度MSE；q=1未知尺度、最终H回代仍缺','UnknownMatchedMinimax：实际H回代、全域平方Ls风险及同一不依赖σ的决策核；q=1未知尺度、高阶矩及极限仍缺').replace('最新阶段说明见[第二十阶段](lean_batch20.md)','最新阶段说明见[第二十一阶段](lean_batch21.md)');p.write_text(s)
p=Path('summary.md');s=p.read_text();s=re.sub(r'第二十阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第二十一阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s).replace('最终H回代、q=1未知尺度、s>2和极限分布仍未完成。','第二十一阶段已补齐q=2未知尺度最终H回代、全域1≤s≤2平方Ls风险与匹配minimax；q=1未知尺度、s>2和极限分布仍未完成。').replace('详见[第二十阶段]','详见[第二十一阶段](lean_batch21.md)、[第二十阶段]');p.write_text(s)
for name in ['README.md','lean_roadmap.md']:
 p=Path(name);p.write_text(p.read_text()+'\n[第二十一阶段](lean_batch21.md)补齐q=2实际未知尺度H回代和1≤s≤2平方Ls minimax；一个可测决策核统一处理所有σ≠0。主线仍缺q=1未知尺度、高阶矩及极限分布。\n')
p=Path('proof_notes/unknown_scale_lean_progress.md');s=p.read_text().replace('未知尺度H回代仍在推进','未知尺度H回代已由第二十一阶段闭合（p≥2、1≤s≤2）').replace('后续仍须完成回代估计器、可测性及全域Ls/minimax封装。','第二十一阶段已完成回代估计器、可测性及全域1≤s≤2的Ls/minimax封装。未知σ纳入同一参数空间，估计器不依赖σ；匹配下界要求固定值域跨越1/2。后续继续q=1、高阶矩和极限。');p.write_text(s)
print(len(ns),count)
