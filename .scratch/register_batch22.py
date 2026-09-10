from pathlib import Path
import json,re,hashlib
mods=sorted(p.stem for p in Path('Hurst').glob('*.lean') if p.stem.startswith(('First','CommonFirst','MergedFirst')))
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='q=1 short-memory unknown-scale pilot, actual two-stride covariance and means, final H and matching squared Ls minimax complete for p>=1 and 1<=s<=2. All higher moments and distributional limits remain.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['12','15','16','17','18','19'],remaining=remaining))
j['date']='2026-09-09';j['latest_batch']=22;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=22]+[dict(batch=22,new_mathematical_declarations=len(ns),declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['4.1','4.2','4.3']:
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_q1_pilot_mse_unknown_scale','hurstHolder_q1_optimal_scale_risk_unknown','hurstHolder_q1_unknown_Lp_risk','unknownScale_q1_minimax_matched']))
 e['repair_status']=e.get('repair_status','')+' 第二十二阶段补齐q=1短记忆、p≥1的真实两步长pilot、未知尺度平均和H回代；全域1≤s≤2平方Ls风险及未知σ的同类minimax匹配已完成。'
 e['remaining']='q=1短记忆和q=2在各自原光滑性范围的1≤s≤2修正版未知尺度风险与minimax已完成；s>2、高阶矩、精细偏差、其他记忆范围及极限分布仍需完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
Path('lean_batch22.md').write_text(f'''# 第二十二阶段：q=1未知尺度全域风险与minimax

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。主线未完成；原27个编号结果仍为2项完整。

范围是原Hölder类p≥1、固定0<a≤H≤b<3/4和任意未知共同σ≠0。包含p=1。每个固定正整数步长均从真实谱特征证明全域协方差扰动、非退化、相关平方行和和精细对数均值。两个pilot尺度使用原n个观测中的n−2个共同基点，保留真实相关。

`FirstPilotRisk`证明实际未知尺度pilot的MSE。`FirstScaleBias`证明采用同一合并权重时H主项逐点精确消去，无非线性修正；线性尺度方差为O(log²n/n)。`FirstScaleSharperRisk`得到尺度MSE/log²n≤C/n，`FirstScaleUnknownRisk`将最优速率界传递至任意未知σ。

`FirstUnknownEstimator`和`FirstUnknownDecision`验证最终回代估计器的联合可测性、空间连续性及Ls决策可测性。`FirstUnknownInvariance`证明实际尺度不变性。`FirstUnknownLpRisk`给出全(0,1)上1≤s≤2的平方Ls风险≤C(n log²n)^(-2p/(2p+1))。

`unknownScale_q1_minimax_matched`把同一个不依赖σ的决策核与固定σ子模型的下界接合。匹配范围要求0<a<1/2<b<3/4、M>0；下界对任意随机化可测估计器成立。上界单独不要求值域跨越1/2。

实现采用全域粗平均，具体直接证明见[说明](proof_notes/q1_unknown_scale.md)。至此q=1短记忆及q=2在1≤s≤2内的已知/未知尺度风险与minimax链均闭合。s>2、高阶矩、精细偏差和短/临界/长记忆极限仍在主线，未移入backlog、未改标完成。
''')
p=Path('mainline_status.md');s=p.read_text().replace('q=2、p≥2、1≤s≤2未知尺度风险及minimax已完成','q=1短记忆及q=2的1≤s≤2未知尺度风险与minimax已完成').replace('q=1未知尺度、高阶矩及极限仍缺','FirstUnknownMatched补齐q=1且包含p=1；高阶矩及极限仍缺').replace('最新阶段说明见[第二十一阶段](lean_batch21.md)','最新阶段说明见[第二十二阶段](lean_batch22.md)');p.write_text(s)
p=Path('summary.md');s=p.read_text();s=re.sub(r'第二十一阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第二十二阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s).replace('q=1未知尺度、s>2和极限分布仍未完成。','第二十二阶段进一步补齐q=1短记忆、p≥1的未知尺度pilot、最终回代及全域1≤s≤2平方Ls minimax。s>2、高阶矩与极限分布仍未完成。').replace('详见[第二十一阶段]','详见[第二十二阶段](lean_batch22.md)、[第二十一阶段]');p.write_text(s)
for name in ['README.md','lean_roadmap.md']:
 p=Path(name);p.write_text(p.read_text()+'\n[第二十二阶段](lean_batch22.md)完成q=1短记忆、p≥1的实际未知尺度pilot、尺度平均和H回代，给出1≤s≤2全域平方Ls minimax匹配。下一主线为高阶矩及所列极限分布。\n')
p=Path('lean_roadmap.md');s=p.read_text().replace('1. 原Hölder半范数及有界值域到统一导数与Taylor控制。\n2. 变化Hurst协方差/方差逼近、相关加权高阶矩及整个风险链。\n3. 未知尺度链及所列短/临界/长记忆极限；保持上面的严格完成标准。','1. 相关Gaussian阵列的高阶矩与s>2全域风险；Hermite正交性、展开或等价直接矩证明。\n2. 精细偏差及短/临界/长记忆分布极限的实际模型连接。\n3. 各原编号结果的范围核对和主入口审计；前述1≤s≤2风险完成不替代这些工作。');p.write_text(s)
p=Path('proof_notes/unknown_scale_lean_progress.md');p.write_text(p.read_text()+'\n第二十二阶段另补齐q=1短记忆、p≥1的全部二阶风险链，详见[q=1直接说明](q1_unknown_scale.md)。当前转向高阶矩与极限分布。\n')
print(len(ns),count)
