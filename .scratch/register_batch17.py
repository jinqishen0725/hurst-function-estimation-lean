from pathlib import Path
import json,re,hashlib
mods=['HolderJets','SmoothJetBounds','JetComposition','HolderComposition','CompositeLocalBias','HolderQ2MSE','HolderQ2Rate','HolderQ2LpRisk','DecisionContinuity']
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='All s>2 high moments, unknown scale, explicit minimax upper packaging and distributional limits remain.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['10','18','19'],remaining=remaining))
j['latest_batch']=17;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=17]+[dict(batch=17,new_mathematical_declarations=len(ns),declarations=ns,description='Original Holder class smooth composition with degree ceil(p)-1, including integer p; actual q=2 full-interval MSE and 1<=s<=2 squared Ls optimal upper risks for every p>=2, fixed b<1 and known nonzero scale. Uniform curve bounds imply Ls decision continuity.')]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.2','3.4']:
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_smooth_composite_remainder','hurstHolder_smooth_composite_local_bias','hurstHolder_q2_uniform_mse_rate','hurstHolder_q2_known_scale_Lp_risk']))
 e['repair_status']=e.get('repair_status','')+' 第十七阶段已将q=2推广到全部原类p≥2，证明固定b<1、已知非零常尺度、1≤s≤2的实际全域平方Ls最优风险；包括整数p及非线性高阶复合偏差。'
 e['remaining']='q=1,p≥1,b<3/4及q=2,p≥2,b<1的已知尺度1≤s≤2全域最优风险上界已完成。高阶矩及s>2、未知尺度、其他记忆分支和极限分布、显式决策核minimax上界封装仍需完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
Path('lean_batch17.md').write_text(f'''# 第十七阶段：一般p≥2的q=2全域最优风险

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27，主线未完成。

原Hölder类取m=ceil(p)−1、α=p−m∈(0,1]。首先从原假设推出m阶以内统一导数界、α-Hölder差界及C^m正则性，再用mathlib的Faà di Bruno公式与有限乘积差估计证明光滑复合函数的m阶导数α-Hölder。Taylor余项因此为O(|x−y|^p)。整数p使用m=p−1，没有额外要求原最高阶导数连续。

实际局部多项式权重消去到m阶的Taylor项，连续延拓覆盖两个端点。取phi(h)=log(4−2^(2h))，将非线性校准偏差接入实际q=2统计量的均值、方差及截断反演。

最终`hurstHolder_q2_known_scale_Lp_risk`对所有p≥2、固定0<a≤H≤b<1、已知共同σ≠0、1≤s≤2及整个(0,1)证明：

E||Hhat−H||_(Ls(0,1))² ≤ C(n log²n)^(-2p/(2p+1))。

C、N位于函数、σ及s量词之前。没有把高阶复合余项或实际模型风险放进前提。

另有两条决策空间连续性引理，为显式可测估计核准备。该封装尚未完成；所有s>2高阶矩、未知尺度及短/临界/长记忆极限仍未完成。
''')
p=Path('mainline_status.md');s=p.read_text().replace('首项积分极限与复合正则性另需证明','复合正则性已由第十七阶段补齐；首项积分极限仍缺').replace('q=1及q=2,p=2的已知尺度1≤s≤2上界已完成','q=1及q=2的已知尺度1≤s≤2上界已完成').replace('HolderLpRisk / HolderSecondLpRisk：q=1,p≥1,b<3/4；q=2,p=2,b<1。一般q=2,p≥2、s>2和显式minimax上界封装仍缺','HolderLpRisk / HolderQ2LpRisk：q=1,p≥1,b<3/4；q=2,p≥2,b<1。s>2和显式minimax上界封装仍缺').replace('最新阶段说明见[第十六阶段](lean_batch16.md)','最新阶段说明见[第十七阶段](lean_batch17.md)');p.write_text(s)
p=Path('summary.md');s=p.read_text();s=re.sub(r'第十六阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第十七阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s);s=s.replace('一般q=2,p≥2、s>2、未知尺度、显式minimax上界封装和极限分布仍未完成。','第十七阶段已覆盖全部q=2,p≥2，包括整数p的高阶复合偏差；s>2、未知尺度、显式minimax上界封装和极限分布仍未完成。').replace('详见[第十六阶段]','详见[第十七阶段](lean_batch17.md)、[第十六阶段]');p.write_text(s)
p=Path('README.md');s=p.read_text().replace('一般q=2,p≥2、s>2、未知尺度及极限仍待形式化；','[第十七阶段](lean_batch17.md)推广到全部q=2,p≥2；s>2、未知尺度及极限仍待形式化；');p.write_text(s)
p=Path('lean_roadmap.md');p.write_text(p.read_text()+'\n## 第十七阶段\n\n一般q=2,p≥2的已知尺度1≤s≤2全域最优风险已完成，包括高阶光滑复合偏差。继续显式minimax估计核、高阶矩、未知尺度及极限。见[阶段说明](lean_batch17.md)。\n')
p=Path('proof_notes/smooth_holder_composition.md');p.write_text(p.read_text()+'\n第十七阶段已将本余项接入实际局部多项式偏差、q=2均值方差与全域平方Ls风险，覆盖全部p≥2和1≤s≤2。见Hurst/HolderQ2LpRisk.lean。\n')
print(len(ns),count)
