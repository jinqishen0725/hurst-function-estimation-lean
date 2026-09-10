from pathlib import Path
import json,re,hashlib
mods=['OptimalBandwidth','HolderGridRate','SpatialRisk','HolderIntegratedRisk','KnownScaleRisk','UnitLpRisk','HolderLpRisk']
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['12','18','19','20'],remaining='q=2, unknown-scale estimation, s>2 moments, explicit decision-kernel minimax upper packaging, and distributional limits remain.'))
j['latest_batch']=14;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=14]+[dict(batch=14,new_mathematical_declarations=len(ns),declarations=ns,description='Actual q=1 optimal-bandwidth uniform MSE and full-interval L2 risk, verified spatial measurability/Fubini, exact known-scale removal, and all 1<=s<=2 squared Ls upper risks with one class/scale-uniform constant.')]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.2','3.4']:
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['optimalLocalBandwidth_eventual_design','hurstHolder_q1_uniform_mse_rate','hurstHolder_q1_integrated_mse_rate','hurstHolder_q1_known_scale_Lp_risk']))
 e['repair_status']=e.get('repair_status','')+' 第十四阶段已将原类q=1、p≥1、b<3/4的MSE化为最优带宽率；联合可测性和Fubini已核验；任意已知非零常尺度、1≤s≤2的全域平方Ls风险≤C(n log²n)^(-2p/(2p+1))，常数与函数、尺度、s无关。'
 e['remaining']='q=1已知尺度、原类p≥1且b<3/4的点态MSE和1≤s≤2全域平方Ls上界已证明。q=2、其他记忆分支、s>2高阶矩、未知尺度、随机极限，以及显式决策核的minimax上界封装仍需完成；不将这些扩大为完整原定理。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
Path('lean_batch14.md').write_text(f'''# 第十四阶段：最优带宽、已知尺度及全域Ls上界

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27。主线未完成。

在原Hölder类p≥1、M≥0、固定0<a≤H≤b<3/4上，定义实际局部多项式q=1估计量，并对反演补齐[0,1]双端截断。令δ_n=(n log²n)^(-1/(2p+1))。`hurstHolder_q1_uniform_mse_rate`证明统一C、N存在，对全部类内函数和n≥N：

sup_(t∈[0,1]) E|Hhat(t)−H(t)|² ≤ C(n log²n)^(-2p/(2p+1))。

参数类自身给出连续端点延拓；N和常数位于函数量词之前。带宽趋零、nδ_n增长、偏差/方差精确平衡，以及协方差余项的吸收均在Lean中完成。

`SpatialRisk`证明实际估计函数的空间连续性、数据/空间联合可测性、取值[0,1]及交换积分所需可积性。`HolderIntegratedRisk`据此得到整个(0,1)上的平方L²风险。

`KnownScaleRisk`从实际Gaussian线性像证明：已知σ≠0时对全部观测除以σ，任意实值损失积分与单位尺度完全一致。因此风险常数不依赖σ。

最终`hurstHolder_q1_known_scale_Lp_risk`证明同一个C、N对全部已知σ≠0及1≤s≤2成立：

E ||Hhat−H||_(Ls(0,1))² ≤ C(n log²n)^(-2p/(2p+1))。

这里的Ls比较、损失可测性与积分有界性也已核验。输出是真实估计量的全域风险上界；尚未额外封装成GaussianFano库的决策核minimax上界表达式。

已有固定值域子类的下界可以与这一区间的上界比较，但不能因此声称全部有限s、未知尺度、q=2或整篇论文的minimax最优性都已形式化。上述项目和短/临界/长记忆极限仍留在主线。
''')
p=Path('mainline_status.md');s=p.read_text().replace('| MSE及有限Ls上界 | q=1原类全域MSE已完成三项界 | HolderGridMSE：原类p≥1、b<3/4、统一样本门槛；最优带宽、Ls积分及高阶矩仍缺 |','| MSE及有限Ls上界 | q=1已知尺度、1≤s≤2已完成实际风险上界 | HolderLpRisk：原类p≥1、b<3/4，全域最优带宽率；q=2、s>2及显式minimax上界封装仍缺 |').replace('最新阶段说明见[第十三阶段](lean_batch13.md)','最新阶段说明见[第十四阶段](lean_batch14.md)');p.write_text(s)
p=Path('summary.md');s=p.read_text();s=re.sub(r'第十三阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第十四阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s);s=s.replace('匹配上界的概率风险链、未知尺度估计链和极限分布尚未完成。','第十四阶段已证明q=1、p≥1、固定b<3/4、任意已知非零常尺度及1≤s≤2的实际全域平方Ls上界，达到与下界相同的速率。q=2、s>2、未知尺度、显式minimax上界封装和极限分布仍未完成。');s=s.replace('详见[第十三阶段]','详见[第十四阶段](lean_batch14.md)、[第十三阶段]');s=s.replace('| q=1短记忆行和已完成；最终风险率、高阶矩仍缺 |','| q=1已知尺度1≤s≤2最优风险率已完成；高阶矩等仍缺 |');p.write_text(s)
p=Path('README.md');s=p.read_text().replace('最优带宽、Ls风险及其他分支仍待形式化；','[第十四阶段](lean_batch14.md)已完成q=1已知尺度、1≤s≤2的最优带宽全域风险上界；q=2、s>2、未知尺度及极限仍待形式化；');p.write_text(s)
p=Path('lean_roadmap.md');s=p.read_text()+'\n## 第十四阶段\n\nq=1已知常尺度、p≥1、固定b<3/4的统一MSE及1≤s≤2全域平方Ls上界已达到最优带宽率。继续q=2、高阶矩、未知尺度、显式minimax上界封装与极限。见[阶段说明](lean_batch14.md)。\n';p.write_text(s)
print(len(ns),count)
