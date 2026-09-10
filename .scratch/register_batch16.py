from pathlib import Path
import json,re,hashlib
mods=['SmoothCompositeQuadratic','SecondMSE','HolderSecondMSE','SecondSpatial','HolderSecondRate','HolderSecondLpRisk','FiniteProductBounds']
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['10','18','19'],remaining='General p>=2 nonlinear bias/risk, s>2 high moments, unknown scale, explicit minimax upper packaging and distributional limits remain.'))
j['latest_batch']=16;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=16]+[dict(batch=16,new_mathematical_declarations=len(ns),declarations=ns,description='q=2,p=2 actual full-interval MSE and all 1<=s<=2 squared Ls upper risks at optimal bandwidth for any fixed b<1 and known nonzero common scale; nonlinear bias, clipping, joint measurability and Fubini verified.')]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.2','3.4']:
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_smooth_composite_linear_bias','actual_q2_mse_from_mean_variance','hurstHolder_q2_p2_uniform_mse_rate','hurstHolder_q2_p2_known_scale_Lp_risk']))
 e['repair_status']=e.get('repair_status','')+' 第十六阶段已完成q=2,p=2、任意固定b<1、已知非零常尺度、1≤s≤2的实际全域平方Ls风险≤C(n log²n)^(-4/5)，包括非线性平滑偏差、截断反演和可测积分；一般p≥2仍在推进。'
 e['remaining']='已完成q=1,p≥1,b<3/4及q=2,p=2,b<1的已知尺度1≤s≤2全域风险上界。一般q=2,p≥2、高阶矩及s>2、未知尺度、其他记忆分支和极限分布、显式决策核minimax上界封装仍需完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
Path('lean_batch16.md').write_text(f'''# 第十六阶段：q=2,p=2的最优带宽全域风险

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27，主线未完成。

固定0<a≤H≤b<1、原Hölder类p=2。`SmoothCompositeQuadratic`直接组合两个一阶Taylor展开，证明任意固定光滑变换的统一二阶余项；以实际局部线性权重消去常数、一次项，再用连续性覆盖两个端点。此处未省略log(4−2^(2H))的平滑偏差。

`SecondMSE`把H本身和非线性校准项的偏差分别纳入实际Gaussian对数统计量的反演风险。`HolderSecondMSE`将所有条件接回原函数类、实际权重、均值和方差；函数量词之前已有统一常数和样本门槛。

最优带宽δ=(n log²n)^(-1/5)给出全[0,1]的统一MSE≤C(n log²n)^(-4/5)。`SecondSpatial`验证实际估计函数的空间连续性、数据/空间联合可测性以及输出范围[0,b]。

最终`hurstHolder_q2_p2_known_scale_Lp_risk`对任意已知共同σ≠0以及1≤s≤2证明：

E||Hhat−H||_(Ls(0,1))² ≤ C(n log²n)^(-4/5)。

C和N同时独立于类内函数、σ及s。尺度消除、Lp损失比较和Fubini均调用已证明的实际模型引理。

这是p=2的完整实际上界，不能替代任意p≥2的结论。后者正在用mathlib的Faà di Bruno公式补齐高阶复合偏差；高阶矩、未知尺度、显式minimax上界封装与极限分布仍未完成。
''')
p=Path('mainline_status.md');s=p.read_text().replace('q=1已知尺度、1≤s≤2已完成实际风险上界','q=1及q=2,p=2的已知尺度1≤s≤2上界已完成').replace('HolderLpRisk：原类p≥1、b<3/4，全域最优带宽率；q=2实际均值方差已完成，非线性平滑偏差及最终风险、s>2和显式minimax上界封装仍缺','HolderLpRisk / HolderSecondLpRisk：q=1,p≥1,b<3/4；q=2,p=2,b<1。一般q=2,p≥2、s>2和显式minimax上界封装仍缺').replace('最新阶段说明见[第十五阶段](lean_batch15.md)','最新阶段说明见[第十六阶段](lean_batch16.md)');p.write_text(s)
p=Path('summary.md');s=p.read_text();s=re.sub(r'第十五阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第十六阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s);s=s.replace('q=2最终风险、s>2、未知尺度、显式minimax上界封装和极限分布仍未完成。','第十六阶段进一步完成q=2,p=2、固定b<1、已知尺度及1≤s≤2的全域最优带宽风险。一般q=2,p≥2、s>2、未知尺度、显式minimax上界封装和极限分布仍未完成。').replace('详见[第十五阶段]','详见[第十六阶段](lean_batch16.md)、[第十五阶段]');p.write_text(s)
p=Path('README.md');s=p.read_text().replace('最终q=2风险、s>2、未知尺度及极限仍待形式化；','[第十六阶段](lean_batch16.md)完成q=2,p=2的已知尺度1≤s≤2全域最优风险；一般q=2,p≥2、s>2、未知尺度及极限仍待形式化；');p.write_text(s)
p=Path('lean_roadmap.md');p.write_text(p.read_text()+'\n## 第十六阶段\n\nq=2,p=2、固定b<1的已知尺度1≤s≤2全域最优风险已完成。继续一般p≥2的高阶复合偏差，随后高阶矩、未知尺度和极限。见[阶段说明](lean_batch16.md)。\n')
print(len(ns),count)
