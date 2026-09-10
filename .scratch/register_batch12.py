from pathlib import Path
import json,re,hashlib
mods=['GaussianOverlap','GaussianSymmetry','GaussianRotation','GaussianPairLaw','GaussianLogCovariance','GaussianLogRisk']
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['10','12','18','19'],remaining='Actual varying-Hurst correlation row sums, uniform higher moments, estimator risk and limit chains remain.'))
j['latest_batch']=12;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=12]+[dict(batch=12,new_mathematical_declarations=len(ns),declarations=ns,description='Direct Gaussian density overlap, rotation and symmetrization proof of even-function covariance; actual scale-invariant log covariance and correlated weighted-statistic variance bounds.')]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.2','S.3.3']:
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['gaussian_even_covariance_bound','gaussian_log_square_covariance_bound_general','featureGaussian_log_covariance_bound','gaussianLogStatistic_variance_correlation_bound','gaussianLogStatistic_variance_row_bound']))
 e['remaining']='Lean尚缺实际变化Hurst增量的相关衰减与行和、统一相关高阶矩及最终风险链。已完成真实Gaussian对数可积性、尺度不变协方差界、实际加权方差到相关平方和的控制；选定核的全域权重稳定性及原Hölder类偏差已证明。'
 e['repair_status']=e.get('repair_status','')+' 第十二阶段直接从Gaussian密度重叠与正交旋转证明偶函数的相关平方协方差界，并接到实际加权统计量；无需Hermite完备性，但尚不替代任意高阶矩。'
u['8.1']['verdict']='原谱归一化与中点网格证明须修正；修正版已接回原函数条件及limsup，Proposition 8.1已完整通过Lean。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
p=Path('proof_notes/gaussian_even_covariance.md');s=p.read_text().replace('下述普通数学推导是新的直接路线；尚未整条形式化，不能据此将风险定理标为完成。','下述直接路线已在GaussianOverlap、GaussianSymmetry、GaussianRotation、GaussianPairLaw、GaussianLogCovariance中完整形式化，GaussianLogRisk进一步给出实际加权方差界。实际mBm相关求和与风险链仍缺，不能据此将风险定理标为完成。');p.write_text(s)
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
Path('lean_batch12.md').write_text(f'''# 第十二阶段：Gaussian偶函数协方差与实际加权方差

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27。主线未完成。

直接证明见[证明说明](proof_notes/gaussian_even_covariance.md)。从实际Gaussian密度出发，计算密度重叠；正交旋转后把相关rho和−rho的密度平均。平均密度相对独立基准的平方误差是rho⁴/(1−rho⁴)。Cauchy–Schwarz与大相关系数情形的普通L²界合起来，得到全部联合标准Gaussian偶函数协方差界，包括退化相关rho=±1。

对任意非零方差的中心联合Gaussian，最终证明

|Cov(log X², log Y²)| ≤ 4 V_log Corr(X,Y)²，

其中V_log是标准Gaussian的log平方方差。标准化、几乎处处非零、可积性、加常数不改变协方差均已在Lean处理。此证明无需Hermite完备性。

真实Hilbert特征Gaussian模型中的加权统计量满足

Var(Σ w_i log D_i²) ≤ 4 V_log Σ_i Σ_j |w_i| |w_j| rho_ij²。

若max|w_i|≤W、Σ|w_i|≤L、每行Σrho_ij²≤R，则进一步≤4 V_log L W R。这里最后的行和条件是显式输入；本阶段没有把它冒充为实际mBm已证性质。

尚需变化Hurst的q=1/2相关衰减与求和、q=2抵消、统一高阶矩、估计器风险、未知尺度和三个记忆极限。
''')
p=Path('summary.md');s=p.read_text();s=s.replace('第十一阶段新增29条数学定理，累计514条数学定理及3条编号检查。',f'第十二阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。');s=s.replace('第十一阶段补出实际q=1全网格均值误差和谱函数的任意阶正则性。','第十一阶段补出实际q=1全网格均值误差和谱函数的任意阶正则性。第十二阶段直接证明Gaussian对数协方差界及实际加权统计量的相关平方和方差界，实际相关行和仍待证明。');s=s.replace('详见[第十一阶段]', '详见[第十二阶段](lean_batch12.md)、[第十一阶段]');s=s.replace('| 原Hölder类的Taylor及导数统一界 |','| 已由第十阶段补齐 |')
start=s.index('## 证明过程如何对应Lean')
s=s[:start]+'''## 当前证明过程与主要缺口

| 论文过程 | 当前Lean部分 | 仍缺 |
|---|---|---|
| 实际Gaussian观测与log矩 | GaussianFinite、Harmonizable、GaussianLog | 变化Hurst相关估计 |
| 全域局部多项式 | LocalWeights、HolderRegularity、LocalBias | 偏差首项及复合正则性 |
| 相关log统计量方差 | GaussianPairLaw、GaussianLogCovariance、GaussianLogRisk | 实际相关行和与最终风险率 |
| KL到minimax下界 | MidpointKL、HurstPacking、LossGeometry、MinimaxLower | 原3.1/8.1已完成；匹配上界未完成 |
| 未知尺度与有限Ls风险 | 已有确定性传递工具 | 高阶矩、pilot和空间平均的实际输入 |
| 短/临界/长记忆极限 | 部分代数及分析工具 | 相关三角阵列与随机极限证明 |

分项状态以[主线记录](mainline_status.md)、[逐项目录](results/catalog.json)和[实际审计](verification/audit_result.json)为准。较早阶段说明保留历史状态；20份书面证明不等于完整Lean认证。
'''
p.write_text(s)
p=Path('mainline_status.md');s=p.read_text().replace('| MSE及有限Ls上界 |', '| Gaussian对数协方差 | 已完成这一部分 | GaussianLogCovariance / GaussianLogRisk：实际尺度不变界及加权方差到相关平方和；实际行和仍缺 |\n| MSE及有限Ls上界 |').replace('最新阶段说明见[第十一阶段](lean_batch11.md)','最新阶段说明见[第十二阶段](lean_batch12.md)');p.write_text(s)
p=Path('README.md');s=p.read_text().replace('匹配上界的概率风险链仍待形式化；','[第十二阶段](lean_batch12.md)补出Gaussian偶函数协方差及实际加权方差界；匹配上界的概率风险链仍待形式化；');p.write_text(s)
p=Path('lean_roadmap.md');s=p.read_text()+'\n## 第十二阶段\n\nGaussian密度重叠、旋转与偶函数协方差已形式化；实际加权log统计量方差已归结到相关平方和。实际变化Hurst行和、高阶矩和风险链仍缺。见[阶段说明](lean_batch12.md)。\n';p.write_text(s)
print(len(ns),count)
