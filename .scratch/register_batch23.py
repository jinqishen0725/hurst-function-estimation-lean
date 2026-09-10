from pathlib import Path
import json,re,hashlib
mods='GaussianPolynomial HermiteAlgebra HermiteOrthogonality GaussianHermite MomentDetermination GaussianCompleteness HermiteSpan HermiteTotal GaussianHilbert HermiteParity HermiteConditional GaussianPolynomialLaw HermitePair GaussianRegression JointHermite HilbertDiagonal GaussianPullback GaussianLogHermite GaussianHermiteCovariance GaussianLogStein GaussianLogRank HermiteRankBound GaussianLogResidual GaussianResidualCovariance GaussianLogSeries'.split()
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='Gaussian Hermite completeness, actual joint-pair identity and L2 expansion, exact log-square rank two, rank-four residual covariance and sharp log covariance bounds complete. Multi-index moment bounds, s>2 risk, fine bias and actual short/critical/long-memory distribution limits remain.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['03','08','11','13','14','19'],remaining=remaining))
j['date']='2026-09-09';j['latest_batch']=23;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=23]+[dict(batch=23,new_mathematical_declarations=len(ns),declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.3','3.4','8.5']:
 if key not in u:continue
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['gaussianHermite_expansion','joint_standardGaussian_hermite','gaussianLog_hermite_rank_exactly_two','gaussian_log_covariance_series','gaussian_log_residual_covariance_bound']))
 e['repair_status']=e.get('repair_status','')+' 第二十三阶段从Gaussian积分证明Hermite完备性、实际联合展开、log-square的精确二阶系数及四阶余项相关界。'
 e['remaining']='已完成Hermite概率论基础，但多指标矩界、精细偏差及实际短/临界/长记忆极限仍未完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
Path('lean_batch23.md').write_text(f'''# 第二十三阶段：Hermite 完备性与实际 Gaussian 展开

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27，主线未完成。

从 Gaussian 权重下的分部积分证明全部 Hermite 正交关系。通过有全部指数矩的有限测度的矩唯一性，证明单项式的 Gaussian L² 完备性，再由 Hermite 线性包络包含全部多项式得到完整 Hilbert 基、真实 L² 级数收敛和 Parseval 等式。没有将完备性当作前提。

`HermiteConditional`从 Stein 恒等式证明 E[H_n(rho*x+s*Z)]=rho^n H_n(x)，`JointHermite`将联合矩公式传递到任意实际联合标准 Gaussian 对，包含相关±1。`GaussianHermiteCovariance`证明任意 L² 变换的实际相关展开。

`GaussianLogStein`处理零点奇性，`GaussianLogRank`证明 E[g(Z)H₂(Z)]=2、归一化系数sqrt(2)，故 Hermite 阶数恰为2。`GaussianLogResidual`证明g−H₂的前四个系数消失，平方范数为Var(log Z²)−2。`GaussianResidualCovariance`将余项协方差控制为(Var(log Z²)−2)*rho⁴。`GaussianLogSeries`给出真实协方差级数和2rho²≤Cov(g(X),g(Y))≤Var(log Z²)*rho²。

证明说明见[Hermite基础](proof_notes/hermite_foundations.md)。本阶段只闭合这些概率论输入；多指标图展开与矩求和界、s>2风险、精细偏差和短/临界/长记忆分布极限仍属主线，未移至backlog。
''')
p=Path('summary.md');s=p.read_text();s=re.sub(r'第二十二阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第二十三阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s)
s=s.replace('s>2、高阶矩与极限分布仍未完成。详见','第二十三阶段已证明Hermite完备性、真实L²展开、任意Gaussian对的联合矩、log-square恰为二阶及四阶余项界。s>2、多指标高阶矩界、精细偏差与极限分布仍未完成。详见[第二十三阶段](lean_batch23.md)、')
p.write_text(s)
p=Path('mainline_status.md');s=p.read_text().replace('| 短/临界/长记忆极限 | 未完成 | 相关三角阵列、Hermite/累积量或等价直接证明、算子/混沌极限 |','| Hermite与Gaussian展开 | 已完成这一基础部分 | GaussianHilbert、JointHermite、GaussianLogRank：完备性、实际L²收敛、联合矩公式及精确二阶系数；GaussianResidualCovariance：四阶余项界 |\n| 短/临界/长记忆极限 | 未完成 | 仍需多指标图展开/矩界、相关三角阵列CLT、实际算子/混沌极限及精细偏差 |').replace('最新阶段说明见[第二十二阶段](lean_batch22.md)','最新阶段说明见[第二十三阶段](lean_batch23.md)');p.write_text(s)
for name in ['README.md','lean_roadmap.md']:
 p=Path(name);p.write_text(p.read_text()+'\n[第二十三阶段](lean_batch23.md)闭合Hermite完备性、实际Gaussian联合展开、精确二阶log系数及四阶余项相关界。剩余主线仍为多指标高阶矩、s>2风险、精细偏差与实际分布极限。\n')
p=Path('verification/lean_reuse_inventory.json');j=json.loads(p.read_text());j['date']='2026-09-09';j['hermite_integration']=dict(source='Independent proofs from local mathlib v4.31.0',modules=['Hurst.'+m for m in mods],external_hermite_code_copied=False,completed='Gaussian integration by parts, moment determination, complete Hermite Hilbert basis, actual joint Gaussian identities and L2 series; exact log-square rank two and rank-four residual bound',remaining='Gaussian multi-index moment estimates and array distribution limits');p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
print('batch23',len(ns),'total mathematical',count)
