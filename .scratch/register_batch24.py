from pathlib import Path
import json,re,hashlib
mods='HermiteTruncation WeightedSchur HilbertSchur HermitePolynomialTruncation GaussianArrayL2 WeightEnergy GaussianArrayApproximation FeatureStandardGaussian FeatureHermiteApproximation GridHermiteApproximation HermiteTailEnergy L2TestApproximation FeatureHermiteTests'.split()
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
remaining='Actual finite Hermite polynomial truncation, tail energy, correlated-array Schur bound, whole-domain q1/q2 fixed-class uniform normalized L2 approximation and bounded Lipschitz test bound complete. Finite-polynomial correlated-array CLT, variance limits, high moments, s>2 risk, fine bias and critical/long-memory limits remain.'
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['11','13','19'],remaining=remaining))
j['date']='2026-09-09';j['latest_batch']=24;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=24]+[dict(batch=24,new_mathematical_declarations=len(ns),declarations=ns,description=remaining)]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.3','3.4','8.5']:
 if key not in u:continue
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['gaussian_array_log_polynomial_error','featureGaussian_log_truncation_error','hurstHolder_grid_second_log_truncation_uniform','hurstHolder_stride_first_log_truncation_uniform','featureGaussian_log_truncation_test_bound']))
 e['repair_status']=e.get('repair_status','')+' 第二十四阶段闭合实际一阶短记忆和二阶差分、全域固定Hurst类的统一Hermite截断L²误差及测试函数控制。'
 e['remaining']='统一Hermite截断已接到实际统计量；有限多项式相关阵列CLT、实际方差极限、多指标高阶矩、s>2风险、精细偏差和临界/长记忆极限仍未完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
Path('lean_batch24.md').write_text(f'''# 第二十四阶段：实际相关统计量的一致 Hermite 截断

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27，主线未完成。

`HermiteTruncation`与`HermitePolynomialTruncation`将Hilbert基截断落实为实际有限多项式P_K，证明余项L²趋零。`HermiteTailEnergy`给出其平方范数恰等于总能量减去前K项系数平方和；本项目截断索引为n<K。

`WeightedSchur`、`HilbertSchur`、`GaussianArrayL2`从实际相关平方行和证明加权余项二阶矩界，不要求独立，也不要求权重非负。`GaussianArrayApproximation`给出统一截断阶数。

`FeatureStandardGaussian`证明实际Gaussian线性观测的标准化law、联合Gaussian性及相关系数身份。`FeatureHermiteApproximation`证明中心化对数统计量与标准化观测的精确AE等式，并将截断误差界接到实际统计量。

`WeightEnergy`证明全域局部权重满足nb*sum(w_i²)≤D。`GridHermiteApproximation`完成q=2、p≥2、0<a≤H≤b<1和固定步长q=1、p≥1、0<a≤H≤b<3/4的全类统一结论：nb*E|G−EG−G_K|²≤C*‖R_K‖²，并对给定误差得到统一K阈值。位置覆盖[0,1]，带宽满足0<δ≤1/2及nδ≥N₀；样本量充分大阈值统一于H、位置、带宽。

`L2TestApproximation`和`FeatureHermiteTests`证明有界1-Lipschitz测试函数的真实期望误差由上述L²误差平方根控制，允许任意归一化常数c。

详见[证明说明](proof_notes/hermite_truncation.md)。这是文件11第4节、文件13短记忆截断步骤的形式化；有限多项式CLT和方差极限尚未证明，不能据此宣称实际对数CLT完成。高阶矩、s>2风险、精细偏差与临界/长记忆极限继续保留在主线。
''')
p=Path('summary.md');s=p.read_text();s=re.sub(r'第二十三阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第二十四阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s)
s=s.replace('s>2、多指标高阶矩界、精细偏差与极限分布仍未完成。详见','第二十四阶段已把一致Hermite截断接到q=1短记忆和q=2实际统计量、全域局部权重及整个固定Hurst类，并证明测试函数误差界。s>2、多指标高阶矩界、精细偏差、有限多项式CLT和实际极限分布仍未完成。详见[第二十四阶段](lean_batch24.md)、')
p.write_text(s)
p=Path('mainline_status.md');s=p.read_text().replace('| 短/临界/长记忆极限 |','| 实际Hermite一致截断 | 已完成q=1短记忆及q=2这一部分 | GridHermiteApproximation：全域、全固定Hurst类的nb归一化L²误差；FeatureHermiteTests：实际测试函数期望误差 |\n| 短/临界/长记忆极限 |').replace('最新阶段说明见[第二十三阶段](lean_batch23.md)','最新阶段说明见[第二十四阶段](lean_batch24.md)');p.write_text(s)
for name in ['README.md','lean_roadmap.md']:
 p=Path(name);p.write_text(p.read_text()+'\n[第二十四阶段](lean_batch24.md)完成实际q=1短记忆及q=2全域、全固定Hurst类的一致Hermite截断L²误差，以及实际有界Lipschitz测试函数误差。有限多项式CLT、实际方差极限、高阶矩、精细偏差等仍缺。\n')
p=Path('verification/lean_reuse_inventory.json');j=json.loads(p.read_text());j['date']='2026-09-09';j['hermite_truncation_integration']=dict(source='Independent proofs from local mathlib v4.31.0 and verified project Hermite basis',modules=['Hurst.'+m for m in mods],completed='Actual finite polynomial truncation; uniform correlated-array and q1/q2 fixed-class L2 bounds; actual bounded Lipschitz test error',remaining='Finite polynomial correlated-array CLT, variance limits, high moments and non-Gaussian limits');p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
print('batch24',len(ns),'total mathematical',count)
