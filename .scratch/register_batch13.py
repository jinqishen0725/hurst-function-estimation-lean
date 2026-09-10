from pathlib import Path
import json,re,hashlib
mods=['MeshPowerGeneral','MixedKernelGeneral','MeshRescaling','GridMixedCovariance','FrozenCorrelation','GridCovariancePerturb','CorrelationSums','GridCorrelationDecay','GridErrorLimit','GridCorrelationRows','GridLogVariance','GridLogMeanSharp','GridMSE','HolderGridMSE']
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['12','18','19','20'],remaining='Optimal-bandwidth risk simplification, q=2 covariance/cancellation, arbitrary higher moments, unknown-scale and distributional limits remain.'))
j['latest_batch']=13;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=13]+[dict(batch=13,new_mathematical_declarations=len(ns),declarations=ns,description='Actual q=1 full-grid covariance perturbation, short-memory correlation-square row sums, local log variance, sharpened mean, and full-interval clipped-estimator MSE from the original Holder class with a common sample threshold.')]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
updates={'3.2':['actual_grid_local_log_variance','actual_grid_log_mean_sharp','hurstHolder_q1_local_mse'], '3.4':['actual_q1_mse_from_mean_variance','hurstHolder_q1_local_mse'], '8.2':['normalizedFrozenIncrement_uniform_decay','grid_increment_covariance_perturbation','actual_grid_covariance_perturbation'], '8.3':['actual_grid_log_mean_sharp'], 'S.2.3':['kernelIncrement_mesh_parameter_bound_general','grid_mixed_covariance_bound','grid_increment_covariance_perturbation'], 'S.3.3':['actual_grid_correlation_rows_eventually','actual_grid_local_log_variance']}
for key,names in updates.items():
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+names))
 e['repair_status']=e.get('repair_status','')+' 第十三阶段已完成一维q=1、固定0<a≤H≤b<3/4的实际全网格相关平方行和、O(1/(nδ))方差、精细均值，以及原Hölder类p≥1全域截断估计MSE；常数和样本门槛统一于参数类。'
 if key in ['3.2','S.3.3']:
  e['remaining']='q=1所列短记忆范围的实际全网格行和、方差和原类MSE已形式化；最优带宽速率合并、q=2抵消与求和、其他记忆分支、高阶矩、未知尺度和极限仍缺。'
u['8.3']['remaining']='q=1实际全网格精细对数均值已证明；q=2变化Hurst修正版、原文其他rho分支及更广范围仍需形式化。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
Path('lean_batch13.md').write_text(f'''# 第十三阶段：实际q=1全网格相关行和与原类MSE

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号结果仍为2/27。主线未完成。

固定0<a≤H≤b<3/4、统一Lipschitz常数B。对于单位方差的冻结增量U_i及实际标准化增量W_i，本阶段从实际谱协方差证明

|Cov(W_i,W_j)−Cov(U_i,U_j)| ≤ C(1+log(2n))(n⁻¹+n^(2b−2)) = e_n，

覆盖全部有效中点网格，包括靠近0的位置。证明保留幂函数在半网格上的1+(2n)^(1−h−k)因子；参数每步变化≤B/n仅引入固定exp(B)因子。它没有沿用minimax下界中接近H=1/2的小扰动假设。

冻结协方差在相隔至少一个空格时满足C(d−1)^(2b−2)，近对角由Hilbert空间Cauchy–Schwarz控制。平方衰减可求和，且n e_n²→0。因此充分大的n，实际相关系数每行平方和≤同一个R；非退化性也在该证明中推出。

结合第十二阶段的Gaussian log协方差界与实际权重稳定性，得到全域Var(Ghat)≤C/(nδ)。对角扰动同时给出精细均值误差≤2e_n。

`hurstHolder_q1_local_mse`直接从原Hölder类p≥1构造连续端点延拓g。存在统一N及常数，对所有类内f、n≥N、t∈[0,1]和满足nδ≥N₀、0<δ≤1/2的带宽，实际截断估计量满足

MSE ≤ 2 Cb² δ^(2p) + Cv/(4nδ log²n) + 2D² e_n²/log²n。

其中Cb已吸收固定M；N和全部常数位于对f的量词之前。未假设Gaussian独立、相关行和或真实统计量风险率。此阶段使用单位共同尺度；一般已知尺度的显式封装尚待补充。

下一步为最优带宽化简及Ls风险连接；q=2、高阶矩、未知尺度和短/临界/长记忆极限继续保留在主线。
''')
p=Path('mainline_status.md');s=p.read_text().replace('| 变化Hurst协方差估计 | 部分完成，当前重点 | q=1实际增量范数与全网格对数均值误差已证明；q=2抵消、非对角相关衰减和求和仍缺 |','| 变化Hurst协方差估计 | q=1短记忆全网格已完成 | GridCorrelationRows：实际协方差扰动及相关平方行和；q=2、其他记忆分支仍缺 |').replace('| MSE及有限Ls上界 | 未完成 | 实际模型到估计器的风险链、统一相关高阶矩 |','| MSE及有限Ls上界 | q=1原类全域MSE已完成三项界 | HolderGridMSE：原类p≥1、b<3/4、统一样本门槛；最优带宽、Ls积分及高阶矩仍缺 |').replace('最新阶段说明见[第十二阶段](lean_batch12.md)','最新阶段说明见[第十三阶段](lean_batch13.md)').replace('实际行和仍缺 |','实际q=1短记忆行和已由第十三阶段补齐 |');p.write_text(s)
p=Path('summary.md');s=p.read_text();s=re.sub(r'第十二阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第十三阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s);s=s.replace('实际相关行和仍待证明。','第十三阶段进一步补齐q=1、固定b<3/4的实际全网格行和、方差、精细均值和原类全域MSE三项界。');s=s.replace('详见[第十二阶段]','详见[第十三阶段](lean_batch13.md)、[第十二阶段]');s=s.replace('| 真实协方差、对数矩和最终风险 |','| q=1短记忆MSE已接通；其他分支及完整风险仍缺 |').replace('| 实际相关行和与最终风险率 |','| q=1短记忆行和已完成；最终风险率、高阶矩仍缺 |');p.write_text(s)
p=Path('README.md');s=p.read_text().replace('匹配上界的概率风险链仍待形式化；','[第十三阶段](lean_batch13.md)补出实际q=1全网格行和与原类全域MSE；最优带宽、Ls风险及其他分支仍待形式化；');p.write_text(s)
p=Path('lean_roadmap.md');s=p.read_text()+'\n## 第十三阶段\n\nq=1固定值域上界b<3/4时，实际全网格相关平方行和、局部对数方差、精细均值与原类全域MSE三项界已形式化。主线继续处理最优带宽、Ls风险、q=2、高阶矩、未知尺度与极限。见[阶段说明](lean_batch13.md)。\n';p.write_text(s)
print(len(ns),count)
