from pathlib import Path
import json,re,hashlib
mods=['SpectralSecondOrder','SmoothTaylor','FeatureSecondOrder','SpectralTime','FeatureTime','SecondCancellation','HolderSecond','SecondIncrement','HolderSecondIncrement','PowerDifferences','SecondFrozen','SecondCorrelationSums','SecondGridDecay','HilbertPerturbation','SecondCorrelationRows','SecondGridActual','SecondGridLogVariance','LogNormPerturbation','LogCorrectionSmooth','SecondGridLogMean']
p=Path('Hurst.lean');s=p.read_text()
for m in mods:
 if 'import Hurst.'+m+'\n' not in s:s+='import Hurst.'+m+'\n'
p.write_text(s)
p=Path('verification/lean_formalization_progress.json');j=json.loads(p.read_text());ns=[]
for m in mods:
 f=Path('Hurst')/(m+'.lean');names=['Hurst.'+n for n in re.findall(r'^theorem\s+(\w+)',f.read_text(),re.M)];ns+=names
 j['modules']=[x for x in j['modules'] if x['path']!=str(f)]
 j['modules'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),declarations=names,written_proofs=['09','10','18','19'],remaining='q=2 nonlinear smoothing bias and final risk, all high moments, unknown scale and distributional limits remain.'))
j['latest_batch']=15;j['latest_batch_new_mathematical_declarations']=len(ns);j['mainline_complete']=False
j['batches']=[x for x in j['batches'] if x['batch']!=15]+[dict(batch=15,new_mathematical_declarations=len(ns),declarations=ns,description='Actual q=2 quadratic parameter cancellation, temporal slope scaling, original Holder p>=2 freezing error, fourth-order frozen covariance decay, actual correlation rows and local log variance and mean for any fixed b<1.')]
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
p=Path('scripts/repair_updates.json');u=json.loads(p.read_text())
for key in ['3.2','3.4']:
 e=u[key];e['evidence_add']=list(dict.fromkeys(e.get('evidence_add',[])+['hurstHolder_second_increment_remainder','normalizedFrozenSecondIncrement_uniform_decay','hurstHolder_grid_second_correlation_rows','hurstHolder_grid_second_log_variance','hurstHolder_grid_second_log_mean']))
 e['repair_status']=e.get('repair_status','')+' 第十五阶段已完成原类p≥2、固定0<a≤H≤b<1的q=2实际全网格相关平方行和、局部对数方差C/(nδ)及含log(4−2^(2H))的实际均值校准；参数二阶抵消和时间对数修正均由实际谱函数推出。'
 e['remaining']='q=1已知尺度、原类p≥1且b<3/4的点态MSE和1≤s≤2全域平方Ls上界已证明。q=2实际均值、方差已接通，但非线性平滑偏差与最终风险仍需完成；其他记忆分支、s>2高阶矩、未知尺度、随机极限，以及显式决策核的minimax上界封装仍需完成。'
p.write_text(json.dumps(u,indent=2,ensure_ascii=False)+'\n')
count=sum(len(re.findall(r'^theorem\s+',f.read_text(),re.M)) for f in Path('Hurst').glob('*.lean'))-3
Path('lean_batch15.md').write_text(f'''# 第十五阶段：实际q=2参数抵消、相关行和与对数均值方差

新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。完整原编号結果仍为2/27，主线未完成。

固定0<a≤H≤b<1、原Hölder类p≥2（包含整数p=2）。从实际谱函数直接证明参数二阶余项、斜率的时间缩放及logδ修正，结合原函数类给出的二阶差分界，得到归一化变化误差Cδ(1+|logδ|)。没有把参数二阶抵消或最高阶导数连续性作为新假设。

冻结二阶差分协方差通过四阶有限差分逐次均值估计，给出C d^(2b−4)衰减。归一化方差4−2^(2H)有统一正下界，相关平方可求和。实际误差e_n=O((1+log n)/n)带来行和附加项O(n e_n²)→0；`hurstHolder_grid_second_correlation_rows`将所有前提接回原Hölder函数类。

`gridSecond_feature_identity`核对实际观测系数[1,−2,1]与上述特征完全一致。`hurstHolder_grid_second_log_variance`据此给出真实Gaussian观测模型和实际局部权重的方差≤C/(nδ)，包括目标点0和1。

`hurstHolder_grid_second_log_mean`证明实际均值为−2H_i log n+log(4−2^(2H_i))+c，误差O((1+log n)/n)，常数与类内函数和网格位置无关。

注意：这里仍需把非线性log(4−2^(2H))的平滑偏差接到最终反演风险。不能将本批方差、均值的完成表述为q=2最终minimax上界已经完成。所有有限高阶矩、未知尺度和极限分布也仍需形式化。

直接证明说明见[参数抵消笔记](proof_notes/q2_parameter_cancellation.md)。
''')
p=Path('mainline_status.md');s=p.read_text().replace('| 变化Hurst协方差估计 | q=1短记忆全网格已完成 | GridCorrelationRows：实际协方差扰动及相关平方行和；q=2、其他记忆分支仍缺 |','| 变化Hurst协方差估计 | q=1短记忆及q=2全网格已完成 | q=2覆盖原类p≥2及固定b<1；其他记忆分支仍缺 |').replace('q=2、s>2及显式minimax上界封装仍缺','q=2实际均值方差已完成，非线性平滑偏差及最终风险、s>2和显式minimax上界封装仍缺').replace('最新阶段说明见[第十四阶段](lean_batch14.md)','最新阶段说明见[第十五阶段](lean_batch15.md)');p.write_text(s)
p=Path('summary.md');s=p.read_text();s=re.sub(r'第十四阶段新增\d+条数学定理，累计\d+条数学定理及3条编号检查。',f'第十五阶段新增{len(ns)}条数学定理，累计{count}条数学定理及3条编号检查。',s);s=s.replace('| 匹配上界仍需风险链 |','| q=1已知尺度1≤s≤2匹配上界已完成；其他范围仍缺 |');s=s.replace('q=2、s>2、未知尺度、显式minimax上界封装和极限分布仍未完成。','第十五阶段已补齐q=2、原类p≥2和固定b<1的实际相关平方行和、全域局部方差及精确非线性均值校准。q=2最终风险、s>2、未知尺度、显式minimax上界封装和极限分布仍未完成。');s=s.replace('详见[第十四阶段]','详见[第十五阶段](lean_batch15.md)、[第十四阶段]');p.write_text(s)
p=Path('README.md');s=p.read_text().replace('q=2、s>2、未知尺度及极限仍待形式化；','[第十五阶段](lean_batch15.md)完成q=2原类p≥2、固定b<1的实际相关行和及对数均值方差；最终q=2风险、s>2、未知尺度及极限仍待形式化；');p.write_text(s)
p=Path('lean_roadmap.md');p.write_text(p.read_text()+'\n## 第十五阶段\n\nq=2参数抵消、实际全网格行和、全域局部对数均值方差已接回原Hölder类p≥2及固定b<1。继续非线性平滑偏差和反演风险，随后高阶矩、未知尺度和极限。见[阶段说明](lean_batch15.md)。\n')
p=Path('proof_notes/q2_parameter_cancellation.md');s=p.read_text().replace('这些步骤在继续形式化中；本笔记不把尚未通过检查的后续步骤标为 Lean 已完成。','上述相关衰减、原类实际行和以及局部对数方差和非线性均值校准均已在第十五阶段通过Lean检查。剩余q=2任务是非线性平滑偏差和最终反演风险。');p.write_text(s)
print(len(ns),count)
