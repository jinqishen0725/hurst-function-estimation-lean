"""Source-grounded index; entries record proof gaps rather than assume them away."""
from pathlib import Path
import json, re, hashlib
ROOT=Path(__file__).resolve().parents[1]
entries=[]
def add(id,kind,claim,verdict,repair,remaining,evidence,deps):
    source='supplement' if id.startswith('S.') else 'paper'
    text=(ROOT/f'source/{source}.txt').read_text()
    match=re.search(r'^'+re.escape(kind+' '+id)+r'\.\s',text,re.M|re.I)
    assert match, (kind,id)
    page=int(re.findall(r'===== PDF PAGE (\d+) =====',text[:match.start()])[-1])
    entries.append(dict(id=id,kind=kind,source=source,pdf_page=page,claim=claim,verdict=verdict,
      repair=repair,remaining=remaining,lean_evidence=evidence.split(),dependencies=deps.split(),full_lean_proof=False))

add('3.1','Theorem',
 'd=1、p>1 时，在 Hurst 函数类上的 Ls 极小极大概率风险具有 (n log²n)^(-p/(2p+1)) 下界。',
 '下界结论未被本次工作推翻；印出的证明构造必须修改；完整定理未形式化。',
 'p.855 的 κ 在右端点爆炸。改用 expNegInvGlue(1/4-x²)，再按实际 Hölder 半范数归一化。式(8.1)只要求 j≠k；测试半径取已证明分离距离的一半或更小。参数空间显式限制 0<H<1；σ固定。先修复命题8.1的谱归一化。',
 'Gaussian KL 与协方差矩阵的联系、8.1 的矩阵估计、Hölder bump packing 的全局半范数、Varshamov–Gilbert/Fano、inf/sup/liminf 和任意 γ 的处理，均未完成 Lean 证明。',
 'printedBump_unbounded correctedBump_smooth correctedBump_positive correctedBump_zero packing_radius impossible_self_separation spectralKL_bound', '8.1 S.1.1 S.1.2')
add('3.2','Theorem',
 '局部多项式对数估计量的偏差为 O(T1)，方差为 O(T2)，声称在 Ωδ 上一致。',
 '逐点率有合理证明路线；一致性表述及依赖引理存在未解决问题。',
 '明确有效差分网格及矩阵非退化；修复8.4的积分区域。短/长记忆区域分别要求 |2ψ(t)-d|≥ε>0，或使用带临界过渡因子的统一方差界；原S.3.3的常数不能直接在跨临界的t上一致。',
 '实际权重的统一稳定性、离散逼近误差、协方差求和及跨临界情况仍未完成；已有有限和恒等式不能替代这些估计。',
 'log_estimator_decomposition polynomial_reproduction smooth_residual_bound mse_decomposition bias_variance_bound','8.2 8.3 8.4 8.5 S.3.3')
add('3.3','Theorem',
 '中心化 Ghat 在短记忆、临界、长记忆下分别具有对应的归一化和极限分布。',
 '临界方差公式的推导有确定错误；短/长记忆完整极限定理仍未形式化。',
 '临界双和必须保留 ∫ω²，而不是 Vd·ω²(0)。按文中定义的真实 ch，候选修正为 2 g(H,0,h)^(-2) ∫_{sphere}ch² · ∫ω²。一维ch的显式公式须补1/2。长记忆特征函数的级数只应在收敛邻域使用，或改用正则化行列式/二阶混沌定义。',
 'Breuer–Major 三角阵列、临界CLT和Taqqu非中心极限定理均未形式化；候选修正方差的完整概率极限尚未证明。',
 'half_second_rpow leading_critical_value diagonal_weight_product diagonal_not_center_value','8.5 S.3.1 S.3.2 S.3.3 S.3.4')
add('3.4','Theorem',
 '反演后 Hhat 的偏差、MSE，以及相对 G^(-1)(E Ghat) 的极限分布。',
 '极限分布的符号需要修改；q=1估计量需补定义；MSE率尚未完整证明。',
 '2 a log n (Hhat-G^(-1)(E Ghat)) 应趋向 -Z；只有对称极限才与 Z 同分布。q=1在低于G(1-)处也需截断到1。正态情况符号不改变零均值正态分布，但不能推广至非对称二阶混沌。',
 '仅证明精确仿射反演、确定性极限转移、截断不扩张和MSE代数界；随机delta方法、尾事件估计和原文所有统一性尚缺。',
 'G_one_range G_one_no_preimage inverseOne_recovers clip_error inverse_affine_sign negative_limit inverse_mse_bound reflected_square','3.2 3.3')
add('3.5','Corollary',
 '最优带宽下 Ghat 和 Hhat 的有偏正态极限，原文两个均值都印作 R(t)。',
 '与(3.7)及S.4.34不一致；均值系数必须改。',
 '令 b0=(n^d log²n)^(-1/(2p+d))，b/b0→1。原归一化下Ghat的均值应为 -2R(t)，Hhat的均值应为 2R(t)，方差均为ξ²(t)。若b/b0→c，均值另乘c^p、方差乘c^(-d)。R允许有符号；R=0需从偏差展开得到o项，不能使用与0的等价记号。',
 '修正系数的Lean证明以A·L·B=1为显式代数前提；未证明这些统计量的CLT或完整带宽幂函数极限。',
 'corollary_bias_G corollary_bias_H corollary_printed_mean_wrong bandwidth_balance','3.2 3.3 3.4')
add('4.1','Theorem',
 '未知σ时两尺度pilot Hhat1的偏差O(b1^p+ρ)、方差O(T2)及渐近正态性。',
 '尺度消去正确；正文中心化及补充证明的归一化有笔误；完整概率结论未核验。',
 'Hhat1-E[H(t)]应明确为Hhat1-E[Hhat1(t)]，并给出正向增长的归一化a；临界情形要有log修正。修复依赖的临界方差及统一性。',
 '两尺度差分的联合协方差和联合CLT、实际pilot偏差控制未形式化。',
 'g_scale_two log_g_scale_two pilot_scale_cancels','3.2 3.3 8.2')
add('4.2','Theorem',
 '三步backfitting中log σ²估计量的MSE为O((T1′)²+T2′)，并给出条件偏差界。',
 '未发现直接推翻速率的反例；完整结论未证明。',
 '明确m≈1/b1、有效平均集合非空及γ截断；修复S.2.1的正下界前提和全局协方差估计；不能由单点pilot误差直接推出平均的方差。',
 'S.5.1的双重空间平均、S.5.2非线性截断误差及实际m选择的所有分支未完成。',
 'clip_mem clip_error error_sum_square log_lipschitz_from_below','4.1 S.5.1 S.5.2')
add('4.3','Theorem',
 '将估计的log σ²代入后，Hhat2具有所列MSE及条件偏差界。',
 '修复基础估计量后有合理推导路线；未完整证明，不能认证其达到极小极大率。',
 '应用修正的双端截断逆函数，并同时计入Ghat误差与log σ²误差；沿用3.2的一致性限制。',
 '依赖4.2、随机非线性反演及其统一控制；现有平方和界只是其中一个步骤。',
 'backfitting_error_decomposition error_sum_square inverse_mse_bound','3.4 4.2')
add('8.1','Proposition',
 'H=1/2+φ且(a_n+b_n)log n→0时，KL为O((b_n²+n a_n²)log²n)。',
 '命题待证；补充证明的谱表示少1/2，必须先修正。',
 '按Definition1.1的D定义，谱积分前应为1/(2D(H(s))D(H(t)))，而不是1/(D(H(s))D(H(t)))。保留σ一致归一化；补证从端点网格换到中点网格不改变界。S.1.1应解释为实部积分或主值。',
 'Lean已证明特征值小于1/2时的对数二次余项与有限谱和界、对称矩阵trace平方恒等式；没有证明mBm矩阵满足这些特征值及Frobenius界，也没有形式化Gaussian KL公式。',
 'spectral_normalization log_quadratic_remainder spectralKL_bound symmetric_trace_square','S.1.1 S.1.2')
add('8.2','Theorem',
 '标准化差分协方差在有界、局部远距、全域远距以及增长滞后下的四类估计。',
 '第一至三部分待完整核验；第四部分的O(b log b)余项过强，证明遗漏有限滞后误差。',
 '给出有效差分点条件及h≠0。第四部分至少保留随|u|衰减的差分余项；不能在仅有|u|→∞、|u|<2nb时把它吸入O(b log b)。先建立(ch+o(1))|u|^(-ψ)，再给额外联合速率假设。S.2.3的光滑背景项也需检查。',
 '尚未构造或分析完整mBm covariance有限差分；有限u展开反例分析见summary，尚无此项完整Lean反例。',
 'g_one g_two_unit half_second_rpow','S.2.1 S.2.2 S.2.3')
add('8.3','Lemma',
 'E[2 log|Wn|]=gtilde(H,h)+O(ρ_n)。',
 '在方差正下界与8.2成立时推导正确；印出的S.3.17错误，且[A3]独自不足。',
 '改为 E log(Wn²)=log Var(Wn)+E log χ₁²；不得使用log|E Wn|，因为均值为0。补[A1]、h≠0、t远离原点及有效网格条件。',
 '一般概率空间的尺度恒等式、log Lipschitz界已证明；标准Gaussian的log平方可积性及与实际Wn的law识别尚未形式化。',
 'expected_log_square_scale log_lipschitz_from_below g_two_uniform_lower','8.2 S.2.1')
add('8.4','Lemma',
 '局部多项式平滑H的偏差O(b^p)，并给出整数p的Taylor余项积分表达。',
 '积分区域与余项变量记法需要改；稳定性和数值积分误差待证。',
 'D_{t,b}应为{z:t+bz在实际使用的观测域}∩suppK，不能与[0,1]^d在z坐标直接相交。Rα依赖z，应写Rα(t,b,z)。边界[0,1]^d的结论需定义H的延拓及单侧设计；p<2不能声称H有连续二阶导数。',
 '已证有限设计上的多项式再现和残差界；尚未从本文矩阵逆公式推出moment条件、统一权重界及O((nb)^(-min(2,p)))。',
 'polynomial_reproduction smooth_residual_bound','')
add('8.5','Lemma',
 '向量Z的三个极限、期望界和方差界。',
 '临界协方差依赖错误的S.3.2；定理中Z与证明中Z-EZ的中心化不一致。',
 '将极限陈述中心化为Z-EZ；若保留Z，必须另证明归一化后的EZ→0，不能只凭EZ=O((nb)^(d/2)ρ)。a的维度应为局部多项式基维S，而不是d。补核条件。',
 '向量三角阵列CLT、Hermite展开和高阶累积量未形式化。',
 'centered_square_covariance negative_limit','8.2 S.3.1 S.3.2 S.3.3 S.3.4')

add('S.1.1','Lemma',
 '在n^(δ_n)→1下，两个Fourier积分相邻差的界为O(1)、O(log n)。',
 '作为普通复Lebesgue积分表述不成立；取实部或对称主值后有可行修复。',
 '原条件是n^(δ_n)→1（不是nδ_n→1）。近0的虚部约为-ikx/|x|^(2+δ)，不绝对可积。将1-e^(ikx)换为1-cos(kx)，或明确定义PV；之后缩放和均值定理得到相邻差估计。',
 'Fourier/主值积分、统一k≤n及log加权积分界均未形式化。','', '')
add('S.1.2','Lemma',
 'δ_n∈[0,1/2)、δ_n→0时，滤波Fourier积分为O(δ_n/k^(1-δ_n))。',
 '未发现结论反例；有更直接的二阶差分证明路线，尚未Lean证明。',
 '可用cos形式及(k+1)^(1+δ)-2k^(1+δ)+(k-1)^(1+δ)替代复杂围道积分；k=1单独处理，δ=0给0。围道推导中应保留Re。',
 '积分缩放恒等式与对δ一致的常数、二阶差分余项尚缺。','second_rpow_derivative','S.1.1')
add('S.2.1','Lemma',
 '声称仅在[A3]下，固定h的g(H,0,h)一致远离0。',
 '原假设不足；h=0直接反例，q=2且H→1也无统一正下界。',
 '要求h≠0及H∈[γ,1-γ]；后者来自[A1]而不是[A3]。正定性+连续性+紧性才能得到一致正下界。',
 '已证明q=1,2的明确公式与q=2单位方向显式统一下界；一般q和多维严格条件负定性的证明未形式化。',
 'g_zero_direction g_one_zero g_two_pos g_two_uniform_lower','')
add('S.2.2','Lemma',
 '冻结指数的最高奇异项系数为H、|h|²、方向投影的多项式。',
 '按冻结H的主项解释有正确递推路线；未完成一般阶数和多维证明。',
 '明确只抽取所有导数作用在距离上的主奇异项，H导数属于余项；主文一维ch公式必须补1/2。',
 '一般q方向导数递推和带H导数的全部余项分离未形式化。',
 'second_rpow_derivative half_second_rpow','')
add('S.2.3','Lemma',
 '协方差混合导数的全局幂界和靠近对角线时的主项展开。',
 '待核验；当前余项从O(1)直接略去的步骤需要额外控制。',
 '界应用绝对值并排除s=t。保留光滑背景的相对O(|t-s|^ψ)项；尤其q=1,H>1/2时ψ<1，此项不能自动吸入O(|t-s|·|log|t-s||)。',
 '完整的混合导数公式及各余项统一界未证明；本项是具体证明缺口，不是已完成的mBm反例。','half_second_rpow','S.2.2')
add('S.3.1','Lemma',
 'g(H,u,h)在|u|→∞时等于(ch+o(1))|u|^(-ψ)。',
 '冻结H情形有正确Taylor证明路线；尚未完整形式化。',
 '使用带1/2的ch；这里的o(1)不要错误加强为8.2(iv)的O(b log b)。',
 '一般q、多维以及随t变化的一致Taylor余项未证明。','g_one half_second_rpow','S.2.2')
add('S.3.2','Lemma',
 '带权相关幂双和和循环乘积在三个记忆区域的极限。',
 '临界部分的证明错误，其他部分未认证。',
 'S.3.24中ε4不能用|i-j|小推出f(i/N)f(j/N)≈f²(0)；应替换为f²(i/N)并求和得到∫f²。同步修正g的平方分母及Hermite rank2的2!因子。',
 '正确带权临界求和极限及其统计应用尚未形式化；有限对角权重恒等式和独立数值诊断仅定位问题。',
 'diagonal_weight_product diagonal_not_center_value','8.2 S.3.1')
add('S.3.3','Lemma',
 '相关幂带权双和的短、临界、长记忆三分支统一界。',
 '固定t的估计路线合理；跨临界的一致常数未被证明。',
 '幂和常数随2ψ-d→0发散。增加固定阈值间隔ε，或保留统一过渡因子1+(N^(d-2ψ)-1)/(d-2ψ)，临界时取1+log N。',
 '实际mBm权重双和及跨阈值统一界未形式化。','short_memory_q1_d1 short_memory_q1_d2 short_memory_q1_d3 short_memory_q2','8.2 S.2.1')
add('S.3.4','Lemma',
 '联合标准Gaussian变量的Hermite正交公式 E[Hk(ξ)Hl(η)]=1{k=l} r^k k!。',
 '标准恒等式在数学上正确；完整Lean证明尚未实现。',
 'τ改为η，并明确使用概率论Hermite多项式。证明：两指数生成函数的期望=e^(rst)，比较s^k t^l系数。Gaussian可积性支持求导交换。',
 'Gaussian生成函数、Hermite系数比较与任意k,l的形式化仍缺；当前仅有一般概率空间的二阶中心化恒等式。','centered_square_covariance','')
add('S.5.1','Lemma',
 '尺度估计分量I1′的偏差和不同m区间的空间平均方差界。',
 '尚未完整核验；不能以代数分解代替空间相关性证明。',
 '从8.2(iii)重新核对每个距离指数、临界幂和及m≈1/b1的代入；区分采样间隔和窗口重叠两种贡献。',
 '双重求和、所有m分支、统一常数未形式化。','log_estimator_decomposition','4.1 8.2 S.3.3 S.3.4')
add('S.5.2','Lemma',
 '非线性截断分量I2′的MSE及条件偏差界。',
 '在统一正下界与pilot矩控制成立时路线合理；未完整证明。',
 '显式使用γ截断、log g导数有界及尾事件控制；不把随机变量落出(0,1)的情况代入未定义的逆。',
 '本文log g的全阶导数界、尾事件和空间平均估计未形式化。','clip_error log_lipschitz_from_below','4.1 S.2.1')
add('S.6.1','Proposition',
 '非规则网格差分协方差的局部g逼近和远距界。',
 '第一部分按印出的未标准化协方差是错误的；Brownian特例即可否定。',
 '改为Wn(t)=σ^(-1)n^H(t) Δ^q X(t)，估计Cov(Wn(t),Wn(s))；或在原始协方差两侧恢复σ² n^(-H(t)-H(s))。',
 'Lean反例验证的是Brownian方差1/n所对应的标量渐近命题；尚未在Lean中构造Brownian过程并实例化整条命题。修正后非规则网格的一般协方差界仍缺。',
 'proposition_S6_1_raw_counterexample normalized_variance','8.2')
add('S.7.1','Lemma',
 '非恒定已知σ(t)、q≥2下，归一化差分的局部与远距协方差估计。',
 '未发现直接反例，尚未完整核验。',
 '明确[S]的光滑性和正下界、有效差分域及与8.2一致的归一化。主文误称此项为Proposition S.7.1，实际是Lemma。',
 '乘积高阶差分、所有交叉协方差余项未形式化。','difference_one difference_two','8.2 S.2.3')
add('S.7.2','Proposition',
 '已知光滑σ(t)、q≥2、d≤3下Ghat的偏差O(T1)和方差O((nb)^(-d))。',
 '有合理推导路线，未完整证明；不能据此声称d=2,3的极小极大最优。',
 '保留q≥2,d≤3和[S]；修复基础局部多项式论证。d=2,3只有上界路线，主文自己未建立对应极小极大下界。',
 '需要S.7.1全部协方差估计及实际权重控制；现在仅证明q≥2,d≤3确在短记忆区的算术条件。','short_memory_q2 smooth_residual_bound','S.7.1 8.4')

# Verified repair progress is kept separate from the original source transcription.
updates=json.loads((ROOT/'scripts/repair_updates.json').read_text())
for e in entries:
    update=updates.get(e['id'], {})
    for key,value in update.items():
        if key=='evidence_add':
            e['lean_evidence']=list(dict.fromkeys(e['lean_evidence']+value))
        else:
            e[key]=value

direct_updates=json.loads((ROOT/'scripts/direct_proof_links.json').read_text())
for e in entries:
    direct=direct_updates[e['id']]
    e['direct_proofs']=['direct_proofs/'+name for name in direct['files']]
    e['direct_proof_status']=direct['status']
    if 'complete_repaired_direct_proof' in direct:
        e['complete_repaired_direct_proof']=direct['complete_repaired_direct_proof']

assert len(entries)==27
ids={e['id'] for e in entries}
assert len(ids)==27
for e in entries: assert set(e['dependencies'])<=ids
(ROOT/'results').mkdir(exist_ok=True)
for e in entries:
    evidence='\n'.join(f'- `Hurst.{n}`' for n in e['lean_evidence']) or '无。本项保留为明确待证明结果。'
    direct_links='、'.join(f'[{Path(name).name}](../{name})' for name in e['direct_proofs']) or '暂无对应直接证明。'
    evidence_intro = '以下包含整条原命题的最终证明及其支撑引理。' if e['full_lean_proof'] else '以下仅是对应的已证明片段，不是整条原文结果的证明。'
    completion_label = '已完成' if e['full_lean_proof'] else '未完成'
    text=f"""# {e['kind']} {e['id']}

来源：{'正文 19-AOS1825.pdf' if e['source']=='paper' else '补充材料 suppdf_1.pdf'}，PDF 第 {e['pdf_page']} 页。

## 原结论

{e['claim']}

## 是否正确

{e['verdict']}

## 修改或证明路线

{e['repair']}

## 已有普通数学证明（完整Lean状态另列）

{e['direct_proof_status']}

{direct_links}

## 已有Lean修复进度

{e.get('repair_status', '保留逐项核验记录；本轮尚未闭合本项证明。')}

## Lean 对应部分

{evidence_intro}

{evidence}

## 尚未完成的Lean证明

{e['remaining']}

依赖编号：{', '.join(e['dependencies']) or '无本项目内编号依赖'}。

**完整原定理 Lean 证明：{completion_label}。**
"""
    (ROOT/f"results/{e['id']}.md").write_text(text)
(ROOT/'results/catalog.json').write_text(json.dumps(entries,ensure_ascii=False,indent=2)+'\n')
# Lean metadata with typed result IDs: verifies coverage, NOT theorem truth.
lines=['import Mathlib.Data.List.Basic', '/-! Coverage metadata only. An entry is not a proof of its paper claim. -/',
'namespace Hurst.Index','inductive ResultId where']
for e in entries: lines.append('  | r'+e['id'].replace('.','_'))
lines+=['  deriving DecidableEq, Repr','', 'def allResults : List ResultId := [']
lines += [('  .r'+e['id'].replace('.','_')+(',' if i<26 else '')) for i,e in enumerate(entries)]
lines+= [']','', 'theorem indexed_count : allResults.length = 27 := by decide',
 'theorem indexed_unique : allResults.Nodup := by decide',
 'theorem indexed_complete (r : ResultId) : r ∈ allResults := by cases r <;> decide','end Hurst.Index','']
(ROOT/'Hurst/ResultIndex.lean').write_text('\n'.join(lines))
# Mechanically compare against actual numbered statement starts, excluding references.
main=set(re.findall(r'^(?:THEOREM|LEMMA|PROPOSITION|COROLLARY) (\d+\.\d+)\.\s',(ROOT/'source/paper.txt').read_text(),re.M))
supp=set(re.findall(r'^(?:Lemma|Proposition|Theorem|Corollary) (S\.\d+\.\d+)\.\s',(ROOT/'source/supplement.txt').read_text(),re.M))
assert main|supp==ids,(main|supp)^ids
manifest={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in ['19-AOS1825.pdf','suppdf_1.pdf']}
(ROOT/'verification/source_manifest.json').write_text(json.dumps({'sha256':manifest,'main_results':len(main),'supplement_results':len(supp),'all_indexed':len(entries)},indent=2)+'\n')
print('Indexed 13 main-paper and 14 supplement results; no missing IDs.')
